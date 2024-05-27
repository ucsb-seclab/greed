"""
This module helps identify which functions are doing SAFEMATH (overflow-protected)
operations using static analysis. This analysis is tuned to identify solidity 0.8+
builtin safemath operations.
"""

import logging
from typing import TYPE_CHECKING, Optional, Tuple

import networkx as nx

if TYPE_CHECKING:
    from greed.project import Project
    from greed.function import TAC_Function
    from greed.block import Block

from .common import basic_safemath_checks_pass
from .types import SafeMathFunc

log = logging.getLogger(__name__)


def identify_builtin_safemath_func(
    project: "Project", function: "TAC_Function"
) -> Optional[SafeMathFunc]:
    """
    Identify which SAFEMATH functions are called in a given function.
    """
    log.debug(f"Examining function {function.name} for builtin SAFEMATH operations")

    maybe_basic_info = basic_safemath_checks_pass(project, function)
    if maybe_basic_info is None:
        return None
    return_stmts_and_vars = maybe_basic_info
    if len(return_stmts_and_vars) != 1:
        log.debug(f"Function {function.name} does not have exactly one return block")
        return None
    (return_stmt, return_var) = return_stmts_and_vars[0]

    # Find all instructions used in this function, so we can return early if it uses any banned
    # instructions which indicate not-safemath.
    banned_instructions = {
        "CALLPRIVATE",
        "CALL",
        "CALLCODE",
        "DELEGATECALL",
        "STATICCALL",
        "CREATE",
        "CREATE2",
        "SELFDESTRUCT",
        "SSTORE",
        "SLOAD",
        "LOG0",
        "LOG1",
        "LOG2",
        "LOG3",
        "LOG4",
        "EXTCODESIZE",
        "EXTCODECOPY",
        "EXTCODEHASH",
        "BLOCKHASH",
        "COINBASE",
        "TIMESTAMP",
        "NUMBER",
        "DIFFICULTY",
        "GASLIMIT",
        "GASPRICE",
        "ORIGIN",
        "CALLER",
        "CALLVALUE",
        "CALLDATASIZE",
        "CALLDATALOAD",
        "CALLDATACOPY",
        "CODESIZE",
        "CODECOPY",
        "CODEHASH",
        "RETURNDATASIZE",
        "RETURNDATACOPY",
        "BALANCE",
        "SELFBALANCE",
        "ADDRESS",
        "SHA3",
        "RETURN",
        "STOP",
        "INVALID",
    }

    for block in function.blocks:
        for stmt in block.statements:
            if stmt.__internal_name__ in banned_instructions:
                log.debug(
                    f"Function {function.name} uses banned instruction {stmt.__internal_name__}; ignoring"
                )
                return None

    # Look at the value it returns; where did it come from?
    # For SAFEMATH we should see it originated from one of the math ops;
    # we check this later
    return_var = return_stmt.arg_vars[1]
    log.debug(f"Function {function.name} returns variable {return_var}")

    # Find the block that assigns the return value; we can do this with the usedef
    def_stmts = [
        declarer
        for declarer, _, d in function.usedef_graph.in_edges(return_var, data=True)
        if d["type"] == "def"
    ]
    if len(def_stmts) != 1:
        log.debug(
            f"Function {function.name} does not have exactly one def statement for return var {return_var}"
        )
        return None

    # Get the statement that computes the return var
    def_stmt = project.statement_at[def_stmts[0]]
    log.debug(f"Function {function.name} assigns return value in statement {def_stmt}")
    for arg in def_stmt.arg_vars:
        if arg not in function.arguments:
            log.debug(
                f"Function {function.name} return value is not immediately computed from arguments"
            )
            return None

    # Find the reverting block
    cfg: "nx.DiGraph" = function.cfg.graph
    revert_blocks = [
        block
        for block in function.cfg.graph.nodes()
        if block.statements[-1].__internal_name__ == "REVERT"
    ]

    revert_conditions = []
    for revert_block in revert_blocks:
        #
        # Find the condition variable(s) that gate the revert

        while True:
            # Continue walking backward until we find a JUMPI
            revert_block_preds = list(cfg.predecessors(revert_block))
            if len(revert_block_preds) != 1:
                log.debug(
                    f"Function {function.name} reverting block does not have exactly one predecessor"
                )
                return False

            pred_block: "Block" = revert_block_preds[0]
            pred_final_stmt = pred_block.statements[-1]
            if pred_final_stmt.__internal_name__ == "JUMPI":
                reverts_on_true = revert_block != pred_block.fallthrough_edge
                break
            elif pred_final_stmt.__internal_name__ == "JUMP":
                revert_block = pred_block
            else:
                log.debug(
                    f"Function {function.name} encountered weird statement {pred_final_stmt} while walking back to find revert condition"
                )
                return False

        # Now we should have the JUMPI statement, and we know the gating variable
        jumpi_stmt = pred_final_stmt
        gating_var = jumpi_stmt.arg_vars[1]
        log.debug(
            f"Function {function.name} found JUMPI statement controlling revert at {jumpi_stmt} (reverts on {gating_var}={reverts_on_true})"
        )

        # Construct the condition that causes the revert
        condition = _basic_symbolic_recover_condition(project, function, gating_var)

        # Negate condition if needed (TRUE should mean REVERT)
        if not reverts_on_true:
            # Flip the condition
            condition = _rec_simplify_condition(("ISZERO", condition))

        revert_conditions.append(condition)

    log.debug(
        f"Function {function.name} revert condition(s) is/are {revert_conditions}"
    )

    # Do specialized analysis for each math operator
    # (add, sub, mul, div, mod)
    match def_stmt.__internal_name__:
        case "ADD":
            if _is_safemath_add(project, function, revert_conditions):
                return SafeMathFunc.ADD
            if _is_safemath_add_signed(project, function, revert_conditions):
                return SafeMathFunc.ADD_SIGNED
        case "SUB":
            if _is_safemath_sub(project, function, revert_conditions):
                return SafeMathFunc.SUB
            if _is_safemath_sub_signed(project, function, revert_conditions):
                return SafeMathFunc.SUB_SIGNED
        case "MUL":
            if _is_safemath_mul(project, function, revert_conditions):
                return SafeMathFunc.MUL
            if _is_safemath_mul_signed(project, function, revert_conditions):
                return SafeMathFunc.MUL_SIGNED
        case "DIV":
            if _is_safemath_div(project, function, revert_conditions):
                return SafeMathFunc.DIV
        case "SDIV":
            if _is_safemath_sdiv(project, function, revert_conditions):
                return SafeMathFunc.SDIV
        case "MOD":
            if _is_safemath_mod(project, function, revert_conditions):
                return SafeMathFunc.MOD
        case "SMOD":
            if _is_safemath_smod(project, function, revert_conditions):
                return SafeMathFunc.SMOD
        case _:
            log.debug(
                f"Function {function.name} uses operator {def_stmt.__internal_name__} which doesn't look like SAFEMATH"
            )
            return None


def _is_safemath_add(project: "Project", function: "TAC_Function", conditions) -> bool:
    if len(conditions) != 1:
        log.debug(f"Function {function.name} does not have one revert condition")
        return False
    condition = conditions[0]

    # several checks are already done in identify_safemath_func
    # we just need to check the revert condition

    # This should be a simple condition
    if _get_op(condition) not in ["GT", "GE", "LT", "LE"]:
        log.debug(
            f"Function {function.name} revert condition is not a simple condition"
        )
        return False

    # One of the args should be a function argument; usually it is the first one
    # If not, flip the inequality
    if condition[1] not in function.arguments:
        # flip the argument order and the inequality
        condition = _flip_inequality(condition)

    if not _is_op(condition, "GT"):
        log.debug(f"Function {function.name} revert condition is not a GT")
        return False

    # The first argument should be a function arg
    if condition[1] not in function.arguments:
        log.debug(
            f"Function {function.name} revert condition first arg is not a function arg"
        )
        return False

    # The second argument should be an ADD of the two args
    if (
        not _is_op(condition[2], "ADD")
        or condition[2][1] not in function.arguments
        or condition[2][2] not in function.arguments
        or condition[2][1] == condition[2][2]
    ):
        log.debug(
            f"Function {function.name} revert condition second arg is not an ADD of two function args"
        )

    return True


def _is_safemath_add_signed(
    project: "Project", function: "TAC_Function", conditions
) -> bool:
    # Break down OR conditions into their components
    new_conditions = []
    for condition in conditions:
        if _is_op(condition, "OR"):
            new_conditions.append(condition[1])
            new_conditions.append(condition[2])
        else:
            new_conditions.append(condition)
    conditions = new_conditions

    if not len(conditions) == 2:
        log.debug(f"Function {function.name} does not have two revert conditions")
        return False

    # Should have two AND conditions
    # One condition should check for overflow, the other for underflow
    # Find out which one is which

    has_undeflow_check = False
    has_overflow_check = False
    for check in conditions:
        if not _is_op(check, "AND"):
            log.debug(f"Function {function.name} revert condition is not an AND")
            return False

        for and_cond in (check[1], check[2]):
            # Flip the condition if needed
            if _get_op(and_cond) in ("SGT", "SGE", "SLT", "SLE") and and_cond[1] == 0:
                and_cond = _flip_inequality(and_cond)

            if _is_op(and_cond, "SLT") and and_cond[2] == 0:
                # we found the underflow check; make sure it makes sense
                other_cond = check[2] if check[1] == and_cond else check[1]
                negative_var = and_cond[1]

                if negative_var not in function.arguments:
                    log.debug(
                        f"Function {function.name} revert condition underflow check does not have a function argument"
                    )
                    return False

                other_var = (
                    function.arguments[0]
                    if function.arguments[1] == negative_var
                    else function.arguments[1]
                )

                # If the ADD of the two args is greater than the other arg, then it's an underflow
                if _is_op(other_cond, "SLE"):
                    other_cond == _flip_inequality(other_cond)
                if (
                    not _is_op(other_cond, "SGE")
                    or other_cond[2] != other_var
                    or not _is_op(other_cond[1], "ADD")
                    or not (
                        (
                            other_cond[1][1] == function.arguments[0]
                            and other_cond[1][2] == function.arguments[1]
                        )
                        or (
                            other_cond[1][1] == function.arguments[1]
                            and other_cond[1][2] == function.arguments[0]
                        )
                    )
                ):
                    log.debug(
                        f"Function {function.name} revert condition underflow check is malformed"
                    )
                    return False

                has_undeflow_check = True
                break

            elif _is_op(and_cond, "SGE") and and_cond[2] == 0:
                # we found the overflow check; make sure it makes sense
                other_cond = check[2] if check[1] == and_cond else check[1]
                positive_var = and_cond[1]

                if positive_var not in function.arguments:
                    log.debug(
                        f"Function {function.name} revert condition overflow check does not have a function argument"
                    )
                    return False

                other_var = (
                    function.arguments[0]
                    if function.arguments[1] == positive_var
                    else function.arguments[1]
                )

                # If the ADD of the two args is less than the other arg, then it's an overflow
                if _is_op(other_cond, "SGT"):
                    other_cond == _flip_inequality(other_cond)
                if (
                    not _is_op(other_cond, "SLT")
                    or other_cond[2] != other_var
                    or not _is_op(other_cond[1], "ADD")
                    or not (
                        (
                            other_cond[1][1] == function.arguments[0]
                            and other_cond[1][2] == function.arguments[1]
                        )
                        or (
                            other_cond[1][1] == function.arguments[1]
                            and other_cond[1][2] == function.arguments[0]
                        )
                    )
                ):
                    log.debug(
                        f"Function {function.name} revert condition overflow check is malformed"
                    )
                    return False

                has_overflow_check = True
                break

        else:
            # We couldnt'f figure out what this condition is doing
            log.debug(
                f"Function {function.name} revert condition has a weird condition {and_cond}"
            )
            return False

    return has_overflow_check and has_undeflow_check


def _is_safemath_sub(project: "Project", function: "TAC_Function", conditions) -> bool:
    if len(conditions) != 1:
        log.debug(f"Function {function.name} does not have one revert condition")
        return False
    condition = conditions[0]

    # This should be a simple condition
    if _get_op(condition) not in ["GT", "GE", "LT", "LE"]:
        log.debug(
            f"Function {function.name} revert condition is not a simple condition"
        )
        return False

    # One of the args should be a function argument; usually it is the first one
    # If not, flip the inequality
    if condition[1] not in function.arguments:
        # flip the argument order and the inequality
        condition = _flip_inequality(condition)

    if not _is_op(condition, "LT"):
        log.debug(f"Function {function.name} revert condition is not a LT")
        return False

    # The first argument should be a function arg
    if condition[1] not in function.arguments:
        log.debug(
            f"Function {function.name} revert condition first arg is not a function arg"
        )
        return False

    # The second argument should be an ADD of the two args
    if (
        not _is_op(condition[2], "SUB")
        or condition[2][1] not in function.arguments
        or condition[2][2] not in function.arguments
        or condition[2][1] == condition[2][2]
    ):
        log.debug(
            f"Function {function.name} revert condition second arg is not a SUB of two function args"
        )

    return True


def _is_safemath_sub_signed(
    project: "Project", function: "TAC_Function", conditions
) -> bool:
    # NOTE: this is the same as _is_safemath_add_signed, but with the inequalities flipped

    # Break down OR conditions into their components
    new_conditions = []
    for condition in conditions:
        if _is_op(condition, "OR"):
            new_conditions.append(condition[1])
            new_conditions.append(condition[2])
        else:
            new_conditions.append(condition)
    conditions = new_conditions

    if not len(conditions) == 2:
        log.debug(f"Function {function.name} does not have two revert conditions")
        return False

    # Should have two AND conditions
    # One condition should check for overflow, the other for underflow
    # Find out which one is which

    has_undeflow_check = False
    has_overflow_check = False
    for check in conditions:
        if not _is_op(check, "AND"):
            log.debug(f"Function {function.name} revert condition is not an AND")
            return False

        for and_cond in (check[1], check[2]):
            # Flip the condition if needed
            if _get_op(and_cond) in ("SGT", "SGE", "SLT", "SLE") and and_cond[1] == 0:
                and_cond = _flip_inequality(and_cond)

            if _is_op(and_cond, "SLT") and and_cond[2] == 0:
                # we found the underflow check; make sure it makes sense
                other_cond = check[2] if check[1] == and_cond else check[1]
                negative_var = and_cond[1]

                if negative_var not in function.arguments:
                    log.debug(
                        f"Function {function.name} revert condition underflow check does not have a function argument"
                    )
                    return False

                other_var = (
                    function.arguments[0]
                    if function.arguments[1] == negative_var
                    else function.arguments[1]
                )

                # If the ADD of the two args is greater than the other arg, then it's an underflow
                if _is_op(other_cond, "SGT"):
                    other_cond == _flip_inequality(other_cond)
                if (
                    not _is_op(other_cond, "SLT")
                    or other_cond[2] != other_var
                    or not _is_op(other_cond[1], "SUB")
                    or other_cond[1][1] != function.arguments[0]
                    or other_cond[1][2] != function.arguments[1]
                ):
                    log.debug(
                        f"Function {function.name} revert condition underflow check is malformed"
                    )
                    return False

                has_undeflow_check = True
                break

            elif _is_op(and_cond, "SGE") and and_cond[2] == 0:
                # we found the overflow check; make sure it makes sense
                other_cond = check[2] if check[1] == and_cond else check[1]
                positive_var = and_cond[1]

                if positive_var not in function.arguments:
                    log.debug(
                        f"Function {function.name} revert condition overflow check does not have a function argument"
                    )
                    return False

                other_var = (
                    function.arguments[0]
                    if function.arguments[1] == positive_var
                    else function.arguments[1]
                )

                # If the ADD of the two args is less than the other arg, then it's an overflow
                if _is_op(other_cond, "SLT"):
                    other_cond == _flip_inequality(other_cond)
                if (
                    not _is_op(other_cond, "SGT")
                    or other_cond[2] != other_var
                    or not _is_op(other_cond[1], "SUB")
                    or other_cond[1][1] != function.arguments[0]
                    or other_cond[1][2] != function.arguments[1]
                ):
                    log.debug(
                        f"Function {function.name} revert condition overflow check is malformed"
                    )
                    return False

                has_overflow_check = True
                break

        else:
            # We couldnt'f figure out what this condition is doing
            log.debug(
                f"Function {function.name} revert condition has a weird condition {and_cond}"
            )
            return False

    return has_overflow_check and has_undeflow_check


def _is_safemath_mul(project: "Project", function: "TAC_Function", conditions) -> bool:
    if len(conditions) != 1:
        log.debug(f"Function {function.name} does not have one revert condition")
        return False
    condition = conditions[0]

    # This one is a bit more complex than the previous two.

    # SAFEMUL's condition should have two branches:
    # First, it picks an argument and checks whether it is zero, call it 'a'
    #   (if the argument is zero, it cannot overflow, and thus the function should not revert and the condition should be false)
    # Second, it checks whether the result of (a * b) / a is equal to b

    # In the simplification process we've ensured that this looks roughly like:
    # (AND a (ISZERO (EQ (DIV (MUL a b) a) b)))

    if not _is_op(condition, "AND"):
        log.debug(f"Function {function.name} revert condition is not an AND")
        return False

    for nonzero_arg, check in (
        (condition[1], condition[2]),
        (condition[2], condition[1]),
    ):
        if nonzero_arg in function.arguments:
            break
    else:
        log.debug(
            f"Function {function.name} revert condition does not have a function argument in the first AND branch"
        )
        return False

    if not _is_op(check, "ISZERO"):
        log.debug(
            f"Function {function.name} revert condition second branch is not an ISZERO"
        )
        return False

    a = nonzero_arg
    b = function.arguments[0] if function.arguments[1] == a else function.arguments[1]

    log.debug(
        f"Function {function.name} found a={a} and b={b} while checking SAFEMUL condition"
    )

    if not _is_op(check[1], "EQ"):
        log.debug(
            f"Function {function.name} revert condition second branch does not contain an EQ"
        )
        return False

    for eq_lhs, eq_rhs in ((check[1][1], check[1][2]), (check[1][2], check[1][1])):
        if eq_lhs == b:
            break
    else:
        log.debug(
            f"Function {function.name} revert condition EQ was malformed; could not find 'b'"
        )
        return False

    # We are now checking whether (a * b) / a == b
    # Note that since multiplication is commutative, we don't care about the order of a and b
    if (
        not _is_op(eq_rhs, "DIV")
        or not _is_op(eq_rhs[1], "MUL")
        or not (
            (eq_rhs[1][1] == a and eq_rhs[1][2] == b)
            or (eq_rhs[1][1] == b and eq_rhs[1][2] == a)
        )
        or eq_rhs[2] != a
    ):
        log.debug(
            f"Function {function.name} revert condition EQ was malformed; could not find 'a * b / a == b'"
        )
        return False

    return True


def _is_safemath_mul_signed(
    project: "Project", function: "TAC_Function", conditions
) -> bool:
    # Break down OR conditions into their components
    new_conditions = []
    for condition in conditions:
        if _is_op(condition, "OR"):
            new_conditions.append(condition[1])
            new_conditions.append(condition[2])
        else:
            new_conditions.append(condition)
    conditions = new_conditions

    if not len(conditions) == 2:
        log.debug(f"Function {function.name} does not have two revert conditions")
        return False

    # Should have two AND conditions
    # One ensures that we do not multiply 0x8000000000000000000000000000000000000000000000000000000000000000
    #   by a negative number
    # The other ensures that if the argument is nonzero then we do not overflow,
    #   in a way similar to the non-signed version

    has_mul_by_neg_check = False
    has_overflow_check = False
    for check in conditions:
        if not _is_op(check, "AND"):
            log.debug(f"Function {function.name} revert condition is not an AND")
            return False

        for and_cond in (check[1], check[2]):
            # is this condition checking for multiplication by 0x80..0 by a negative?
            if (
                _is_op(and_cond, "EQ")
                and 0x8000000000000000000000000000000000000000000000000000000000000000
                in and_cond[1:]
                and (
                    and_cond[1] in function.arguments
                    or and_cond[2] in function.arguments
                )
            ):

                # This is the multiplication by 0x800...0 check
                other_cond = check[2] if check[1] == and_cond else check[1]
                named_var = (
                    function.arguments[0]
                    if function.arguments[0] in and_cond
                    else function.arguments[1]
                )
                other_var = (
                    function.arguments[0]
                    if function.arguments[1] == named_var
                    else function.arguments[1]
                )

                # NOTE FOR FUTURE SELF: below is an example of the condition we are checking for, this should check for the first
                # AND. We just need to check for the SLT check.
                if _is_op(other_cond, "SGT"):
                    other_cond = _flip_inequality(other_cond)
                if (
                    not _is_op(other_cond, "SLT")
                    or other_cond[2] != 0
                    or other_cond[1] != other_var
                ):
                    log.debug(
                        f"Function {function.name} revert condition multiplication by 0x800...0 check is malformed"
                    )
                    return False

                has_mul_by_neg_check = True

            # Is this condition checking for overflow?
            # This requires that one variable is nonzero. Check to see if we find the nonzero check
            if and_cond in function.arguments:
                b = and_cond
                a = (
                    function.arguments[0]
                    if function.arguments[1] == b
                    else function.arguments[1]
                )

                other_cond = check[2] if check[1] == and_cond else check[1]
                # The remainder is a check: NOT (a * b / b == a)
                # (because we know b is nonzero)

                if not _is_op(other_cond, "ISZERO") or not _is_op(other_cond[1], "EQ"):
                    log.debug(
                        f"Function {function.name} revert condition overflow check is not an ISZERO-EQ"
                    )
                    return False

                eq_lhs = other_cond[1][1]
                eq_rhs = other_cond[1][2]
                # one of the two should be a, the other should be a * b / b
                if eq_lhs == a:
                    mul_and_div = eq_rhs
                else:
                    if eq_lhs != a:
                        log.debug(
                            f"Function {function.name} revert condition overflow check is malformed"
                        )
                        return False
                    mul_and_div = eq_lhs

                if (
                    not _is_op(mul_and_div, "SDIV")
                    or not _is_op(mul_and_div[1], "MUL")
                    or not (
                        (mul_and_div[1][1] == a and mul_and_div[1][2] == b)
                        or (mul_and_div[1][1] == b and mul_and_div[1][2] == a)
                    )
                    or mul_and_div[2] != b
                ):
                    log.debug(
                        f"Function {function.name} revert condition overflow check multiplication-division is malformed"
                    )

                has_overflow_check = True

    return has_mul_by_neg_check and has_overflow_check


def _is_safemath_div(project: "Project", function: "TAC_Function", conditions) -> bool:
    if len(conditions) != 1:
        log.debug(f"Function {function.name} does not have one revert condition")
        return False
    condition = conditions[0]

    # Very easy; the condition should just be a check for division by zero
    if not _is_op(condition, "ISZERO") or condition[1] != function.arguments[1]:
        log.debug(
            f"Function {function.name} revert condition is not an ISZERO of the second function argument"
        )
        return False

    return True


def _is_safemath_sdiv(project: "Project", function: "TAC_Function", conditions) -> bool:
    # Break down OR conditions into their components
    new_conditions = []
    for condition in conditions:
        if _is_op(condition, "OR"):
            new_conditions.append(condition[1])
            new_conditions.append(condition[2])
        else:
            new_conditions.append(condition)
    conditions = new_conditions

    if not len(conditions) == 2:
        log.debug(f"Function {function.name} does not have two revert conditions")
        return False

    for cond1, cond2 in (
        (conditions[0], conditions[1]),
        (conditions[1], conditions[0]),
    ):
        if _is_op(cond1, "ISZERO") and cond1[1] == function.arguments[1]:
            overflow_check_cond = cond2
            break
    else:
        log.debug(
            f"Function {function.name} could not find divide by zero check condition"
        )
        return False

    # The overflow check condition should be a simple direct equality for the two arguments
    if not _is_op(overflow_check_cond, "AND"):
        log.debug(f"Function {function.name} overflow check is not an AND")
        return False

    num_var = function.arguments[0]
    denom_var = function.arguments[1]
    for and_lhs, and_rhs in (
        (overflow_check_cond[1], overflow_check_cond[2]),
        (overflow_check_cond[2], overflow_check_cond[1]),
    ):
        if (
            _is_op(and_lhs, "EQ")
            and (
                (
                    and_lhs[1] == num_var
                    and and_lhs[2]
                    == 0x8000000000000000000000000000000000000000000000000000000000000000
                )
                or (
                    and_lhs[2] == num_var
                    and and_lhs[1]
                    == 0x8000000000000000000000000000000000000000000000000000000000000000
                )
            )
            and _is_op(and_rhs, "EQ")
            and (
                (
                    and_rhs[1] == denom_var
                    and and_rhs[2]
                    == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
                )
                or (
                    and_rhs[2] == denom_var
                    and and_rhs[1]
                    == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
                )
            )
        ):
            # Found the overflow check
            break
    else:
        log.debug(
            f"Function {function.name} could not match the overflow check condition"
        )
        return False

    return True


def _is_safemath_mod(project: "Project", function: "TAC_Function", conditions) -> bool:
    if len(conditions) != 1:
        log.debug(f"Function {function.name} does not have one revert condition")
        return False
    condition = conditions[0]

    # Just checks for division by zero
    if not _is_op(condition, "ISZERO") or condition[1] != function.arguments[1]:
        log.debug(
            f"Function {function.name} revert condition is not an ISZERO of the second function argument"
        )
        return False

    return True


def _is_safemath_smod(project: "Project", function: "TAC_Function", conditions) -> bool:
    if len(conditions) != 1:
        log.debug(f"Function {function.name} does not have one revert condition")
        return False
    condition = conditions[0]

    # Just checks for division by zero
    if not _is_op(condition, "ISZERO") or condition[1] != function.arguments[1]:
        log.debug(
            f"Function {function.name} revert condition is not an ISZERO of the second function argument"
        )
        return False

    return True


def _basic_symbolic_recover_condition(
    project: "Project", function: "TAC_Function", var: str
) -> Tuple:
    """
    Construct the symbolic computation that occurs to produce 'var'.

    Note that this is extremely naive (we don't care about many operations other than those used in SAFEMATH)

    Returns a tuple, e.g., of ('ISZERO', ('GT', ('ADD', 'a', 'b'), 'a'))
    """
    unsimplified = _rec_basic_symbolic_recover_condition(project, function, var)
    simplified = _rec_simplify_condition(unsimplified)
    return simplified


def _rec_basic_symbolic_recover_condition(
    project: "Project", function: "TAC_Function", var: str
) -> Tuple:
    # If this is a function argument, return the argument
    if var in function.arguments:
        return var

    # Where is var defined?
    def_stmts = [
        declarer
        for declarer, _, d in function.usedef_graph.in_edges(var, data=True)
        if d["type"] == "def"
    ]
    if len(def_stmts) != 1:
        log.debug(
            f"In function {function.name} variable {var} is not defined exactly once; confused"
        )
        return None

    def_stmt = project.statement_at[def_stmts[0]]

    rewritten_args = []
    for arg in def_stmt.arg_vars:
        if val := def_stmt.arg_vals.get(arg):
            rewritten_args.append(val.value)
        else:
            rewritten_args.append(
                _rec_basic_symbolic_recover_condition(project, function, arg)
            )

    return (def_stmt.__internal_name__, *rewritten_args)


def _rec_simplify_condition(cond: Tuple) -> Tuple:
    """
    Extremely dumb simplification procedure for the condition.

    Basically, just handles negations and double-negations.
    """
    if isinstance(cond, (int, str)):
        return cond

    # Case 1: if this is a double-negation, remove it (e.g., NOT(NOT(x)) -> x)
    if _is_op(cond, "ISZERO") and _is_op(cond[1], "ISZERO"):
        return _rec_simplify_condition(cond[1][1])

    # Case 2: if this is a negation followed by a comparison, remove the negation and flip the comparison
    if _is_op(cond, "ISZERO"):
        if _is_op(cond[1], "GT"):
            return ("LE", *(_rec_simplify_condition(arg) for arg in cond[1][1:]))
        if _is_op(cond[1], "GE"):
            return ("LT", *(_rec_simplify_condition(arg) for arg in cond[1][1:]))
        if _is_op(cond[1], "LT"):
            return ("GE", *(_rec_simplify_condition(arg) for arg in cond[1][1:]))
        if _is_op(cond[1], "LE"):
            return ("GT", *(_rec_simplify_condition(arg) for arg in cond[1][1:]))
        if _is_op(cond[1], "SGT"):
            return ("SLE", *(_rec_simplify_condition(arg) for arg in cond[1][1:]))
        if _is_op(cond[1], "SGE"):
            return ("SLT", *(_rec_simplify_condition(arg) for arg in cond[1][1:]))
        if _is_op(cond[1], "SLT"):
            return ("SGE", *(_rec_simplify_condition(arg) for arg in cond[1][1:]))
        if _is_op(cond[1], "SLE"):
            return ("SGT", *(_rec_simplify_condition(arg) for arg in cond[1][1:]))

    # Case 3: distribute ISZERO over OR using De Morgan's laws
    if _is_op(cond, "ISZERO") and _is_op(cond[1], "OR"):
        return (
            "AND",
            *(_rec_simplify_condition(("ISZERO", arg)) for arg in cond[1][1:]),
        )
    if _is_op(cond, "ISZERO") and _is_op(cond[1], "AND"):
        return (
            "OR",
            *(_rec_simplify_condition(("ISZERO", arg)) for arg in cond[1][1:]),
        )

    # Do not recurse if we cannot simplify; since we don't really want to recurse into the math ops.
    # This is generally safe, since SAFEMATH follows particular patterns, and we're looking for those
    # patterns: if anything weird comes up, it's probably not SAFEMATH anyway.
    return cond


def _flip_inequality(inequality: tuple) -> tuple:
    """
    Flip the argument order and the inequality in an inequality.
    """
    match _get_op(inequality):
        case "GT":
            return ("LT", *reversed(inequality[1:]))
        case "GE":
            return ("LE", *reversed(inequality[1:]))
        case "LT":
            return ("GT", *reversed(inequality[1:]))
        case "LE":
            return ("GE", *reversed(inequality[1:]))
        case "SGT":
            return ("SLT", *reversed(inequality[1:]))
        case "SGE":
            return ("SLE", *reversed(inequality[1:]))
        case "SLT":
            return ("SGT", *reversed(inequality[1:]))
        case "SLE":
            return ("SGE", *reversed(inequality[1:]))
        case _:
            raise ValueError(f"Cannot flip inequality {inequality}")


def _is_op(tup: Tuple, op: str) -> bool:
    return isinstance(tup, tuple) and tup[0] == op


def _get_op(tup: Tuple) -> Optional[str]:
    if not isinstance(tup, tuple):
        return None
    return tup[0]
