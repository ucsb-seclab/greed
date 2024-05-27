import logging
from typing import TYPE_CHECKING, List

import greed.options as options
from greed.solver.shortcuts import *
from greed.TAC import TAC_Returnprivate, TAC_Statement

if TYPE_CHECKING:
    from greed import Project
    from greed.analyses.safemath_funcs.types import SafeMathFunc, SafeMathFuncReport
    from greed.state import SymbolicEVMState

log = logging.getLogger(__name__)

MAX_UNSIGNED_WORD = 2**256 - 1
MIN_UNSIGNED_WORD = 0
MAX_SIGNED_WORD = 2**255 - 1
MIN_SIGNED_WORD = -(2**255)


def patch_function(project: "Project", report: "SafeMathFuncReport"):
    """
    Patches the function to use safe math symprocedures
    """
    old_block_id = report.func.id
    old_block = project.block_at[old_block_id]

    return_var_id = _gen_var_id()

    if report.func_kind == SafeMathFunc.ADD:
        op = construct_safe_add(report, old_block_id, return_var_id)

    new_return_stmt = TAC_Returnprivate(
        old_block_id, _gen_statement_id(), [return_var_id]
    )

    new_stmts: List[TAC_Statement] = [op, new_return_stmt]
    old_block.statements = new_stmts
    old_block._statement_at = {stmt.id: stmt for stmt in new_stmts}

    for new_stmt in new_stmts:
        project.statement_at[new_stmt.id] = new_stmt

    log.debug(f"Patched function {report.func.name} to use safemath symprocedure")


def construct_safe_add(
    report: "SafeMathFuncReport", block_id: str, return_into_var: str
) -> "SymProcedureSafeAdd":
    uses = (report.func.arguments[0], report.func.arguments[1])
    defs = (return_into_var,)
    return SymProcedureSafeAdd(block_id, _gen_statement_id(), uses, defs)


class SymProcedureSafeAdd(TAC_Statement):
    __internal_name__ = "SYMPROCEDURE_SAFEADD"
    __aliases__ = {}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: "SymbolicEVMState"):
        a = self.arg1_val
        b = self.arg2_val

        if options.LAZY_SOLVES:
            a_concrete = False
            b_concrete = False
        else:
            a_concrete = state.solver.is_concrete(a)
            b_concrete = state.solver.is_concrete(b)

        if a_concrete:
            a_val = state.solver.eval(a)
        if b_concrete:
            b_val = state.solver.eval(b)

        if a_concrete and b_concrete:
            # Concrete computation, we can do it directly
            result_i = a_val + b_val
            # if result fits within 1 word, use it as return value
            if result_i < 2**256:
                result = BVV(a_val + b_val, 256)
            else:
                # no non-revert states
                return []
        # If one of the arguments is concrete, we can do some simplification
        elif a_concrete or b_concrete:
            conc_val, sym = (a_val, b) if a_concrete else (b_val, a)

            # if the concrete value is zero, the result is the other
            if conc_val == 0:
                result = sym
            else:
                # we can simply constrain the sym value to be such that (conc_val + sym) < 2**256
                assert conc_val > 0, f"Expected positive concrete value, got {conc_val}"
                limit = 2**256 - conc_val
                new_constraint = BV_ULT(sym, BVV(limit, 256))
                setattr(new_constraint, "safemath", True)
                state.solver.add_path_constraint(new_constraint)
                result = BV_Add(a, b)
        else:
            # Fully symbolic, we need to do some more work

            # extend by 1 bit (the carry)
            a_extended = BV_Zero_Extend(a, 1)
            b_extended = BV_Zero_Extend(b, 1)

            # do the addition
            result_extended = BV_Add(a_extended, b_extended)

            # assert it fits without using the carry bit
            limit = BVV((1 << 256), 257)
            new_constraint = BV_ULT(result_extended, limit)
            setattr(new_constraint, "safemath", True)
            state.solver.add_path_constraint(new_constraint)

            # do the addition
            result = BV_Add(a, b)

        # store the result
        state.registers[self.res1_var] = result

        return [state]


class SymProcedureSafeAddSigned(TAC_Statement):
    __internal_name__ = "SYMPROCEDURE_SAFEADD_SIGNED"
    __aliases__ = {}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: "SymbolicEVMState"):
        a = self.arg1_val
        b = self.arg2_val

        if options.LAZY_SOLVES:
            a_concrete = False
            b_concrete = False
        else:
            a_concrete = state.solver.is_concrete(a)
            b_concrete = state.solver.is_concrete(b)

        if a_concrete:
            a_val_unsigned = state.solver.eval(a)
            a_val = _unsigned_word_to_signed(a_val_unsigned)
        if b_concrete:
            b_val_unsigned = state.solver.eval(b)
            b_val = _unsigned_word_to_signed(b_val_unsigned)

        if a_concrete and b_concrete:
            # Concrete computation, we can do it directly
            result_i = a_val + b_val
            # if result fits within 1 word, use it as return value
            if MIN_SIGNED_WORD <= result_i <= MAX_SIGNED_WORD:
                result = BVV(_signed_word_to_unsigned(result_i), 256)
            else:
                # no non-revert states
                return []
        # If one of the arguments is concrete, we can do some simplification
        elif a_concrete or b_concrete:
            conc_val, sym = (a_val, b) if a_concrete else (b_val, a)

            # if the concrete value is zero, the result is the other
            if conc_val == 0:
                result = sym
            else:
                # we can simply constrain the sym value to be such that MIN_SIGNED_WORD <= (conc_val + sym) <= MAX_SIGNED_WORD
                # => (MIN_SIGNED_WORD - conc_val) <= sym <= (MAX_SIGNED_WORD - conc_val)
                # BUT note that the lower might underflow, so we need to handle that
                val_lo = _signed_word_to_unsigned(
                    max(MIN_SIGNED_WORD, MIN_SIGNED_WORD - conc_val)
                )
                val_hi = _signed_word_to_unsigned(
                    min(MAX_SIGNED_WORD, MAX_SIGNED_WORD - conc_val)
                )

                new_constraint = And(
                    BV_SLE(BVV(val_lo, 256), sym), BV_SLE(sym, BVV(val_hi, 256))
                )
                setattr(new_constraint, "safemath", True)
                state.solver.add_path_constraint(new_constraint)
                result = BV_Add(a, b)
        else:
            # Fully symbolic, we need to do some more work

            # extend by 1 bit (the carry)
            a_extended = BV_Sign_Extend(a, 1)
            b_extended = BV_Sign_Extend(b, 1)

            # do the addition
            result_extended = BV_Add(a_extended, b_extended)

            # assert it fits within signed limits
            new_constraint = And(
                BV_SLE(
                    BVV(_signed_word_to_unsigned(MIN_SIGNED_WORD, 257), 257),
                    result_extended,
                ),
                BV_SLE(
                    result_extended,
                    BVV(_signed_word_to_unsigned(MAX_SIGNED_WORD, 257), 257),
                ),
            )
            setattr(new_constraint, "safemath", True)
            state.solver.add_path_constraint(new_constraint)

            # do the addition
            result = BV_Add(a, b)

        # store the result
        state.registers[self.res1_var] = result

        return [state]


class SymProcedureSafeSub(TAC_Statement):
    __internal_name__ = "SYMPROCEDURE_SAFESUB"
    __aliases__ = {}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: "SymbolicEVMState"):
        a = self.arg1_val
        b = self.arg2_val

        if options.LAZY_SOLVES:
            a_concrete = False
            b_concrete = False
        else:
            a_concrete = state.solver.is_concrete(a)
            b_concrete = state.solver.is_concrete(b)

        if a_concrete:
            a_val = state.solver.eval(a)
        if b_concrete:
            b_val = state.solver.eval(b)

        if a_concrete and b_concrete:
            result_i = a_val - b_val
            # if result does not underflow (i.e., is positive), use it as return value
            if result_i >= 0:
                result = BVV(a_val - b_val, 256)
            else:
                # no non-revert states
                return []
        # NOTE: if 'just A' or 'just B' are concrete, we cannot do any simplification anyway, so just
        # use the fully symbolic path below
        else:
            # do the subtraction
            result = BV_Sub(a, b)

            # assert no underflow
            new_constraint = BV_UGE(a, b)
            setattr(new_constraint, "safemath", True)
            state.solver.add_path_constraint(new_constraint)

        # store the result
        state.registers[self.res1_var] = result

        return [state]


class SymProcedureSafeSubSigned(TAC_Statement):
    __internal_name__ = "SYMPROCEDURE_SAFESUB_SIGNED"
    __aliases__ = {}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: "SymbolicEVMState"):
        a = self.arg1_val
        b = self.arg2_val

        if options.LAZY_SOLVES:
            a_concrete = False
            b_concrete = False
        else:
            a_concrete = state.solver.is_concrete(a)
            b_concrete = state.solver.is_concrete(b)

        if a_concrete:
            a_val_unsigned = state.solver.eval(a)
            a_val = _unsigned_word_to_signed(a_val_unsigned)
        if b_concrete:
            b_val_unsigned = state.solver.eval(b)
            b_val = _unsigned_word_to_signed(b_val_unsigned)

        if a_concrete and b_concrete:
            result_i = a_val - b_val
            # if result does not underflow (i.e., is positive), use it as return value
            if MIN_SIGNED_WORD <= result_i <= MAX_SIGNED_WORD:
                result = BVV(_signed_word_to_unsigned(result_i), 256)
            else:
                # no non-revert states
                return []
        else:
            # do the subtraction
            a_extended = BV_Sign_Extend(a, 1)
            b_extended = BV_Sign_Extend(b, 1)
            result_extended = BV_Sub(a_extended, b_extended)

            limit_lo = _signed_word_to_unsigned(MIN_SIGNED_WORD, 257)
            limit_hi = _signed_word_to_unsigned(MAX_SIGNED_WORD, 257)

            # assert no underflow or overflow
            new_constraint = And(
                BV_SLE(BVV(limit_lo, 257), result_extended),
                BV_SLE(result_extended, BVV(limit_hi, 257)),
            )
            setattr(new_constraint, "safemath", True)
            state.solver.add_path_constraint(new_constraint)

            result = BV_Sub(a, b)

        # store the result
        state.registers[self.res1_var] = result

        return [state]


class SymProcedureSafeMul(TAC_Statement):
    __internal_name__ = "SYMPROCEDURE_SAFEMUL"
    __aliases__ = {}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: "SymbolicEVMState"):
        a = self.arg1_val
        b = self.arg2_val
        if options.LAZY_SOLVES:
            a_concrete = False
            b_concrete = False
        else:
            a_concrete = state.solver.is_concrete(a)
            b_concrete = state.solver.is_concrete(b)

        if a_concrete:
            a_val = state.solver.eval(a)
        if b_concrete:
            b_val = state.solver.eval(b)

        if a_concrete and b_concrete:
            result_i = a_val * b_val
            # if result fits within 1 word, use it as return value
            if result_i < 2**256:
                result = BVV(a_val * b_val, 256)
            else:
                # no non-revert states
                return []
        # if one of the arguments is concrete, we can do some simplification
        elif a_concrete or b_concrete:
            conc_val, sym = (a_val, b) if a_concrete else (b_val, a)

            if conc_val == 0:
                # if either is zero, the result is zero
                result = BVV(0, 256)
            if conc_val == 1:
                # if either is one, the result is the other
                result = sym
            else:
                # we can simply constrain the sym value to be such that (conc_val * sym) < 2**256
                limit = 2**256 // conc_val
                new_constraint = BV_ULT(sym, BVV(limit, 256))
                setattr(new_constraint, "safemath", True)
                state.solver.add_path_constraint(new_constraint)
                result = BV_Mul(a, b)
        else:
            # do the multiplication
            a_extended = BV_Zero_Extend(a, 256)
            b_extended = BV_Zero_Extend(b, 256)
            result_extended = BV_Mul(a_extended, b_extended)

            # assert no overflow
            limit = BVV((1 << 256), 256 * 2)
            new_constraint = BV_ULT(result_extended, limit)
            setattr(new_constraint, "safemath", True)
            state.solver.add_path_constraint(new_constraint)

            # extract the result
            result = BV_Mul(a, b)

        state.registers[self.res1_var] = result

        return [state]


class SymProcedureSafeMulSigned(TAC_Statement):
    __internal_name__ = "SYMPROCEDURE_SAFEMUL_SIGNED"
    __aliases__ = {}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: "SymbolicEVMState"):
        a = self.arg1_val
        b = self.arg2_val
        if options.LAZY_SOLVES:
            a_concrete = False
            b_concrete = False
        else:
            a_concrete = state.solver.is_concrete(a)
            b_concrete = state.solver.is_concrete(b)

        if a_concrete:
            a_val_unsigned = state.solver.eval(a)
            a_val = _unsigned_word_to_signed(a_val_unsigned)
        if b_concrete:
            b_val_unsigned = state.solver.eval(b)
            b_val = _unsigned_word_to_signed(b_val_unsigned)

        if a_concrete and b_concrete:
            result_i = a_val * b_val
            # if result fits within 1 word, use it as return value
            if MIN_SIGNED_WORD <= result_i <= MAX_SIGNED_WORD:
                result = BVV(a_val * b_val, 256)
            else:
                # no non-revert states
                return []
        # if one of the arguments is concrete, we can do some simplification
        elif a_concrete or b_concrete:
            conc_val, sym = (a_val, b) if a_concrete else (b_val, a)

            if conc_val == 0:
                # if either is zero, the result is zero
                result = BVV(0, 256)
            if conc_val == 1:
                # if either is one, the result is the other
                result = sym
            else:
                # we can simply constrain the sym value to be such that min_signed <= (conc_val * sym) <= max_signed
                # or, equivalently, min_signed // conc_val <= sym <= max_signed // conc_val
                if b > 0:
                    limit_lo = _div_rounding_to_zero(MIN_SIGNED_WORD, conc_val)
                    limit_hi = _div_rounding_to_zero(MAX_SIGNED_WORD, conc_val)
                if b < 0:
                    limit_lo = _div_rounding_to_zero(MAX_SIGNED_WORD, conc_val)
                    limit_hi = _div_rounding_to_zero(MIN_SIGNED_WORD, conc_val)

                new_constraint = And(
                    BV_SLE(BVV(_signed_word_to_unsigned(limit_lo), 256), sym),
                    BV_SLE(sym, BVV(_signed_word_to_unsigned(limit_hi), 256)),
                )
                setattr(new_constraint, "safemath", True)
                state.solver.add_path_constraint(new_constraint)
                result = BV_Mul(a, b)
        else:
            # do the multiplication
            a_extended = BV_Sign_Extend(a, 256)
            b_extended = BV_Sign_Extend(b, 256)
            result_extended = BV_Mul(a_extended, b_extended)

            # assert no overflow
            new_constraint = And(
                BV_SLE(
                    BVV(_signed_word_to_unsigned(MIN_SIGNED_WORD, 512), 512),
                    result_extended,
                ),
                BV_SLE(
                    result_extended,
                    BVV(_signed_word_to_unsigned(MAX_SIGNED_WORD, 512), 512),
                ),
            )
            setattr(new_constraint, "safemath", True)
            state.solver.add_path_constraint(new_constraint)

            # extract the result
            result = BV_Mul(a, b)

        state.registers[self.res1_var] = result

        return [state]


class SymProcedureSafeDiv(TAC_Statement):
    __internal_name__ = "SYMPROCEDURE_SAFEDIV"
    __aliases__ = {}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: "SymbolicEVMState"):
        a = self.arg1_val
        b = self.arg2_val

        # check if the arguments are concrete
        if options.LAZY_SOLVES:
            a_concrete = False
            b_concrete = False
        else:
            a_concrete = state.solver.is_concrete(a)
            b_concrete = state.solver.is_concrete(b)

        if a_concrete:
            a_val = state.solver.eval(a)
        if b_concrete:
            b_val = state.solver.eval(b)

        if b_concrete and b_val == 0:
            # division by zero, revert
            return []

        if a_concrete and b_concrete:
            # if both are concrete, we can do the division directly
            result_i = a_val // b_val
            result = BVV(result_i, 256)
        elif b_concrete:
            # We know b != 0, no need to add any more constraints
            result = BV_UDiv(a, b)
        else:
            # do the division
            result = BV_UDiv(a, b)

            # Assert no divide by zero.

            # We use GT instead of NEQ for no reason in particular
            # (it might help the 'hybrid' solver in development) - Robert
            new_constraint = BV_UGT(b, BVV(0, 256))
            setattr(new_constraint, "safemath", True)
            state.solver.add_path_constraint(new_constraint)

        # store the result
        state.registers[self.res1_var] = result

        return [state]


_next_statement_id = 0


def _gen_statement_id() -> str:
    global _next_statement_id
    _next_statement_id += 1
    return f"SAFEMATH_{_next_statement_id:02x}"


_next_var_id = 0


def _gen_var_id() -> str:
    global _next_var_id
    _next_var_id += 1
    return f"SAFEMATH_{_next_var_id:02x}"


def _unsigned_word_to_signed(i: int, bitsize=256) -> int:
    if i < 2 ** (bitsize - 1):
        return i
    return i - 2**bitsize


def _signed_word_to_unsigned(i: int, bitsize=256) -> int:
    if i >= 0:
        return i
    return i + 2**bitsize


def _div_rounding_to_zero(a, b):
    # Perform integer division
    result = a // b

    # Calculate the product of result and divisor
    product = result * b

    # Check if we need to adjust the result
    if (a < 0) != (b < 0) and a != product:
        result += 1

    return result
