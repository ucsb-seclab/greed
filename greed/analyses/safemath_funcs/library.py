"""
This module attempts to discover library-based safemath functions
(i.e., those from OpenZeppelin) by symbolic execution.
"""

import logging
from typing import Optional, Set, TYPE_CHECKING

import networkx as nx

import contextlib
import greed.options as options
from greed.solver.shortcuts import *
from greed.exploration_techniques import DirectedSearch, DFS
from greed.utils.extra import gen_exec_id

from .types import SafeMathFuncReport, SafeMathFunc
from .common import basic_safemath_checks_pass

if TYPE_CHECKING:
    from greed import Project
    from greed.state import SymbolicEVMState
    from greed.function import TAC_Function
    from greed.TAC.gigahorse_ops import TAC_Returnprivate

log = logging.getLogger(__name__)

MAX_UNSIGNED_WORD = 2**256 - 1
MAX_SIGNED_WORD = 2**255 - 1

def identify_library_safemath_func(project: 'Project', function: 'TAC_Function') -> Optional[SafeMathFuncReport]:
    log.debug(f'Examining function {function.name} for library SAFEMATH operations')

    maybe_basic_info = basic_safemath_checks_pass(project, function)
    if maybe_basic_info is None:
        return None
    return_stmts_and_vars = maybe_basic_info

    # Remove any returns that just return a constant (i.e., mul by 0 returns 0)
    return_stmts_and_vars_no_constant_returns = []
    for return_stmt, return_var in return_stmts_and_vars:
        if return_stmt.arg_vals.get(return_var) is not None:
            continue
        return_stmts_and_vars_no_constant_returns.append((return_stmt, return_var))

    if len(return_stmts_and_vars_no_constant_returns) != 1:
        log.debug(f'Function {function.name} has multiple return blocks with non-constant returns')
        return None
    
    (return_stmt, return_var) = return_stmts_and_vars_no_constant_returns[0]
    return_stmt: 'TAC_Returnprivate'

    # Ensure that the subgraph of the callgraph starting at this function is acyclic
    reachable_funcs: Set['TAC_Function'] = nx.descendants(project.callgraph, function)
    reachable_funcs.add(function)
    if not nx.is_directed_acyclic_graph(project.callgraph.subgraph(reachable_funcs)):
        log.debug(f'Function {function.name} has loops in its callgraph')
        return None
    
    # Ensure each reachable func is also acyclic
    for reachable_func in reachable_funcs:
        func_cfg = reachable_func.cfg.graph
        if not nx.is_directed_acyclic_graph(func_cfg):
            log.debug(f'Function {function.name} has loops in a reachable func\'s CFG')
            return None

    # Find all instructions used in this function, so we can return early if it uses any banned
    # instructions which indicate not-safemath.
    banned_instructions = {
        'CALL', 'CALLCODE', 'DELEGATECALL', 'STATICCALL',
        'CREATE', 'CREATE2',
        'SELFDESTRUCT',
        'SSTORE', 'SLOAD',
        'LOG0', 'LOG1', 'LOG2', 'LOG3', 'LOG4',
        'EXTCODESIZE', 'EXTCODECOPY', 'EXTCODEHASH',
        'BLOCKHASH', 'COINBASE', 'TIMESTAMP', 'NUMBER', 'DIFFICULTY', 'GASLIMIT', 'GASPRICE',
        'ORIGIN', 'CALLER', 'CALLVALUE', 'CALLDATASIZE', 'CALLDATALOAD', 'CALLDATACOPY',
        'CODESIZE', 'CODECOPY', 'CODEHASH',
        'RETURNDATASIZE', 'RETURNDATACOPY',
        'BALANCE', 'SELFBALANCE', 'ADDRESS',
        'SHA3',
        'RETURN', 'STOP', 'INVALID',
    }

    for func in reachable_funcs:
        for block in func.blocks:
            for stmt in block.statements:
                if stmt.__internal_name__ in banned_instructions:
                    log.debug(f'Function {function.name} uses banned instruction {stmt.__internal_name__}; ignoring')
                    return None


    # Start a directed symbolic execution at this function entry
    entry_state = project.factory.entry_state(
        xid=gen_exec_id(),
    )
    entry_state.pc = project.block_at[function.id].first_ins.id
    log.debug(f'Function entry: {entry_state.pc}')

    # Set up the function arguments. There should be 3:
    # 0, 1: the two operands
    # 2: the return pc
    operand_0 = BVS(f'safemath_check_{function.name}_operand_0', 256)
    operand_1 = BVS(f'safemath_check_{function.name}_operand_1', 256)
    return_pc = BVV(0x0, 256) # we will not be returning anyway

    entry_state.registers[function.arguments[0]] = operand_0
    entry_state.registers[function.arguments[1]] = operand_1
    entry_state.registers[function.arguments[2]] = return_pc

    with _with_timeout(10.0):
        with _enable_lazy_solves():
            simgr = project.factory.simgr(entry_state)

            directed_search = DirectedSearch(target_stmt=return_stmt)
            simgr.use_technique(directed_search)

            dfs = DFS()
            simgr.use_technique(dfs)

            while True:
                simgr.run(find=lambda s: s.curr_stmt.id == return_stmt.id)

                if len(simgr.found) == 0:
                    break

                # remove unsat
                simgr.move(from_stash='found', to_stash='pruned', filter_func=lambda s: s.solver.is_unsat())

                # remove any states that are returning a constant
                def is_returning_constant(s: 'SymbolicEVMState'):
                    return_var = return_stmt.arg_vars[1]
                    return_val = s.registers[return_var]
                    return s.solver.is_concrete(return_val)
                simgr.move(from_stash='found', to_stash='pruned', filter_func=is_returning_constant)

                if len(simgr.found) >= 1:
                    # found a sat state
                    break

        if len(simgr.found) == 0:
            log.debug(f'Function {function.name} did not reach the return statement')
            return None

        # We have reached the return statement.

        found_state = simgr.found[0]
        log.debug(f'Function {function.name} reached the return statement at state {found_state}')

        return_var = return_stmt.arg_vars[1]
        sym_return_var = found_state.registers[return_var]
        
        # Guess what type of math op it is by just trying a few

        # Addition: 50 + 10 == 60
        guess_assumptions = [
            Equal(operand_0, BVV(50, 256)),
            Equal(operand_1, BVV(10, 256)),
            Equal(sym_return_var, BVV(60, 256)),
        ]
        if found_state.solver.are_formulas_sat(guess_assumptions):
            # Ensure that this is generically true
            generic_assumption = Equal(BV_Add(operand_0, operand_1), sym_return_var)
            is_generic = found_state.solver.is_formula_true(generic_assumption)
            
            if not is_generic:
                log.debug(f'Function {function.name} addition is not generic')
                return None

            # Setting of vars to create overflow should be unsat
            overflow_assumption = [
                Equal(operand_0, BVV(2**256 - 1, 256)),
                Equal(operand_1, BVV(2**256 - 1, 256)),
            ]
            overflow_possible = found_state.solver.are_formulas_sat(overflow_assumption)
            
            if overflow_possible:
                log.debug(f'Function {function.name} addition can overflow without revert')
                return None
            
            return SafeMathFuncReport(
                func_kind=SafeMathFunc.ADD,
                func=function,
                first_arg_at_start=True,
            )
        
        # Subtraction: 50 - 10 == 40
        sym_sub_forward = BVS(f'safemath_check_{function.name}_sub_is_forward', 256)
        guess_assumptions = [
            Or(
                And(
                    Equal(operand_0, BVV(50, 256)),
                    Equal(operand_1, BVV(10, 256)),
                    Equal(sym_return_var, BVV(40, 256)),
                    Equal(sym_sub_forward, BVV(1, 256)),
                ),
                And(
                    Equal(operand_1, BVV(50, 256)),
                    Equal(operand_0, BVV(10, 256)),
                    Equal(sym_return_var, BVV(40, 256)),
                    Equal(sym_sub_forward, BVV(2, 256)),
                ),
            ),
        ]
        if found_state.solver.are_formulas_sat(guess_assumptions):
            sub_forward_val = found_state.solver.eval(sym_sub_forward)
            if sub_forward_val == 1:
                sub_forward = True
            elif sub_forward_val == 2:
                sub_forward = False
            else:
                log.debug(f'Function {function.name} subtraction direction is unknown')
                return None
            
            minuend, subtrahend = (operand_0, operand_1) if sub_forward else (operand_1, operand_0)

            # Ensure that this is generically true
            generic_assumption = Equal(BV_Sub(minuend, subtrahend), sym_return_var)
            is_generic = found_state.solver.is_formula_true(generic_assumption)

            # Ensure that sub underflow is unsat
            sub_underflow_assumption = [
                Equal(subtrahend, BVV(2**256 - 1, 256)),
                Equal(minuend, BVV(0, 256)),
            ]
            sub_underflow_possible = found_state.solver.are_formulas_sat(sub_underflow_assumption)

            if is_generic and not sub_underflow_possible:
                return SafeMathFuncReport(
                    func_kind=SafeMathFunc.SUB,
                    func=function,
                    first_arg_at_start=sub_forward,
                )

        # Multiplication: 50 * 10 == 500
        guess_assumptions = [
            Equal(operand_0, BVV(50, 256)),
            Equal(operand_1, BVV(10, 256)),
            Equal(sym_return_var, BVV(500, 256)),
        ]
        if found_state.solver.are_formulas_sat(guess_assumptions):
            # Ensure that this is generically true
            generic_assumption = Equal(BV_Mul(operand_0, operand_1), sym_return_var)
            is_generic = found_state.solver.is_formula_true(generic_assumption)

            # Ensure that mul with overflow is unsat
            overflow_assumption = [
                Equal(operand_0, BVV(2**128, 256)),
                Equal(operand_1, BVV(2**128, 256)),
            ]
            overflow_possible = found_state.solver.are_formulas_sat(overflow_assumption)

            # Ensure that you can receive a value greater than max signed word
            a = (MAX_SIGNED_WORD // 100) + 1
            b = 100
            assert MAX_SIGNED_WORD < a * b <= MAX_UNSIGNED_WORD, 'Product should be above max signed word'
            assert int.from_bytes(a.to_bytes(32, 'big', signed=False), 'big', signed=True) > 0, 'a should be positive (in signed view)'
            assert int.from_bytes(b.to_bytes(32, 'big', signed=False), 'big', signed=True) > 0, 'b should be positive (in signed view)'
            assert int.from_bytes((a * b).to_bytes(32, 'big', signed=False), 'big', signed=True) < 0, 'product should be negative (in signed view)'
            signed_overflow_assumption = [
                Equal(operand_0, BVV(a, 256)),
                Equal(operand_1, BVV(b, 256)),
            ]
            signed_overflow_possible = found_state.solver.are_formulas_sat(signed_overflow_assumption)

            if is_generic and signed_overflow_possible and not overflow_possible:
                return SafeMathFuncReport(
                    func_kind=SafeMathFunc.MUL,
                    func=function,
                    first_arg_at_start=True,
                )

        # Division: 50 / 10 == 5
        sym_div_forward = BVS(f'safemath_check_{function.name}_div_is_forward', 256)
        guess_assumptions = [
            Or(
                And(
                    Equal(operand_0, BVV(50, 256)),
                    Equal(operand_1, BVV(10, 256)),
                    Equal(sym_return_var, BVV(5, 256)),
                    Equal(sym_div_forward, BVV(1, 256)),
                ),
                And(
                    Equal(operand_1, BVV(50, 256)),
                    Equal(operand_0, BVV(10, 256)),
                    Equal(sym_return_var, BVV(5, 256)),
                    Equal(sym_div_forward, BVV(2, 256)),
                ),
            ),
        ]
        if found_state.solver.are_formulas_sat(guess_assumptions):
            # Query the model to find out if arguments go forward or backward
            div_forward_val = found_state.solver.eval(sym_div_forward)
            if div_forward_val == 1:
                div_forward = True
            elif div_forward_val == 2:
                div_forward = False
            else:
                log.debug(f'Function {function.name} division direction is unknown')
                return None

            dividend, divisor = (operand_0, operand_1) if div_forward else (operand_1, operand_0)

            # Ensure that this is generically true
            generic_assumption = Equal(BV_UDiv(dividend, divisor), sym_return_var)
            is_generic = found_state.solver.is_formula_true(generic_assumption)

            # Ensure that div by zero is unsat
            div_by_zero_assumption = Equal(divisor, BVV(0, 256))
            div_by_zero_possible = found_state.solver.is_formula_sat(div_by_zero_assumption)

            if is_generic and not div_by_zero_possible:
                return SafeMathFuncReport(
                    func_kind=SafeMathFunc.DIV,
                    func=function,
                    first_arg_at_start=div_forward,
                )
        
        # Modulo: 52 % 10 == 2
        sym_mod_forward = BVS(f'safemath_check_{function.name}_mod_is_forward', 256)
        guess_assumptions = [
            Or(
                And(
                    Equal(operand_0, BVV(52, 256)),
                    Equal(operand_1, BVV(10, 256)),
                    Equal(sym_return_var, BVV(2, 256)),
                    Equal(sym_mod_forward, BVV(1, 256)),
                ),
                And(
                    Equal(operand_1, BVV(52, 256)),
                    Equal(operand_0, BVV(10, 256)),
                    Equal(sym_return_var, BVV(2, 256)),
                    Equal(sym_mod_forward, BVV(2, 256)),
                ),
            ),
        ]
        if found_state.solver.are_formulas_sat(guess_assumptions):
            # Query the model to find out if arguments go forward or backward
            mod_forward_val = found_state.solver.eval(sym_mod_forward)
            if mod_forward_val == 1:
                mod_forward = True
            elif mod_forward_val == 2:
                mod_forward = False
            else:
                log.debug(f'Function {function.name} modulo direction is unknown')
                return None

            dividend, divisor = (operand_0, operand_1) if mod_forward else (operand_1, operand_0)

            # Ensure that this is generically true
            generic_assumption = Equal(BV_URem(dividend, divisor), sym_return_var)
            is_generic = found_state.solver.is_formula_true(generic_assumption)

            # Ensure that div by zero is unsat
            div_by_zero_assumption = Equal(divisor, BVV(0, 256))
            div_by_zero_possible = found_state.solver.is_formula_sat(div_by_zero_assumption)

            if is_generic and not div_by_zero_possible:
                return SafeMathFuncReport(
                    func_kind=SafeMathFunc.MOD,
                    func=function,
                    first_arg_at_start=mod_forward,
                )


        # If we reach here, we couldn't guess the operation
        log.debug(f'Function {function.name} could not guess the operation')

        return None

@contextlib.contextmanager
def _enable_lazy_solves():
    old_lazy_solves = options.LAZY_SOLVES
    options.LAZY_SOLVES = True
    try:
        yield
    finally:
        options.LAZY_SOLVES = old_lazy_solves


@contextlib.contextmanager
def _with_timeout(timeout: float):
    old_timeout = options.SOLVER_TIMEOUT
    options.SOLVER_TIMEOUT = timeout
    try:
        yield
    finally:
        options.SOLVER_TIMEOUT = old_timeout
