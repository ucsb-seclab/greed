import logging

from SEtaac.TAC.base import TAC_Statement
from SEtaac.solver.shortcuts import *
from SEtaac.state import SymbolicEVMState
from SEtaac.utils.exceptions import VMNoSuccessors

__all__ = ['TAC_Throw', 'TAC_Callprivate', 'TAC_Returnprivate', 'TAC_Phi', 'TAC_Const', 'TAC_Nop']

log = logging.getLogger(__name__)


class TAC_Throw(TAC_Statement):
    __internal_name__ = "THROW"

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        state.halt = True
        return [state]


class TAC_Callprivate(TAC_Statement):
    __internal_name__ = "CALLPRIVATE"
    __aliases__ = {}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        # read target
        target_bb_id = hex(bv_unsigned_value(self.arg1_val))
        target_bb = state.project.factory.block(target_bb_id)

        # read arg-alias map
        args = self.arg_vars[1:]
        args_alias = target_bb.function.arguments
        assert len(args) == len(args_alias), "Invalid CALLPRIVATE arguments"
        alias_arg_map = dict(zip(args_alias, args))

        for alias, arg in alias_arg_map.items():
            state.registers[alias] = state.registers[arg]

        # read destination
        dest = target_bb.first_ins.id

        known_returns = set()
        for bb in target_bb.function.blocks:
            for stmt in bb.statements:
                if stmt.__internal_name__ == "RETURNPRIVATE":
                    try:
                        known_returns.add(state.get_non_fallthrough_pc(state.registers[stmt.arg1_var]))
                    except:
                        pass
        try:
            known_returns.add(state.get_fallthrough_pc())
        except:
            pass
        known_returns = list(known_returns)

        state.callstack.append((state.pc, known_returns, self.res_vars))

        # jump to target
        state.pc = dest
        return [state]


class TAC_Returnprivate(TAC_Statement):
    __internal_name__ = "RETURNPRIVATE"
    __aliases__ = {}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        # pop stack frame (read callprivate pc from stack)
        callprivate_pc, _, callprivate_return_vars = state.callstack.pop()

        # set the return variables to their correct values
        returnprivate_args = self.arg_vars[1:]
        for callprivate_return_var, returnprivate_arg in zip(callprivate_return_vars, returnprivate_args):
            state.registers[callprivate_return_var] = state.registers[returnprivate_arg]

        # restore callprivate pc to translate return pc
        state.pc = callprivate_pc
        return_pc = state.get_non_fallthrough_pc(state.registers[self.arg1_var])

        state.pc = return_pc
        return [state]


class TAC_Phi(TAC_Statement):
    __internal_name__ = "PHI"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.set_next_pc()
        return [state]


class TAC_Const(TAC_Statement):
    __internal_name__ = "CONST"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = self.res1_val
        state.set_next_pc()
        return [state]


class TAC_Nop(TAC_Statement):
    __internal_name__ = "NOP"

    # @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.set_next_pc()
        return [state]
