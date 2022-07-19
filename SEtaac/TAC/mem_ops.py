from SEtaac.utils.solver.shortcuts import *
from .base import TAC_Statement
from ..state import SymbolicEVMState

__all__ = ['TAC_Mstore', 'TAC_Mstore8', 'TAC_Mload', 'TAC_Sload', 'TAC_Sstore', 'TAC_Msize']


class TAC_Mstore(TAC_Statement):
    __internal_name__ = "MSTORE"
    __aliases__ = {
        'offset_var': 'arg1_var', 'offset_val': 'arg1_val',
        'value_var': 'arg2_var', 'value_val': 'arg2_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        for i in range(32):
            m = BV_Extract((31 - i) * 8, (31 - i) * 8 + 7, self.value_val)
            succ.memory[BV_Add(self.offset_val, BVV(i, 256))] = m

        succ.set_next_pc()
        return [succ]


class TAC_Mstore8(TAC_Statement):
    __internal_name__ = "MSTORE8"
    __aliases__ = {
        'offset_var': 'arg1_var', 'offset_val': 'arg1_val',
        'value_var': 'arg2_var', 'value_val': 'arg2_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.memory[self.offset_val] = BV_Extract(0, 7, self.value_val)

        succ.set_next_pc()
        return [succ]


class TAC_Mload(TAC_Statement):
    __internal_name__ = "MLOAD"
    __aliases__ = {
        'offset_var': 'arg1_var', 'offset_val': 'arg1_val',
        'value_var': 'res_var', 'value_val': 'res_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.registers[self.res1_var] = succ.memory.readn(self.offset_val, BVV(32, 256))

        succ.set_next_pc()
        return [succ]


class TAC_Sload(TAC_Statement):
    __internal_name__ = "SLOAD"
    __aliases__ = {
        'key_var': 'arg1_var', 'key_val': 'arg1_val',
        'value_var': 'res_var', 'value_val': 'res_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        v = succ.storage[self.key_val]
        succ.registers[self.res1_var] = v

        succ.set_next_pc()
        return [succ]


class TAC_Sstore(TAC_Statement):
    __internal_name__ = "SSTORE"
    __aliases__ = {
        'key_var': 'arg1_var', 'key_val': 'arg1_val',
        'value_var': 'arg2_var', 'value_val': 'arg2_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.storage[self.key_val] = self.value_val

        succ.set_next_pc()
        return [succ]


class TAC_Msize(TAC_Statement):
    __internal_name__ = "MSIZE"
    __aliases__ = {
        'size_var': 'res_var', 'size_val': 'res_val'
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.registers[self.res1_var] = len(succ.memory)

        succ.set_next_pc()
        return [succ]
