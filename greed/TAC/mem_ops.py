from greed.solver.shortcuts import *
from greed.TAC.base import TAC_Statement
from greed.state import SymbolicEVMState

__all__ = ['TAC_Mstore', 'TAC_Mstore8', 'TAC_Mload', 'TAC_Sload', 'TAC_Sstore', 'TAC_Msize']


"""
This module contains the TAC statements that are related to the memory and storage operations.
"""

class TAC_Mstore(TAC_Statement):
    __internal_name__ = "MSTORE"
    __aliases__ = {
        'offset_var': 'arg1_var', 'offset_val': 'arg1_val',
        'value_var': 'arg2_var', 'value_val': 'arg2_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        # for i in range(32):
        #     m = BV_Extract((31 - i) * 8, (31 - i) * 8 + 7, self.value_val)
        #     state.memory[BV_Add(self.offset_val, BVV(i, 256))] = m
        state.memory.writen(self.offset_val, self.value_val, BVV(32, 256))

        state.set_next_pc()
        return [state]


class TAC_Mstore8(TAC_Statement):
    __internal_name__ = "MSTORE8"
    __aliases__ = {
        'offset_var': 'arg1_var', 'offset_val': 'arg1_val',
        'value_var': 'arg2_var', 'value_val': 'arg2_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        state.memory[self.offset_val] = BV_Extract(0, 7, self.value_val)

        state.set_next_pc()
        return [state]


class TAC_Mload(TAC_Statement):
    __internal_name__ = "MLOAD"
    __aliases__ = {
        'offset_var': 'arg1_var', 'offset_val': 'arg1_val',
        'value_var': 'res1_var', 'value_val': 'res1_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = state.memory.readn(self.offset_val, BVV(32, 256))

        state.set_next_pc()
        return [state]


class TAC_Sload(TAC_Statement):
    __internal_name__ = "SLOAD"
    __aliases__ = {
        'key_var': 'arg1_var', 'key_val': 'arg1_val',
        'value_var': 'res1_var', 'value_val': 'res1_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        v = state.storage[self.key_val]
        state.registers[self.res1_var] = v

        state.set_next_pc()
        return [state]


class TAC_Sstore(TAC_Statement):
    __internal_name__ = "SSTORE"
    __aliases__ = {
        'key_var': 'arg1_var', 'key_val': 'arg1_val',
        'value_var': 'arg2_var', 'value_val': 'arg2_val'
    }

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        state.storage[self.key_val] = self.value_val

        state.set_next_pc()
        return [state]


class TAC_Msize(TAC_Statement):
    __internal_name__ = "MSIZE"
    __aliases__ = {
        'size_var': 'res1_var', 'size_val': 'res1_val'
    }

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        # TODO: properly implement MSIZE
        state.registers[self.res1_var] = BVS("MSIZE", 256)
        
        state.set_next_pc()
        return [state]
