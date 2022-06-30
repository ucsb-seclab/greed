from SEtaac import utils
from SEtaac.utils import concrete
from .base import TAC_Statement
from ..state import SymbolicEVMState

from SEtaac.utils.solver.shortcuts import *

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

        succ.memory.extend(self.offset_val, 32)
        if concrete(self.value_val):
            succ.memory.write(self.offset_val, 32, utils.encode_int32(self.value_val))
        else:
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

        succ.memory.extend(self.offset_val, 1)
        succ.memory[self.offset_val] = self.value_val % 256

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

        succ.memory.extend(self.offset_val, 32)
        mm = [succ.memory[BV_Add(self.offset_val, BVV(i, 256))] for i in range(32)]
        if all(concrete(m) for m in mm):
            succ.registers[self.res1_var] = utils.bytes_to_int(succ.memory.read(self.offset_val, 32))
        else:
            v = BV_Concat([m for m in mm])
            succ.registers[self.res1_var] = v

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
