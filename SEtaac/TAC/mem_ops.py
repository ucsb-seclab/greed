import z3

from SEtaac import utils
from SEtaac.utils import concrete
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
        succ = state.copy()

        succ.memory.extend(self.offset_val, 32)
        if concrete(self.value_val):
            succ.memory.write(self.offset_val, 32, utils.encode_int32(self.value_val))
        else:
            for i in range(32):
                m = z3.simplify(z3.Extract((31 - i) * 8 + 7, (31 - i) * 8, self.value_val))
                if z3.is_bv_value(m):
                    succ.memory[self.offset_val + i] = m.as_long()
                else:
                    succ.memory[self.offset_val + i] = m

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
        succ = state.copy()

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
        succ = state.copy()

        succ.memory.extend(self.offset_val, 32)
        mm = [succ.memory[self.offset_val + i] for i in range(32)]
        if all(concrete(m) for m in mm):
            succ.registers[self.res1_var] = utils.bytes_to_int(succ.memory.read(self.offset_val, 32))
        else:
            v = z3.simplify(z3.Concat([m if not concrete(m) else z3.BitVecVal(m, 8) for m in mm]))
            if z3.is_bv_value(v):
                succ.registers[self.res1_var] = v.as_long()
            else:
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
        succ = state.copy()

        v = z3.simplify(succ.storage[self.key_val])
        if z3.is_bv_value(v):
            succ.registers[self.res1_var] = v.as_long()
        else:
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
        succ = state.copy()

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
        succ = state.copy()

        succ.registers[self.res1_var] = len(succ.memory)

        succ.set_next_pc()
        return [succ]
