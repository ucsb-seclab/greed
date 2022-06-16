
import z3

from SEtaac import utils
from SEtaac.utils import concrete
from .base import TAC_Statement
from ..state import SymbolicEVMState

__all__ = ['TAC_Mstore', 'TAC_Mstore8', 'TAC_Mload', 'TAC_Sload', 'TAC_Sstore', 'TAC_Msize']

class TAC_Mstore(TAC_Statement):
    __internal_name__ = "MSTORE"
    __aliases__ = {
                   'offset_var' : 'arg1_var', 'offset_val' : 'arg1_val',
                   'value_var'  : 'arg2_var', 'value_val'  : 'arg2_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.arg1_var]
        arg2 = succ.registers[self.arg2_var]

        # todo: check operand order here
        state.memory.extend(arg1, 32)
        if concrete(arg2):
            state.memory.write(arg1, 32, utils.encode_int32(arg2))
        else:
            for i in range(32):
                m = z3.simplify(z3.Extract((31 - i) * 8 + 7, (31 - i) * 8, arg2))
                if z3.is_bv_value(m):
                    state.memory[arg1 + i] = m.as_long()
                else:
                    state.memory[arg1 + i] = m

        succ.set_next_pc()
        return [succ]

class TAC_Mstore8(TAC_Statement):
    __internal_name__ = "MSTORE8"
    __aliases__ = {
                   'offset_var' : 'arg1_var', 'offset_val' : 'arg1_val',
                   'value_var'  : 'arg2_var', 'value_val'  : 'arg2_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.arg1_var]
        arg2 = succ.registers[self.arg2_var]

        state.memory.extend(arg1, 1)
        state.memory[arg1] = arg2 % 256

        succ.set_next_pc()
        return [succ]

class TAC_Mload(TAC_Statement):
    __internal_name__ = "MLOAD"
    __aliases__ = {
                   'offset_var' : 'arg1_var', 'offset_val' : 'arg1_val',
                   'value_var'  : 'res_var', 'value_val'  : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.arg1_var]

        state.memory.extend(arg1, 32)
        mm = [state.memory[arg1 + i] for i in range(32)]
        if all(concrete(m) for m in mm):
            succ.registers[self.res1_var] = utils.bytes_to_int(state.memory.read(arg1, 32))
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
                   'key_var'    : 'arg1_var', 'key_val'    : 'arg1_val',
                   'value_var'  : 'res_var', 'value_val'  : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.arg1_var]

        v = z3.simplify(state.storage[arg1])
        if z3.is_bv_value(v):
            succ.registers[self.res1_var] = v.as_long()
        else:
            succ.registers[self.res1_var] = v

        succ.set_next_pc()
        return [succ]

class TAC_Sstore(TAC_Statement):
    __internal_name__ = "SSTORE"
    __aliases__ = {
                   'key_var'    : 'arg1_var', 'key_val'    : 'arg1_val',
                   'value_var'  : 'arg2_var', 'value_val'  : 'arg2_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.arg1_var]
        arg2 = succ.registers[self.arg2_var]

        state.storage[arg1] = arg2

        succ.set_next_pc()
        return [succ]

class TAC_Msize(TAC_Statement):
    __internal_name__ = "MSIZE"
    __aliases__ = {
                   'size_var'  : 'res_var', 'size_val'  : 'res_val'
                  }

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        succ.registers[self.res1_var] = len(state.memory)

        succ.set_next_pc()
        return [succ]