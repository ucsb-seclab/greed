import z3

from SEtaac import utils
from SEtaac.exceptions import SymbolicError
from SEtaac.utils import concrete

from .base import TAC_Unary, TAC_Binary, TAC_Ternary
from ..state import SymbolicEVMState

__all__ = [
    'TAC_Add', 'TAC_Sub', 'TAC_Mul', 'TAC_Div', 'TAC_Sdiv',
    'TAC_Mod', 'TAC_Smod', 'TAC_Addmod', 'TAC_Mulmod', 'TAC_Exp',
    'TAC_Signextend', 'TAC_Lt', 'TAC_Gt', 'TAC_Slt', 'TAC_Sgt',
    'TAC_Eq', 'TAC_Iszero', 'TAC_And', 'TAC_Or', 'TAC_Xor',
    'TAC_Not', 'TAC_Byte', 'TAC_Shl', 'TAC_Shr', 'TAC_Sar'
]


class TAC_Add(TAC_Binary):
    __internal_name__ = "ADD"
    __aliases__ = {}

    def handle(self, state: SymbolicEVMState):
        # Grab vals from Gigahorse IR and registers
        # if they are available.
        self.set_op_val(state)
        succ = state.copy()

        # If we already have the result of the op
        # from the Gigahorse IR, just use it.
        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        succ.registers[self.res_var] = self.op1_val + self.op2_val

        succ.set_next_pc()
        return [succ]


class TAC_Sub(TAC_Binary):
    __internal_name__ = "SUB"
    __aliases__ = {}

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        succ.registers[self.res_var] = self.op1_val - self.op2_val

        succ.set_next_pc()
        return [succ]


class TAC_Mul(TAC_Binary):
    __internal_name__ = "MUL"
    __aliases__ = {}

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        succ.registers[self.res_var] = self.op1_val * self.op2_val

        succ.set_next_pc()
        return [succ]


class TAC_Div(TAC_Binary):
    __internal_name__ = "DIV"
    __aliases__ = {}

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.op2_val):
            succ.registers[self.res_var] = 0 if self.op2_val == 0 else self.op1_val / self.op2_val if concrete(
                self.op1_val) else z3.UDiv(self.op1_val, self.op2_val)
        else:
            succ.registers[self.res_var] = z3.If(self.op2_val == 0, z3.BitVecVal(0, 256),
                                                 z3.UDiv(self.op1_val, self.op2_val))

        succ.set_next_pc()
        return [succ]


class TAC_Sdiv(TAC_Binary):
    __internal_name__ = "SDIV"
    __aliases__ = {}

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.op1_val) and concrete(self.op2_val):
            self.op1_val, self.op2_val = utils.to_signed(self.op1_val), utils.to_signed(self.op2_val)
            succ.registers[self.res_var] = 0 if self.op2_val == 0 else abs(self.op1_val) // abs(self.op2_val) * (
                -1 if self.op1_val * self.op2_val < 0 else 1)
        elif concrete(self.op2_val):
            succ.registers[self.res_var] = 0 if self.op2_val == 0 else self.op1_val / self.op2_val
        else:
            succ.registers[self.res_var] = z3.If(self.op2_val == 0, z3.BitVecVal(0, 256), self.op1_val / self.op2_val)

        succ.set_next_pc()
        return [succ]


class TAC_Mod(TAC_Binary):
    __internal_name__ = "MOD"
    __aliases__ = {}

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.op2_val):
            succ.registers[self.res_var] = 0 if self.op2_val == 0 else self.op1_val % self.op2_val
        else:
            succ.registers[self.res_var] = z3.If(self.op2_val == 0, z3.BitVecVal(0, 256),
                                                 z3.URem(self.op1_val, self.op2_val))

        succ.set_next_pc()
        return [succ]


class TAC_Smod(TAC_Binary):
    __internal_name__ = "SMOD"

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.op1_val) and concrete(self.op2_val):
            self.op1_val, self.op2_val = utils.to_signed(self.op1_val), utils.to_signed(self.op2_val)
            succ.registers[self.res_var] = 0 if self.op2_val == 0 else abs(self.op1_val) % abs(self.op2_val) * (
                -1 if self.op1_val < 0 else 1)
        elif concrete(self.op2_val):
            succ.registers[self.res_var] = 0 if self.op2_val == 0 else z3.SRem(self.op1_val, self.op2_val)
        else:
            succ.registers[self.res_var] = z3.If(self.op2_val == 0, z3.BitVecVal(0, 256),
                                                 z3.SRem(self.op1_val, self.op2_val))

        succ.set_next_pc()
        return [succ]


class TAC_Addmod(TAC_Ternary):
    __internal_name__ = "ADDMOD"
    __aliases__ = {'denominator_var': 'op3_var', 'denominator_val': 'op3_val'}

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.denominator_val):
            succ.registers[self.res_var] = (
                                                       self.op1_val + self.op2_val) % self.denominator_val if self.denominator_val else 0
        else:
            succ.registers[self.res_var] = z3.If(self.denominator_val == 0, z3.BitVecVal(0, 256),
                                                 z3.URem((self.op1_val + self.op2_val), self.denominator_val))

        succ.set_next_pc()
        return [succ]


class TAC_Mulmod(TAC_Ternary):
    __internal_name__ = "MULMOD"
    __aliases__ = {'denominator_var': 'op3_var', 'denominator_val': 'op3_val'}

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.denominator_val):
            succ.registers[self.res_var] = (
                                                       self.op1_val * self.op2_val) % self.denominator_val if self.denominator_val else 0
        else:
            succ.registers[self.res_var] = z3.If(self.denominator_val == 0, z3.BitVecVal(0, 256),
                                                 z3.URem((self.op1_val * self.op2_val), self.denominator_val))

        succ.set_next_pc()
        return [succ]


class TAC_Exp(TAC_Binary):
    __internal_name__ = "EXP"
    __aliases__ = {'base_var': 'op1_var', 'base_val': 'op1_val', 'exp_var': 'op2_var', 'exp_val': 'op2_val'}

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.base_val) and concrete(self.exp_val):
            succ.registers[self.res_var] = pow(self.base_val, self.exp_val, utils.TT256)
        else:
            if concrete(self.base_val) and utils.is_pow2(self.base_val):
                l2 = utils.log2(self.base_val)
                succ.registers[self.res_var] = 1 << (l2 * self.exp_val)
            else:
                raise SymbolicError('exponentiation with symbolic exponent currently not supported :-/')

        succ.set_next_pc()
        return [succ]


class TAC_Signextend(TAC_Binary):
    __internal_name__ = "SIGNEXTEND"

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.op1_val) and concrete(self.op2_val):
            if self.op1_val <= 31:
                testbit = self.op1_val * 8 + 7
                if self.op2_val & (1 << testbit):
                    succ.registers[self.res_var] = self.op2_val | (utils.TT256 - (1 << testbit))
                else:
                    succ.registers[self.res_var] = self.op2_val & ((1 << testbit) - 1)
            else:
                succ.registers[self.res_var] = self.op2_val
        elif concrete(self.op1_val):
            if self.op1_val <= 31:
                oldwidth = (self.op1_val + 1) * 8
                succ.registers[self.res_var] = z3.SignExt(256 - oldwidth, self.op2_val)
            else:
                succ.registers[self.res_var] = self.op2_val
        else:
            raise SymbolicError('symbolic bitwidth for signextension is currently not supported')

        succ.set_next_pc()
        return [succ]


class TAC_Lt(TAC_Binary):
    __internal_name__ = "LT"

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.op1_val) and concrete(self.op2_val):
            succ.registers[self.res_var] = 1 if self.op1_val < self.op2_val else 0
        else:
            succ.registers[self.res_var] = z3.If(z3.ULT(self.op1_val, self.op2_val), z3.BitVecVal(1, 256),
                                                 z3.BitVecVal(0, 256))

        succ.set_next_pc()
        return [succ]


class TAC_Gt(TAC_Binary):
    __internal_name__ = "GT"

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.op1_val) and concrete(self.op2_val):
            succ.registers[self.res_var] = 1 if self.op1_val > self.op2_val else 0
        else:
            succ.registers[self.res_var] = z3.If(z3.UGT(self.op1_val, self.op2_val), z3.BitVecVal(1, 256),
                                                 z3.BitVecVal(0, 256))

        succ.set_next_pc()
        return [succ]


class TAC_Slt(TAC_Binary):
    __internal_name__ = "SLT"

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.op1_val) and concrete(self.op2_val):
            self.op1_val, self.op2_val = utils.to_signed(self.op1_val), utils.to_signed(self.op2_val)
            succ.registers[self.res_var] = 1 if self.op1_val < self.op2_val else 0
        else:
            succ.registers[self.res_var] = z3.If(self.op1_val < self.op2_val, z3.BitVecVal(1, 256),
                                                 z3.BitVecVal(0, 256))

        succ.set_next_pc()
        return [succ]


class TAC_Sgt(TAC_Binary):
    __internal_name__ = "SGT"

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.op1_val) and concrete(self.op2_val):
            self.op1_val, self.op2_val = utils.to_signed(self.op1_val), utils.to_signed(self.op2_val)
            succ.registers[self.res_var] = 1 if self.op1_val > self.op2_val else 0
        else:
            succ.registers[self.res_var] = z3.If(self.op1_val > self.op2_val, z3.BitVecVal(1, 256),
                                                 z3.BitVecVal(0, 256))

        succ.set_next_pc()
        return [succ]


class TAC_Eq(TAC_Binary):
    __internal_name__ = "EQ"

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.op1_val) and concrete(self.op2_val):
            succ.registers[self.res_var] = 1 if self.op1_val == self.op2_val else 0
        else:
            succ.registers[self.res_var] = z3.If(self.op1_val == self.op2_val, z3.BitVecVal(1, 256),
                                                 z3.BitVecVal(0, 256))

        succ.set_next_pc()
        return [succ]


class TAC_Iszero(TAC_Unary):
    __internal_name__ = "ISZERO"

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.op1_val):
            succ.registers[self.res_var] = 1 if self.op1_val == 0 else 0
        else:
            succ.registers[self.res_var] = z3.If(self.op1_val == 0, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256))

        succ.set_next_pc()
        return [succ]


class TAC_And(TAC_Binary):
    __internal_name__ = "AND"

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        succ.registers[self.res_var] = self.op1_val & self.op2_val

        succ.set_next_pc()
        return [succ]


class TAC_Or(TAC_Binary):
    __internal_name__ = "OR"

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        succ.registers[self.res_var] = self.op1_val | self.op2_val

        succ.set_next_pc()
        return [succ]


class TAC_Xor(TAC_Binary):
    __internal_name__ = "XOR"

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        succ.registers[self.res_var] = self.op1_val ^ self.op2_val

        succ.set_next_pc()
        return [succ]


class TAC_Not(TAC_Unary):
    __internal_name__ = "NOT"

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        succ.registers[self.res_var] = ~self.op1_val

        succ.set_next_pc()
        return [succ]


class TAC_Byte(TAC_Binary):
    __internal_name__ = "BYTE"
    __aliases__ = {'offset_var': 'op1_var', 'offset_val': 'op1_val'}

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.offset_val):
            if self.offset_val >= 32:
                succ.registers[self.res_var] = 0
            else:
                if concrete(self.op2_val):
                    succ.registers[self.res_var] = (self.op2_val // 256 ** (31 - self.offset_val)) % 256
                else:
                    v = z3.simplify(
                        z3.Extract((31 - self.offset_val) * 8 + 7, (31 - self.offset_val) * 8, self.op2_val))
                    if z3.is_bv_value(v):
                        succ.registers[self.res_var] = v.as_long()
                    else:
                        succ.registers[self.res_var] = z3.ZeroExt(256 - 32, v)
        else:
            raise SymbolicError('symbolic byte-index not supported')

        succ.set_next_pc()
        return [succ]


class TAC_Shl(TAC_Binary):
    __internal_name__ = "SHL"
    __aliases__ = {'shift_var': 'op1_var', 'shift_val': 'op1_val'}

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        succ.registers[self.res_var] = self.op2_val << self.shift_val

        succ.set_next_pc()
        return [succ]


class TAC_Shr(TAC_Binary):
    __internal_name__ = "SHR"
    __aliases__ = {'shift_var': 'op1_var', 'shift_val': 'op1_val'}

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        if concrete(self.op2_val) and concrete(self.shift_val):
            succ.registers[self.res_var] = self.op2_val >> self.shift_val
        else:
            succ.registers[self.res_var] = z3.LShR(self.op2_val, self.shift_val)

        succ.set_next_pc()
        return [succ]


class TAC_Sar(TAC_Binary):
    __internal_name__ = "SAR"
    __aliases__ = {'shift_var': 'op1_var', 'shift_val': 'op1_val'}

    def handle(self, state: SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        if self.res_var and self.res_val:
            succ.registers[self.res_var] = self.res_val
            succ.set_next_pc()
            return [succ]

        succ.registers[self.res_var] = utils.to_signed(self.op2_val) >> self.shift_val

        succ.set_next_pc()
        return [succ]
