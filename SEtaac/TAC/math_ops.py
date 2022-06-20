import z3

from SEtaac import utils
from SEtaac.exceptions import SymbolicError
from SEtaac.utils import concrete
from .base import TAC_Statement
from ..state import SymbolicEVMState

__all__ = [
    'TAC_Add', 'TAC_Sub', 'TAC_Mul', 'TAC_Div', 'TAC_Sdiv',
    'TAC_Mod', 'TAC_Smod', 'TAC_Addmod', 'TAC_Mulmod', 'TAC_Exp',
    'TAC_Signextend', 'TAC_Lt', 'TAC_Gt', 'TAC_Slt', 'TAC_Sgt',
    'TAC_Eq', 'TAC_Iszero', 'TAC_And', 'TAC_Or', 'TAC_Xor',
    'TAC_Not', 'TAC_Byte', 'TAC_Shl', 'TAC_Shr', 'TAC_Sar'
]


class TAC_Add(TAC_Statement):
    __internal_name__ = "ADD"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.registers[self.res1_var] = self.arg1_val + self.arg2_val

        succ.set_next_pc()
        return [succ]


class TAC_Sub(TAC_Statement):
    __internal_name__ = "SUB"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.registers[self.res1_var] = self.arg1_val - self.arg2_val

        succ.set_next_pc()
        return [succ]


class TAC_Mul(TAC_Statement):
    __internal_name__ = "MUL"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.registers[self.res1_var] = self.arg1_val * self.arg2_val

        succ.set_next_pc()
        return [succ]


class TAC_Div(TAC_Statement):
    __internal_name__ = "DIV"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.arg2_val):
            if self.arg2_val == 0:
                succ.registers[self.res1_var] = 0
            elif concrete(self.arg1_val):
                succ.registers[self.res1_var] = self.arg1_val // self.arg2_val
            else:
                succ.registers[self.res1_var] = z3.UDiv(self.arg1_val, self.arg2_val)
        else:
            succ.registers[self.res1_var] = z3.If(self.arg2_val == 0, z3.BitVecVal(0, 256),
                                                  z3.UDiv(self.arg1_val, self.arg2_val))

        succ.set_next_pc()
        return [succ]


class TAC_Sdiv(TAC_Statement):
    __internal_name__ = "SDIV"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.arg1_val) and concrete(self.arg2_val):
            self.arg1_val, self.arg2_val = utils.to_signed(self.arg1_val), utils.to_signed(self.arg2_val)
            succ.registers[self.res1_var] = 0 if self.arg2_val == 0 else abs(self.arg1_val) // abs(self.arg2_val) * (
                -1 if self.arg1_val * self.arg2_val < 0 else 1)
        elif concrete(self.arg2_val):
            succ.registers[self.res1_var] = 0 if self.arg2_val == 0 else self.arg1_val // self.arg2_val
        else:
            succ.registers[self.res1_var] = z3.If(self.arg2_val == 0, z3.BitVecVal(0, 256),
                                                  self.arg1_val / self.arg2_val)

        succ.set_next_pc()
        return [succ]


class TAC_Mod(TAC_Statement):
    __internal_name__ = "MOD"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.arg2_val):
            succ.registers[self.res1_var] = 0 if self.arg2_val == 0 else self.arg1_val % self.arg2_val
        else:
            succ.registers[self.res1_var] = z3.If(self.arg2_val == 0, z3.BitVecVal(0, 256),
                                                  z3.URem(self.arg1_val, self.arg2_val))

        succ.set_next_pc()
        return [succ]


class TAC_Smod(TAC_Statement):
    __internal_name__ = "SMOD"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.arg1_val) and concrete(self.arg2_val):
            self.arg1_val, self.arg2_val = utils.to_signed(self.arg1_val), utils.to_signed(self.arg2_val)
            succ.registers[self.res1_var] = 0 if self.arg2_val == 0 else abs(self.arg1_val) % abs(self.arg2_val) * (
                -1 if self.arg1_val < 0 else 1)
        elif concrete(self.arg2_val):
            succ.registers[self.res1_var] = 0 if self.arg2_val == 0 else z3.SRem(self.arg1_val, self.arg2_val)
        else:
            succ.registers[self.res1_var] = z3.If(self.arg2_val == 0, z3.BitVecVal(0, 256),
                                                  z3.SRem(self.arg1_val, self.arg2_val))

        succ.set_next_pc()
        return [succ]


class TAC_Addmod(TAC_Statement):
    __internal_name__ = "ADDMOD"
    __aliases__ = {'denominator_var': 'arg3_var', 'denominator_val': 'arg3_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.denominator_val):
            succ.registers[self.res1_var] = (self.arg1_val + self.arg2_val) % \
                                            self.denominator_val if self.denominator_val else 0
        else:
            succ.registers[self.res1_var] = z3.If(self.denominator_val == 0, z3.BitVecVal(0, 256),
                                                  z3.URem((self.arg1_val + self.arg2_val), self.denominator_val))

        succ.set_next_pc()
        return [succ]


class TAC_Mulmod(TAC_Statement):
    __internal_name__ = "MULMOD"
    __aliases__ = {'denominator_var': 'arg3_var', 'denominator_val': 'arg3_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.denominator_val):
            succ.registers[self.res1_var] = (self.arg1_val * self.arg2_val) % \
                                            self.denominator_val if self.denominator_val else 0
        else:
            succ.registers[self.res1_var] = z3.If(self.denominator_val == 0, z3.BitVecVal(0, 256),
                                                  z3.URem((self.arg1_val * self.arg2_val), self.denominator_val))

        succ.set_next_pc()
        return [succ]


class TAC_Exp(TAC_Statement):
    __internal_name__ = "EXP"
    __aliases__ = {'base_var': 'arg1_var', 'base_val': 'arg1_val', 'exp_var': 'arg2_var', 'exp_val': 'arg2_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.base_val) and concrete(self.exp_val):
            succ.registers[self.res1_var] = pow(self.base_val, self.exp_val, utils.TT256)
        else:
            if concrete(self.base_val) and utils.is_pow2(self.base_val):
                l2 = utils.log2(self.base_val)
                succ.registers[self.res1_var] = 1 << (l2 * self.exp_val)
            else:
                raise SymbolicError('exponentiation with symbolic exponent currently not supported :-/')

        succ.set_next_pc()
        return [succ]


class TAC_Signextend(TAC_Statement):
    __internal_name__ = "SIGNEXTEND"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.arg1_val) and concrete(self.arg2_val):
            if self.arg1_val <= 31:
                testbit = self.arg1_val * 8 + 7
                if self.arg2_val & (1 << testbit):
                    succ.registers[self.res1_var] = self.arg2_val | (utils.TT256 - (1 << testbit))
                else:
                    succ.registers[self.res1_var] = self.arg2_val & ((1 << testbit) - 1)
            else:
                succ.registers[self.res1_var] = self.arg2_val
        elif concrete(self.arg1_val):
            if self.arg1_val <= 31:
                oldwidth = (self.arg1_val + 1) * 8
                succ.registers[self.res1_var] = z3.SignExt(256 - oldwidth, self.arg2_val)
            else:
                succ.registers[self.res1_var] = self.arg2_val
        else:
            raise SymbolicError('symbolic bitwidth for signextension is currently not supported')

        succ.set_next_pc()
        return [succ]


class TAC_Lt(TAC_Statement):
    __internal_name__ = "LT"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.arg1_val) and concrete(self.arg2_val):
            succ.registers[self.res1_var] = 1 if self.arg1_val < self.arg2_val else 0
        else:
            succ.registers[self.res1_var] = z3.If(z3.ULT(self.arg1_val, self.arg2_val), z3.BitVecVal(1, 256),
                                                  z3.BitVecVal(0, 256))

        succ.set_next_pc()
        return [succ]


class TAC_Gt(TAC_Statement):
    __internal_name__ = "GT"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.arg1_val) and concrete(self.arg2_val):
            succ.registers[self.res1_var] = 1 if self.arg1_val > self.arg2_val else 0
        else:
            succ.registers[self.res1_var] = z3.If(z3.UGT(self.arg1_val, self.arg2_val), z3.BitVecVal(1, 256),
                                                  z3.BitVecVal(0, 256))

        succ.set_next_pc()
        return [succ]


class TAC_Slt(TAC_Statement):
    __internal_name__ = "SLT"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.arg1_val) and concrete(self.arg2_val):
            self.arg1_val, self.arg2_val = utils.to_signed(self.arg1_val), utils.to_signed(self.arg2_val)
            succ.registers[self.res1_var] = 1 if self.arg1_val < self.arg2_val else 0
        else:
            succ.registers[self.res1_var] = z3.If(self.arg1_val < self.arg2_val, z3.BitVecVal(1, 256),
                                                  z3.BitVecVal(0, 256))

        succ.set_next_pc()
        return [succ]


class TAC_Sgt(TAC_Statement):
    __internal_name__ = "SGT"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.arg1_val) and concrete(self.arg2_val):
            self.arg1_val, self.arg2_val = utils.to_signed(self.arg1_val), utils.to_signed(self.arg2_val)
            succ.registers[self.res1_var] = 1 if self.arg1_val > self.arg2_val else 0
        else:
            succ.registers[self.res1_var] = z3.If(self.arg1_val > self.arg2_val, z3.BitVecVal(1, 256),
                                                  z3.BitVecVal(0, 256))

        succ.set_next_pc()
        return [succ]


class TAC_Eq(TAC_Statement):
    __internal_name__ = "EQ"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.arg1_val) and concrete(self.arg2_val):
            succ.registers[self.res1_var] = 1 if self.arg1_val == self.arg2_val else 0
        else:
            succ.registers[self.res1_var] = z3.If(self.arg1_val == self.arg2_val, z3.BitVecVal(1, 256),
                                                  z3.BitVecVal(0, 256))

        succ.set_next_pc()
        return [succ]


class TAC_Iszero(TAC_Statement):
    __internal_name__ = "ISZERO"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.arg1_val):
            succ.registers[self.res1_var] = 1 if self.arg1_val == 0 else 0
        else:
            succ.registers[self.res1_var] = z3.If(self.arg1_val == 0, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256))

        succ.set_next_pc()
        return [succ]


class TAC_And(TAC_Statement):
    __internal_name__ = "AND"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.registers[self.res1_var] = self.arg1_val & self.arg2_val

        succ.set_next_pc()
        return [succ]


class TAC_Or(TAC_Statement):
    __internal_name__ = "OR"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.registers[self.res1_var] = self.arg1_val | self.arg2_val

        succ.set_next_pc()
        return [succ]


class TAC_Xor(TAC_Statement):
    __internal_name__ = "XOR"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.registers[self.res1_var] = self.arg1_val ^ self.arg2_val

        succ.set_next_pc()
        return [succ]


class TAC_Not(TAC_Statement):
    __internal_name__ = "NOT"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.registers[self.res1_var] = ~self.arg1_val

        succ.set_next_pc()
        return [succ]


class TAC_Byte(TAC_Statement):
    __internal_name__ = "BYTE"
    __aliases__ = {'offset_var': 'arg1_var', 'offset_val': 'arg1_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.offset_val):
            if self.offset_val >= 32:
                succ.registers[self.res1_var] = 0
            else:
                if concrete(self.arg2_val):
                    succ.registers[self.res1_var] = (self.arg2_val // 256 ** (31 - self.offset_val)) % 256
                else:
                    v = z3.simplify(
                        z3.Extract((31 - self.offset_val) * 8 + 7, (31 - self.offset_val) * 8, self.arg2_val))
                    if z3.is_bv_value(v):
                        succ.registers[self.res1_var] = v.as_long()
                    else:
                        succ.registers[self.res1_var] = z3.ZeroExt(256 - 32, v)
        else:
            raise SymbolicError('symbolic byte-index not supported')

        succ.set_next_pc()
        return [succ]


class TAC_Shl(TAC_Statement):
    __internal_name__ = "SHL"
    __aliases__ = {'shift_var': 'arg1_var', 'shift_val': 'arg1_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.registers[self.res1_var] = self.arg2_val << self.shift_val

        succ.set_next_pc()
        return [succ]


class TAC_Shr(TAC_Statement):
    __internal_name__ = "SHR"
    __aliases__ = {'shift_var': 'arg1_var', 'shift_val': 'arg1_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        if concrete(self.arg2_val) and concrete(self.shift_val):
            succ.registers[self.res1_var] = self.arg2_val >> self.shift_val
        else:
            succ.registers[self.res1_var] = z3.LShR(self.arg2_val, self.shift_val)

        succ.set_next_pc()
        return [succ]


class TAC_Sar(TAC_Statement):
    __internal_name__ = "SAR"
    __aliases__ = {'shift_var': 'arg1_var', 'shift_val': 'arg1_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.registers[self.res1_var] = utils.to_signed(self.arg2_val) >> self.shift_val

        succ.set_next_pc()
        return [succ]
