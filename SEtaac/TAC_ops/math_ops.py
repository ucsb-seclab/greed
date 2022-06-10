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

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        succ.registers[self.res_var] = arg1 + arg2

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Sub(TAC_Binary):
    __internal_name__ = "SUB"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        succ.registers[self.res_var] = arg1 - arg2

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Mul(TAC_Binary):
    __internal_name__ = "MUL"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        succ.registers[self.res_var] = arg1 * arg2

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Div(TAC_Binary):
    __internal_name__ = "DIV"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        if concrete(arg2):
            succ.registers[self.res_var] = 0 if arg2 == 0 else arg1 / arg2 if concrete(arg1) else z3.UDiv(arg1, arg2)
        else:
            succ.registers[self.res_var] = z3.If(arg2 == 0, z3.BitVecVal(0, 256), z3.UDiv(arg1, arg2))

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Sdiv(TAC_Binary):
    __internal_name__ = "SDIV"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        if concrete(arg1) and concrete(arg2):
            arg1, arg2 = utils.to_signed(arg1), utils.to_signed(arg2)
            succ.registers[self.res_var] = 0 if arg2 == 0 else abs(arg1) // abs(arg2) * (-1 if arg1 * arg2 < 0 else 1)
        elif concrete(arg2):
            succ.registers[self.res_var] = 0 if arg2 == 0 else arg1 / arg2
        else:
            succ.registers[self.res_var] = z3.If(arg2 == 0, z3.BitVecVal(0, 256), arg1 / arg2)

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Mod(TAC_Binary):
    __internal_name__ = "MOD"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        if concrete(arg2):
            succ.registers[self.res_var] = 0 if arg2 == 0 else arg1 % arg2
        else:
            succ.registers[self.res_var] = z3.If(arg2 == 0, z3.BitVecVal(0, 256), z3.URem(arg1, arg2))

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Smod(TAC_Binary):
    __internal_name__ = "SMOD"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        if concrete(arg1) and concrete(arg2):
            arg1, args2 = utils.to_signed(arg1), utils.to_signed(arg2)
            succ.registers[self.res_var] = 0 if args2 == 0 else abs(arg1) % abs(args2) * (-1 if arg1 < 0 else 1)
        elif concrete(arg2):
            succ.registers[self.res_var] = 0 if arg2 == 0 else z3.SRem(arg1, arg2)
        else:
            succ.registers[self.res_var] = z3.If(arg2 == 0, z3.BitVecVal(0, 256), z3.SRem(arg1, arg2))

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Addmod(TAC_Ternary):
    __internal_name__ = "ADDMOD"
    __aliases__ = {'denominator_var': 'op3_var', 'denominator_val': 'op3_val'}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]
        arg3 = succ.registers[self.op3_var]

        if concrete(arg3):
            succ.registers[self.res_var] = (arg1 + arg2) % arg3 if arg3 else 0
        else:
            succ.registers[self.res_var] = z3.If(arg3 == 0, z3.BitVecVal(0, 256), z3.URem((arg1 + arg2), arg3))

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Mulmod(TAC_Ternary):
    __internal_name__ = "MULMOD"
    __aliases__ = {'denominator_var': 'op3_var', 'denominator_val': 'op3_val'}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]
        arg3 = succ.registers[self.op3_var]

        if concrete(arg3):
            succ.registers[self.res_var] = (arg1 * arg2) % arg3 if arg3 else 0
        else:
            succ.registers[self.res_var] = z3.If(arg3 == 0, z3.BitVecVal(0, 256), z3.URem((arg1 * arg2), arg3))

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Exp(TAC_Binary):
    __internal_name__ = "EXP"
    __aliases__ = {'base_var': 'op1_var', 'base_val': 'op1_val', 'exp_var': 'op2_var', 'exp_val': 'op2_val'}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        base = succ.registers[self.op1_var]
        exponent = succ.registers[self.op2_var]

        if concrete(base) and concrete(exponent):
            succ.registers[self.res_var] = pow(base, exponent, utils.TT256)
        else:
            if concrete(base) and utils.is_pow2(base):
                l2 = utils.log2(base)
                succ.registers[self.res_var] = 1 << (l2 * exponent)
            else:
                raise SymbolicError('exponentiation with symbolic exponent currently not supported :-/')

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Signextend(TAC_Binary):
    __internal_name__ = "SIGNEXTEND"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        if concrete(arg1) and concrete(arg2):
            if arg1 <= 31:
                testbit = arg1 * 8 + 7
                if arg2 & (1 << testbit):
                    succ.registers[self.res_var] = arg2 | (utils.TT256 - (1 << testbit))
                else:
                    succ.registers[self.res_var] = arg2 & ((1 << testbit) - 1)
            else:
                succ.registers[self.res_var] = arg2
        elif concrete(arg1):
            if arg1 <= 31:
                oldwidth = (arg1 + 1) * 8
                succ.registers[self.res_var] = z3.SignExt(256 - oldwidth, arg2)
            else:
                succ.registers[self.res_var] = arg2
        else:
            raise SymbolicError('symbolic bitwidth for signextension is currently not supported')

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Lt(TAC_Binary):
    __internal_name__ = "LT"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        if concrete(arg1) and concrete(arg2):
            succ.registers[self.res_var] = 1 if arg1 < arg2 else 0
        else:
            succ.registers[self.res_var] = z3.If(z3.ULT(arg1, arg2), z3.BitVecVal(1, 256), z3.BitVecVal(0, 256))

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Gt(TAC_Binary):
    __internal_name__ = "GT"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        if concrete(arg1) and concrete(arg2):
            succ.registers[self.res_var] = 1 if arg1 > arg2 else 0
        else:
            succ.registers[self.res_var] = z3.If(z3.UGT(arg1, arg2), z3.BitVecVal(1, 256), z3.BitVecVal(0, 256))

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Slt(TAC_Binary):
    __internal_name__ = "SLT"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        if concrete(arg1) and concrete(arg2):
            arg1, arg2 = utils.to_signed(arg1), utils.to_signed(arg2)
            succ.registers[self.res_var] = 1 if arg1 < arg2 else 0
        else:
            succ.registers[self.res_var] = z3.If(arg1 < arg2, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256))

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Sgt(TAC_Binary):
    __internal_name__ = "SGT"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        if concrete(arg1) and concrete(arg2):
            arg1, arg2 = utils.to_signed(arg1), utils.to_signed(arg2)
            succ.registers[self.res_var] = 1 if arg1 > arg2 else 0
        else:
            succ.registers[self.res_var] = z3.If(arg1 > arg2, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256))

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Eq(TAC_Binary):
    __internal_name__ = "EQ"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        if concrete(arg1) and concrete(arg2):
            succ.registers[self.res_var] = 1 if arg1 == arg2 else 0
        else:
            succ.registers[self.res_var] = z3.If(arg1 == arg2, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256))

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Iszero(TAC_Unary):
    __internal_name__ = "ISZERO"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]

        if concrete(arg1):
            succ.registers[self.res_var] = 1 if arg1 == 0 else 0
        else:
            succ.registers[self.res_var] = z3.If(arg1 == 0, z3.BitVecVal(1, 256), z3.BitVecVal(0, 256))

        succ.pc = succ.next_statement()
        return [succ]


class TAC_And(TAC_Binary):
    __internal_name__ = "AND"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        succ.registers[self.res_var] = arg1 & arg2

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Or(TAC_Binary):
    __internal_name__ = "OR"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        succ.registers[self.res_var] = arg1 | arg2

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Xor(TAC_Binary):
    __internal_name__ = "XOR"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        succ.registers[self.res_var] = arg1 ^ arg2

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Not(TAC_Unary):
    __internal_name__ = "NOT"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]

        succ.registers[self.res_var] = ~arg1

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Byte(TAC_Binary):
    __internal_name__ = "BYTE"
    __aliases__ = {'offset_var': 'op1_var', 'offset_val': 'op1_val'}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        if concrete(arg1):
            if arg1 >= 32:
                succ.registers[self.res_var] = 0
            else:
                if concrete(arg2):
                    succ.registers[self.res_var] = (arg2 // 256 ** (31 - arg1)) % 256
                else:
                    v = z3.simplify(z3.Extract((31 - arg1) * 8 + 7, (31 - arg1) * 8, arg2))
                    if z3.is_bv_value(v):
                        succ.registers[self.res_var] = v.as_long()
                    else:
                        succ.registers[self.res_var] = z3.ZeroExt(256 - 32, v)
        else:
            raise SymbolicError('symbolic byte-index not supported')

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Shl(TAC_Binary):
    __internal_name__ = "SHL"
    __aliases__ = {'shift_var': 'op1_var', 'shift_val': 'op1_val'}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        succ.registers[self.res_var] = arg2 << arg1

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Shr(TAC_Binary):
    __internal_name__ = "SHR"
    __aliases__ = {'shift_var': 'op1_var', 'shift_val': 'op1_val'}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        if concrete(arg2) and concrete(arg1):
            succ.registers[self.res_var] = arg2 >> arg1
        else:
            succ.registers[self.res_var] = z3.LShR(arg2, arg1)

        succ.pc = succ.next_statement()
        return [succ]


class TAC_Sar(TAC_Binary):
    __internal_name__ = "SAR"
    __aliases__ = {'shift_var': 'op1_var', 'shift_val': 'op1_val'}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        succ.registers[self.res_var] = utils.to_signed(arg2) >> arg1

        succ.pc = succ.next_statement()
        return [succ]
