from greed.TAC.base import TAC_Statement
from greed.solver.shortcuts import *
from greed.state import SymbolicEVMState
from greed.utils.exceptions import VMSymbolicError
from greed.utils.extra import is_pow2, log2
from greed import options

__all__ = [
    'TAC_Add', 'TAC_Sub', 'TAC_Mul', 'TAC_Div', 'TAC_Sdiv', 'TAC_Mod', 'TAC_Smod', 'TAC_Addmod', 'TAC_Mulmod',
    'TAC_Exp', 'TAC_Signextend', 'TAC_Lt', 'TAC_Gt', 'TAC_Slt', 'TAC_Sgt', 'TAC_Eq', 'TAC_Iszero', 'TAC_And',
    'TAC_Or', 'TAC_Xor', 'TAC_Not', 'TAC_Byte', 'TAC_Shl', 'TAC_Shr', 'TAC_Sar'
]


"""
This module contains the TAC statements that are related to the mathematical operations of the EVM.
"""

class TAC_Add(TAC_Statement):
    __internal_name__ = "ADD"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = BV_Add(self.arg1_val, self.arg2_val)

        state.set_next_pc()
        return [state]


class TAC_Sub(TAC_Statement):
    __internal_name__ = "SUB"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = BV_Sub(self.arg1_val, self.arg2_val)

        state.set_next_pc()
        return [state]


class TAC_Mul(TAC_Statement):
    __internal_name__ = "MUL"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = BV_Mul(self.arg1_val, self.arg2_val)

        state.set_next_pc()
        return [state]


class TAC_Div(TAC_Statement):
    __internal_name__ = "DIV"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = If(Equal(self.arg2_val, BVV(0, 256)),
                                            BVV(0, 256),
                                            BV_UDiv(self.arg1_val, self.arg2_val))

        state.set_next_pc()
        return [state]


class TAC_Sdiv(TAC_Statement):
    __internal_name__ = "SDIV"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = If(Equal(self.arg2_val, BVV(0, 256)),
                                            BVV(0, 256),
                                            BV_SDiv(self.arg1_val, self.arg2_val))

        state.set_next_pc()
        return [state]


class TAC_Mod(TAC_Statement):
    __internal_name__ = "MOD"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = If(Equal(self.arg2_val, BVV(0, 256)),
                                            BVV(0, 256),
                                            BV_URem(self.arg1_val, self.arg2_val))

        state.set_next_pc()
        return [state]


class TAC_Smod(TAC_Statement):
    __internal_name__ = "SMOD"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = If(Equal(self.arg2_val, BVV(0, 256)),
                                            BVV(0, 256),
                                            BV_SRem(self.arg1_val, self.arg2_val))

        state.set_next_pc()
        return [state]


class TAC_Addmod(TAC_Statement):
    __internal_name__ = "ADDMOD"
    __aliases__ = {'denominator_var': 'arg3_var', 'denominator_val': 'arg3_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        # todo: might be over complicated
        sext_arg1_val = BV_Zero_Extend(self.arg1_val, 256)
        sext_arg2_val = BV_Zero_Extend(self.arg2_val, 256)
        sext_arg3_val = BV_Zero_Extend(self.arg3_val, 256)
        sext_add_res = BV_Add(sext_arg1_val, sext_arg2_val)
        
        sext_mod_res = BV_URem(sext_add_res, sext_arg3_val)
        mod_res = BV_Extract(0, 255, sext_mod_res)
        
        state.registers[self.res1_var] = If(Equal(self.denominator_val, BVV(0, 256)),
                                            BVV(0, 256),
                                            mod_res)

        state.set_next_pc()
        return [state]


class TAC_Mulmod(TAC_Statement):
    __internal_name__ = "MULMOD"
    __aliases__ = {'denominator_var': 'arg3_var', 'denominator_val': 'arg3_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        # todo: might be over complicated
        sext_arg1_val = BV_Zero_Extend(self.arg1_val, 256)
        sext_arg2_val = BV_Zero_Extend(self.arg2_val, 256)
        sext_arg3_val = BV_Zero_Extend(self.arg3_val, 256)
        sext_mul_res = BV_Mul(sext_arg1_val, sext_arg2_val)
        sext_mod_res = BV_URem(sext_mul_res, sext_arg3_val)
        mod_res = BV_Extract(0, 255, sext_mod_res)
        
        state.registers[self.res1_var] = If(Equal(self.denominator_val, BVV(0, 256)),
                                            BVV(0, 256),
                                            mod_res)

        state.set_next_pc()
        return [state]


class TAC_Exp(TAC_Statement):
    __internal_name__ = "EXP"
    __aliases__ = {'base_var': 'arg1_var', 'base_val': 'arg1_val', 'exp_var': 'arg2_var', 'exp_val': 'arg2_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        if is_concrete(self.base_val):
            # Concrete base
            base_concrete_val = bv_unsigned_value(self.base_val)
            if is_concrete(self.exp_val):
                # Concrete base, concrete exponent
                exp_concrete_val = bv_unsigned_value(self.exp_val)
                res = pow(base_concrete_val, exp_concrete_val, 2 ** 256)
                state.registers[self.res1_var] = BVV(res, 256)
            else:
                # Concrete base, symbolic exponent
                if is_pow2(base_concrete_val):
                    # Base is a power of 2, we can do a trick to simplify
                    l2 = log2(base_concrete_val)
                    state.registers[self.res1_var] = BV_Shl(BVV(1,256), BV_Mul(BVV(l2,256), self.exp_val))
                else:
                    # Base is not a power of 2.
                    if options.MATH_CONCRETIZE_SYMBOLIC_EXP_EXP:
                        # Let's grab a solution
                        exp_concrete_val = state.solver.eval(self.exp_val, raw=True)
                        # Add it to the constraints
                        state.add_constraint(Equal(self.exp_val, exp_concrete_val))
                        # Calculate the result
                        res = pow(base_concrete_val, bv_unsigned_value(exp_concrete_val), 2 ** 256)
                        state.registers[self.res1_var] = BVV(res, 256)
                    else:
                        raise VMSymbolicError('Exponentiation with symbolic exponent currently not supported.')
        else:
            # Symbolic base
            if is_concrete(self.exp_val):
                # Symbolic base, concrete exponent
                exp_concrete_val = bv_unsigned_value(self.exp_val)
                if exp_concrete_val == 0:
                    state.registers[self.res1_var] = BVV(1, 256)
                elif exp_concrete_val == 1:
                    state.registers[self.res1_var] = self.base_val
                elif exp_concrete_val < options.MATH_MULTIPLY_EXP_THRESHOLD:
                    # Exponentiation by multiplications
                    res = self.base_val
                    for i in range(1, exp_concrete_val):
                        res = BV_Mul(res, self.base_val)
                    state.registers[self.res1_var] = res
                else:
                    raise VMSymbolicError('Exponentiation with symbolic base currently not supported.')
            else:
                # Symbolic base, symbolic exponent
                if options.MATH_CONCRETIZE_SYMBOLIC_EXP_EXP and options.MATH_CONCRETIZE_SYMBOLIC_EXP_BASE:
                    # Let's grab a solution
                    exp_concrete_val = state.solver.eval(self.exp_val, raw=True)
                    base_concrete_val = state.solver.eval(self.base_val, raw=True)
                    
                    # Add it to the constraints
                    state.add_constraint(Equal(self.exp_val, exp_concrete_val))
                    state.add_constraint(Equal(self.base_val, base_concrete_val))

                    # Calculate the result
                    res = pow(base_concrete_val, exp_concrete_val, 2 ** 256)
                    state.registers[self.res1_var] = BVV(res, 256)
                    
                else:
                    raise VMSymbolicError('Exponentiation with symbolic base and exponent currently not supported.')

        state.set_next_pc()
        return [state]


class TAC_Signextend(TAC_Statement):
    __internal_name__ = "SIGNEXTEND"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        if is_concrete(self.arg1_val):
            if bv_unsigned_value(self.arg1_val) <= 31:
                oldwidth = (bv_unsigned_value(self.arg1_val) + 1) * 8
                truncated = BV_Extract(0, oldwidth-1, self.arg2_val)
                state.registers[self.res1_var] = BV_Sign_Extend(truncated, 256 - oldwidth)
            else:
                state.registers[self.res1_var] = self.arg2_val
        else:
            raise VMSymbolicError('symbolic bitwidth for signextension is currently not supported')

        state.set_next_pc()
        return [state]


class TAC_Lt(TAC_Statement):
    __internal_name__ = "LT"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = If(BV_ULT(self.arg1_val, self.arg2_val),
                                            BVV(1, 256),
                                            BVV(0, 256))

        state.set_next_pc()
        return [state]


class TAC_Gt(TAC_Statement):
    __internal_name__ = "GT"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = If(BV_UGT(self.arg1_val, self.arg2_val),
                                            BVV(1, 256),
                                            BVV(0, 256))

        state.set_next_pc()
        return [state]


class TAC_Slt(TAC_Statement):
    __internal_name__ = "SLT"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = If(BV_SLT(self.arg1_val, self.arg2_val),
                                            BVV(1, 256),
                                            BVV(0, 256))

        state.set_next_pc()
        return [state]


class TAC_Sgt(TAC_Statement):
    __internal_name__ = "SGT"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = If(BV_SGT(self.arg1_val, self.arg2_val),
                                            BVV(1, 256),
                                            BVV(0, 256))

        state.set_next_pc()
        return [state]


class TAC_Eq(TAC_Statement):
    __internal_name__ = "EQ"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = If(Equal(self.arg1_val, self.arg2_val),
                                            BVV(1, 256),
                                            BVV(0, 256))

        state.set_next_pc()
        return [state]


class TAC_Iszero(TAC_Statement):
    __internal_name__ = "ISZERO"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = If(Equal(self.arg1_val, BVV(0, 256)),
                                            BVV(1, 256),
                                            BVV(0, 256))

        state.set_next_pc()
        return [state]


class TAC_And(TAC_Statement):
    __internal_name__ = "AND"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = BV_And(self.arg1_val, self.arg2_val)

        state.set_next_pc()
        return [state]


class TAC_Or(TAC_Statement):
    __internal_name__ = "OR"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = BV_Or(self.arg1_val, self.arg2_val)

        state.set_next_pc()
        return [state]


class TAC_Xor(TAC_Statement):
    __internal_name__ = "XOR"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = BV_Xor(self.arg1_val, self.arg2_val)

        state.set_next_pc()
        return [state]


class TAC_Not(TAC_Statement):
    __internal_name__ = "NOT"

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = BV_Not(self.arg1_val)

        state.set_next_pc()
        return [state]


class TAC_Byte(TAC_Statement):
    __internal_name__ = "BYTE"
    __aliases__ = {'offset_var': 'arg1_var', 'offset_val': 'arg1_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        if is_concrete(self.offset_val):
            if bv_unsigned_value(self.offset_val) >= 32:
                state.registers[self.res1_var] = BVV(0, 256)
            elif is_concrete(self.arg2_val):
                res = bv_unsigned_value(self.arg2_val) // 256 ** (31 - bv_unsigned_value(self.offset_val))
                state.registers[self.res1_var] = BVV(res, 256)
            else:
                start = (31 - bv_unsigned_value(self.offset_val)) * 8
                end = (31 - bv_unsigned_value(self.offset_val)) * 8 + 7
                v = BV_Extract(start, end, self.arg2_val)
                state.registers[self.res1_var] = BV_Zero_Extend(v, 256 - 8)
        else:
            raise VMSymbolicError('symbolic byte-index not supported')

        state.set_next_pc()
        return [state]


class TAC_Shl(TAC_Statement):
    __internal_name__ = "SHL"
    __aliases__ = {'shift_var': 'arg1_var', 'shift_val': 'arg1_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = BV_Shl(self.arg2_val, self.arg1_val)

        state.set_next_pc()
        return [state]


class TAC_Shr(TAC_Statement):
    __internal_name__ = "SHR"
    __aliases__ = {'shift_var': 'arg1_var', 'shift_val': 'arg1_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = BV_Shr(self.arg2_val, self.arg1_val)

        state.set_next_pc()
        return [state]


class TAC_Sar(TAC_Statement):
    __internal_name__ = "SAR"
    __aliases__ = {'shift_var': 'arg1_var', 'shift_val': 'arg1_val'}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        state.registers[self.res1_var] = BV_Sar(self.arg2_val, self.arg1_val)

        state.set_next_pc()
        return [state]
