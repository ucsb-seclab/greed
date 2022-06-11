
import logging

import z3

from SEtaac import utils
from SEtaac.exceptions import SymbolicError
from SEtaac.utils import concrete, is_true, get_solver
from .base import TAC_Septenary, TAC_Senary, TAC_UnaryNoRes, TAC_BinaryNoRes
from ..state import SymbolicEVMState

__all__ = ['TAC_Jump', 'TAC_Jumpi', 'TAC_Call', 'TAC_Callcode', 'TAC_Return', 
           'TAC_Delegatecall', 'TAC_Staticcall', ]

class TAC_Jump(TAC_UnaryNoRes):
    __internal_name__ = "JUMP"
    __aliases__ = {'destination_var': 'op1_var', 'destination_val': 'op1_val'}

    def handle(self, state:SymbolicEVMState):
        # TODO: implement symbolic jump destination
        succ = state.copy()
        dest = succ.registers[self.destination_var]
        if not concrete(dest):
            raise SymbolicError('Symbolic jump target')
        succ.pc = dest

        return [succ]

class TAC_Jumpi(TAC_BinaryNoRes):
    __internal_name__ = "JUMPI"
    __aliases__ = {'destination_var': 'op1_var', 'destination_val': 'op1_val', 
                   'condition_var': 'op2_var', 'condition_val': 'op2_val'}

    def handler(self, state:SymbolicEVMState):
        # TODO: implement symbolic jumpi destination
        succ = state.copy()
        dest = succ.registers[self.destination]
        cond = succ.registers[self.condition]

        if concrete(cond):
            # if the jump condition is concrete, use it to determine the jump target
            if cond is True:
                if not concrete(dest):
                    raise SymbolicError('Symbolic jump target')
                succ.pc = dest
                return [succ]
            else:
                succ.set_next_pc()
                return [succ]
        else:
            # TODO: fix get_solver
            # let's check if both branches are sat
            s = get_solver()
            s.add(succ.constraints)
            sat_true = is_true(cond == 1, s)
            sat_false = is_true(cond == 0, s)

            if sat_true and sat_false:
                # actually fork here
                succ_true = succ.copy()
                succ_false = succ

                succ_true.pc = dest
                succ_true.constraints.append(cond == 1)

                succ_false.set_next_pc()
                succ_false.constraints.append(cond == 0)

                return [succ_true, succ_false]
            elif sat_true:
                # if only the true branch is sat, jump
                if not concrete(dest):
                    raise SymbolicError('Symbolic jump target')
                succ.pc = dest
                succ.constraints.append(cond == 1)

                return [succ]
            elif sat_false:
                # if only the false branch is sat, step to the fallthrough branch
                succ.set_next_pc()
                succ.constraints.append(cond == 0)

                return [succ]
            else:
                # nothing is sat
                return []

class TAC_BaseCall(TAC_Septenary):
    __internal_name__ = "_CALL"
    __aliases__ = {
                   'gas_var'       : 'op1_var', 'gas_val'       : 'op1_val',
                   'address_var'   : 'op2_var', 'address_val'   : 'op2_val',
                   'value_var'     : 'op3_var', 'value_val'     : 'op3_val',
                   'argsOffset_var': 'op4_var', 'argsOffset_val': 'op4_val',
                   'argsSize_var'  : 'op5_var', 'argsSize_val'  : 'op5_val',
                   'retOffset_var' : 'op6_var', 'retOffset_val' : 'op6_val',
                   'retSize_var'   : 'op7_var', 'retSize_val'   : 'op7_val',
                   'success_var'   : 'res_var', 'success_val'   : 'res_val'
                   }

    def _handler(self, succ, arg1=None, arg2=None, arg3=None, arg4=None, arg5=None, arg6=None, arg7=None):
        arg1 = arg1 or succ.registers[self.op1_var]
        arg2 = arg2 or succ.registers[self.op2_var]
        arg3 = arg3 or succ.registers[self.op3_var]
        arg4 = arg4 or succ.registers[self.op4_var]
        arg5 = arg5 or succ.registers[self.op5_var]
        arg6 = arg6 or succ.registers[self.op6_var]
        arg7 = arg7 or succ.registers[self.op7_var]

        ostart = arg6 if concrete(arg6) else z3.simplify(arg6)
        olen = arg7 if concrete(arg7) else z3.simplify(arg7)

        if concrete(arg2) and arg2 <= 8:
            if arg2 == 4:
                logging.info("Calling precompiled identity contract")
                istart = arg4 if concrete(arg4) else z3.simplify(arg4)
                ilen = arg5 if concrete(arg5) else z3.simplify(arg5)
                succ.memory.copy(istart, ilen, ostart, olen)
                succ.registers[self.res_var] = 1
            else:
                raise SymbolicError("Precompiled contract %d not implemented" % arg2)
        else:
            for i in range(olen):
                succ.memory[ostart + i] = z3.BitVec('EXT_%d_%d_%d' % (succ.instruction_count, i, succ.xid), 8)
            logging.info("Calling contract %s (%d_%d)" % (arg2, succ.instruction_count, succ.xid))
            succ.registers[self.res_var] = z3.BitVec('CALLRESULT_%d_%d' % (succ.instruction_count, succ.xid), 256)

        succ.set_next_pc()
        return [succ]

class TAC_Call(TAC_BaseCall):
    __internal_name__ = "CALL"

    def handler(self, state:SymbolicEVMState):
        succ = state.copy()
        arg3 = succ.registers[self.op3_var]

        succ.constraints.append(z3.UGE(succ.balance, arg3))
        succ.balance -= arg3

        return self._handler(succ, arg3=arg3)

class TAC_Callcode(TAC_BaseCall):
    __internal_name__ = "CALLCODE"

    def handler(self, state:SymbolicEVMState):
        succ = state.copy()
        return self._handler(succ)

class TAC_Delegatecall(TAC_BaseCall):
    __internal_name__ = "DELEGATECALL"

    def handler(self, state:SymbolicEVMState):
        succ = state.copy()
        arg3 = utils.ctx_or_symbolic('CALLVALUE', succ.ctx, succ.xid)

        return self._handler(succ, arg3=arg3)

class TAC_Staticcall(TAC_BaseCall):
    __internal_name__ = "STATICCALL"

    def handler(self, state:SymbolicEVMState):
        succ = state.copy()
        arg3 = 0

        return self._handler(succ, arg3=arg3)

class TAC_Return(TAC_BinaryNoRes):
    __internal_name__ = "RETURN"
    __aliases__ = {
                   'offset_var'    : 'op1_var', 'offset_val'    : 'op1_val', 
                   'size_var'      : 'op2_var', 'size_val'      : 'op2_val',
                   }
    def handler(self, state:SymbolicEVMState):
        succ = state.copy()
        arg1 = succ.registers[self.op1_var]
        arg2 = succ.registers[self.op2_var]

        if concrete(arg1) and concrete(arg2):
            succ.memory.extend(arg1, arg2)
        succ.constraints.append(z3.Or(*(z3.ULE(succ.calldatasize, access) for access in succ.calldata_accesses)))
        succ.halt = True

        succ.set_next_pc()
        return [succ]