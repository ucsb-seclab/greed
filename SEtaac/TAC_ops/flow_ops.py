
import logging

import z3

from SEtaac import utils
from SEtaac.exceptions import SymbolicError
from SEtaac.utils import concrete, is_sat, get_solver
from .base import TAC_Statement
from ..state import SymbolicEVMState

__all__ = ['TAC_Jump', 'TAC_Jumpi', 'TAC_Call', 'TAC_Callcode',
           'TAC_Delegatecall', 'TAC_Staticcall', ]

class TAC_Jump(TAC_Statement):
    __internal_name__ = "JUMP"
    __aliases__ = {'destination_var': 'arg1_var', 'destination_val': 'arg1_val'}

    def handle(self, state:SymbolicEVMState):
        self.set_arg_val(state)
        succ = state.copy()

        target_bb_id = hex(self.destination_val)
        curr_bb_id = state.curr_stmt.block_ident
        curr_bb = state.project.factory.block(curr_bb_id)
        target_bb = state.project.factory.block(target_bb_id + curr_bb.function.id)

        if not target_bb:
            target_bb = state.project.factory.block(target_bb_id)

        dest = target_bb.first_ins.stmt_ident

        succ.pc = dest

        return [succ]

class TAC_Jumpi(TAC_Statement):
    __internal_name__ = "JUMPI"
    __aliases__ = {'destination_var': 'arg1_var', 'destination_val': 'arg1_val', 
                   'condition_var': 'arg2_var', 'condition_val': 'arg2_val'}

    def handle(self, state:SymbolicEVMState):
        # TODO: implement symbolic jumpi destination
        self.set_arg_val(state)
        succ = state.copy()

        target_bb_id = hex(self.destination_val)
        curr_bb_id = state.curr_stmt.block_ident
        curr_bb = state.project.factory.block(curr_bb_id)
        target_bb = state.project.factory.block(target_bb_id + curr_bb.function.id)

        if not target_bb:
            target_bb = state.project.factory.block(target_bb_id)

        dest = target_bb.first_ins.stmt_ident
        cond = self.condition_val


        if concrete(cond):
            # if the jump condition is concrete, use it to determine the jump target
            if cond is True:
                # if not concrete(dest):
                #     raise SymbolicError('Symbolic jump target')
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
            sat_true = is_sat(cond == 1, s)
            sat_false = is_sat(cond == 0, s)

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
                # if not concrete(dest):
                #     raise SymbolicError('Symbolic jump target')
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

class TAC_BaseCall(TAC_Statement):
    __internal_name__ = "_CALL"
    __aliases__ = {
                   'gas_var'       : 'arg1_var', 'gas_val'       : 'arg1_val',
                   'address_var'   : 'arg2_var', 'address_val'   : 'arg2_val',
                   'value_var'     : 'arg3_var', 'value_val'     : 'arg3_val',
                   'argsOffset_var': 'arg4_var', 'argsOffset_val': 'arg4_val',
                   'argsSize_var'  : 'arg5_var', 'argsSize_val'  : 'arg5_val',
                   'retOffset_var' : 'arg6_var', 'retOffset_val' : 'arg6_val',
                   'retSize_var'   : 'arg7_var', 'retSize_val'   : 'arg7_val',
                   'success_var'   : 'res_var', 'success_val'   : 'res_val'
                   }

    def _handle(self, succ, arg1=None, arg2=None, arg3=None, arg4=None, arg5=None, arg6=None, arg7=None):
        arg1 = arg1 or succ.registers[self.arg1_var]
        arg2 = arg2 or succ.registers[self.arg2_var]
        arg3 = arg3 or succ.registers[self.arg3_var]
        arg4 = arg4 or succ.registers[self.arg4_var]
        arg5 = arg5 or succ.registers[self.arg5_var]
        arg6 = arg6 or succ.registers[self.arg6_var]
        arg7 = arg7 or succ.registers[self.arg7_var]

        ostart = arg6 if concrete(arg6) else z3.simplify(arg6)
        olen = arg7 if concrete(arg7) else z3.simplify(arg7)

        if concrete(arg2) and arg2 <= 8:
            if arg2 == 4:
                logging.info("Calling precompiled identity contract")
                istart = arg4 if concrete(arg4) else z3.simplify(arg4)
                ilen = arg5 if concrete(arg5) else z3.simplify(arg5)
                succ.memory.copy_return_data(istart, ilen, ostart, olen)
                succ.registers[self.res1_var] = 1
            else:
                raise SymbolicError("Precompiled contract %d not implemented" % arg2)
        else:
            for i in range(olen):
                succ.memory[ostart + i] = z3.BitVec('EXT_%d_%d_%d' % (succ.instruction_count, i, succ.xid), 8)
            logging.info("Calling contract %s (%d_%d)" % (arg2, succ.instruction_count, succ.xid))
            succ.registers[self.res1_var] = z3.BitVec('CALLRESULT_%d_%d' % (succ.instruction_count, succ.xid), 256)

        succ.set_next_pc()
        return [succ]

class TAC_Call(TAC_BaseCall):
    __internal_name__ = "CALL"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg3 = succ.registers[self.arg3_var]

        succ.constraints.append(z3.UGE(succ.balance, arg3))
        succ.balance -= arg3

        return self._handle(succ, arg3=arg3)

class TAC_Callcode(TAC_BaseCall):
    __internal_name__ = "CALLCODE"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        return self._handle(succ)

class TAC_Delegatecall(TAC_BaseCall):
    __internal_name__ = "DELEGATECALL"

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg3 = utils.ctx_or_symbolic('CALLVALUE', succ.ctx, succ.xid)

        return self._handle(succ, arg3=arg3)

class TAC_Staticcall(TAC_Statement):
    __internal_name__ = "STATICCALL"
    __aliases__ = {
        'gas_var': 'arg1_var', 'gas_val': 'arg1_val',
        'address_var': 'arg2_var', 'address_val': 'arg2_val',
        'argsOffset_var': 'arg3_var', 'argsOffset_val': 'arg3_val',
        'argsSize_var': 'arg4_var', 'argsSize_val': 'arg4_val',
        'retOffset_var': 'arg5_var', 'retOffset_val': 'arg5_val',
        'retSize_var': 'arg6_var', 'retSize_val': 'arg6_val',
        'success_var': 'res_var', 'success_val': 'res_val'
    }

    def _handle(self, succ, arg1=None, arg2=None, arg3=None, arg4=None, arg5=None, arg6=None, arg7=None):
        arg1 = arg1 or succ.registers[self.arg1_var]
        arg2 = arg2 or succ.registers[self.arg2_var]
        arg3 = 0 # it sucks but opcodes are shifted here
        arg4 = arg4 or succ.registers[self.arg3_var]
        arg5 = arg5 or succ.registers[self.arg4_var]
        arg6 = arg6 or succ.registers[self.arg5_var]
        arg7 = arg7 or succ.registers[self.arg6_var]

        ostart = arg6 if concrete(arg6) else z3.simplify(arg6)
        olen = arg7 if concrete(arg7) else z3.simplify(arg7)

        if concrete(arg2) and arg2 <= 8:
            if arg2 == 4:
                logging.info("Calling precompiled identity contract")
                istart = arg4 if concrete(arg4) else z3.simplify(arg4)
                ilen = arg5 if concrete(arg5) else z3.simplify(arg5)
                succ.memory.copy_return_data(istart, ilen, ostart, olen)
                succ.registers[self.res1_var] = 1
            else:
                raise SymbolicError("Precompiled contract %d not implemented" % arg2)
        else:
            for i in range(olen):
                succ.memory[ostart + i] = z3.BitVec('EXT_%d_%d_%d' % (succ.instruction_count, i, succ.xid), 8)
            logging.info("Calling contract %s (%d_%d)" % (arg2, succ.instruction_count, succ.xid))
            succ.registers[self.res1_var] = z3.BitVec('CALLRESULT_%d_%d' % (succ.instruction_count, succ.xid), 256)

        succ.set_next_pc()
        return [succ]

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        arg3 = 0

        return self._handle(succ, arg3=arg3)
