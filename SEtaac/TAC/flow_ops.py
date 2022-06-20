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

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        target_bb_id = hex(self.destination_val)
        curr_bb_id = succ.curr_stmt.block_ident
        curr_bb = succ.project.factory.block(curr_bb_id)
        target_bb = succ.project.factory.block(target_bb_id + curr_bb.function.id)

        if not target_bb:
            target_bb = succ.project.factory.block(target_bb_id)

        dest = target_bb.first_ins.stmt_ident

        succ.pc = dest

        return [succ]


class TAC_Jumpi(TAC_Statement):
    __internal_name__ = "JUMPI"
    __aliases__ = {'destination_var': 'arg1_var', 'destination_val': 'arg1_val',
                   'condition_var': 'arg2_var', 'condition_val': 'arg2_val'}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        target_bb_id = hex(self.destination_val)
        curr_bb_id = succ.curr_stmt.block_ident
        curr_bb = succ.project.factory.block(curr_bb_id)
        target_bb = succ.project.factory.block(target_bb_id + curr_bb.function.id)

        if not target_bb:
            target_bb = succ.project.factory.block(target_bb_id)

        dest = target_bb.first_ins.stmt_ident
        cond = self.condition_val

        if concrete(cond):
            # if the jump condition is concrete, use it to determine the jump target
            if cond:
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
        'gas_var': 'arg1_var', 'gas_val': 'arg1_val',
        'address_var': 'arg2_var', 'address_val': 'arg2_val',
        'value_var': 'arg3_var', 'value_val': 'arg3_val',
        'argsOffset_var': 'arg4_var', 'argsOffset_val': 'arg4_val',
        'argsSize_var': 'arg5_var', 'argsSize_val': 'arg5_val',
        'retOffset_var': 'arg6_var', 'retOffset_val': 'arg6_val',
        'retSize_var': 'arg7_var', 'retSize_val': 'arg7_val',
        'success_var': 'res_var', 'success_val': 'res_val'
    }

    def _handle(self, succ, gas_val=None, address_val=None, value_val=None, argsOffset_val=None, argsSize_val=None,
                retOffset_val=None, retSize_val=None):
        gas_val = gas_val or self.gas_val
        address_val = address_val or self.address_val
        value_val = value_val or self.value_val
        argsOffset_val = argsOffset_val or self.argsOffset_val
        argsSize_val = argsSize_val or self.argsSize_val
        retOffset_val = retOffset_val or self.retOffset_val
        retSize_val = retSize_val or self.retSize_val

        ostart = retOffset_val if concrete(retOffset_val) else z3.simplify(retOffset_val)
        olen = retSize_val if concrete(retSize_val) else z3.simplify(retSize_val)

        if concrete(address_val) and address_val <= 8:
            if address_val == 4:
                logging.info("Calling precompiled identity contract")
                istart = argsOffset_val if concrete(argsOffset_val) else z3.simplify(argsOffset_val)
                ilen = argsSize_val if concrete(argsSize_val) else z3.simplify(argsSize_val)
                succ.memory.copy_return_data(istart, ilen, ostart, olen)
                succ.registers[self.res1_var] = 1
            else:
                raise SymbolicError("Precompiled contract %d not implemented" % address_val)
        else:
            for i in range(olen):
                succ.memory[ostart + i] = z3.BitVec('EXT_%d_%d_%d' % (succ.instruction_count, i, succ.xid), 8)
            logging.info("Calling contract %s (%d_%d)" % (address_val, succ.instruction_count, succ.xid))
            succ.registers[self.res1_var] = z3.BitVec('CALLRESULT_%d_%d' % (succ.instruction_count, succ.xid), 256)

        succ.set_next_pc()
        return [succ]


class TAC_Call(TAC_BaseCall):
    __internal_name__ = "CALL"

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state
        value_val = succ.registers[self.value_val]

        succ.constraints.append(z3.UGE(succ.balance, value_val))
        succ.balance -= value_val

        return self._handle(succ, value_val=value_val)


class TAC_Callcode(TAC_BaseCall):
    __internal_name__ = "CALLCODE"

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state
        return self._handle(succ)


class TAC_Delegatecall(TAC_BaseCall):
    __internal_name__ = "DELEGATECALL"

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state
        value_val = utils.ctx_or_symbolic('CALLVALUE', succ.ctx, succ.xid)

        return self._handle(succ, value_val=value_val)


class TAC_Staticcall(TAC_BaseCall):
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

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state
        value_val = 0

        return self._handle(succ, value_val=value_val)
