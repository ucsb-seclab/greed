import logging

from SEtaac import utils
from SEtaac.utils.exceptions import VMSymbolicError
from SEtaac.utils import concrete, is_sat, get_solver
from .base import TAC_Statement
from ..state import SymbolicEVMState

__all__ = ['TAC_Jump', 'TAC_Jumpi', 'TAC_Call', 'TAC_Callcode',
           'TAC_Delegatecall', 'TAC_Staticcall', ]

log = logging.getLogger(__name__)


class TAC_Jump(TAC_Statement):
    __internal_name__ = "JUMP"
    __aliases__ = {'destination_var': 'arg1_var', 'destination_val': 'arg1_val'}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        target_bb_id = hex(self.destination_val)
        curr_bb_id = succ.curr_stmt.block_id
        curr_bb = succ.project.factory.block(curr_bb_id)
        target_bb = succ.project.factory.block(target_bb_id + curr_bb.function.id)

        if not target_bb:
            target_bb = succ.project.factory.block(target_bb_id)

        dest = target_bb.first_ins.id

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
        curr_bb_id = succ.curr_stmt.block_id
        curr_bb = succ.project.factory.block(curr_bb_id)
        target_bb = succ.project.factory.block(target_bb_id + curr_bb.function.id)

        if not target_bb:
            target_bb = succ.project.factory.block(target_bb_id)

        dest = target_bb.first_ins.id
        cond = self.condition_val

        if concrete(cond):
            # if the jump condition is concrete, use it to determine the jump target
            if cond != 0:
                succ.pc = dest
                return [succ]
            else:
                succ.set_next_pc()
                return [succ]
        else:
            # let's check if both branches are sat
            s = get_solver()
            s.add(succ.constraints)
            sat_true = is_sat(cond != 0, s)
            sat_false = is_sat(cond == 0, s)

            if sat_true and sat_false:
                # actually fork here
                succ_true = succ.copy()
                succ_false = succ

                succ_true.pc = dest
                succ_true.constraints.append(cond != 0)

                succ_false.set_next_pc()
                succ_false.constraints.append(cond == 0)

                return [succ_true, succ_false]
            elif sat_true:
                # if only the true branch is sat, jump
                succ.pc = dest
                succ.constraints.append(cond != 0)

                return [succ]
            elif sat_false:
                # if only the false branch is sat, step to the fallthrough branch
                succ.set_next_pc()
                succ.constraints.append(cond == 0)

                return [succ]
            else:
                # nothing is sat
                log.debug(f"Unsat branch ({succ})")
                succ.halt = True
                return [succ]


class TAC_BaseCall(TAC_Statement):
    __internal_name__ = "_CALL"

    def _handle(self, succ: SymbolicEVMState, gas_val=None, address_val=None, value_val=None,
                argsOffset_val=None, argsSize_val=None, retOffset_val=None, retSize_val=None):
        gas_val = gas_val if gas_val is not None else self.gas_val
        address_val = address_val if address_val is not None else self.address_val
        value_val = value_val if value_val is not None else self.value_val
        argsOffset_val = argsOffset_val if argsOffset_val is not None else self.argsOffset_val
        argsSize_val = argsSize_val if argsSize_val is not None else self.argsSize_val
        retOffset_val = retOffset_val if retOffset_val is not None else self.retOffset_val
        retSize_val = retSize_val if retSize_val is not None else self.retSize_val

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
                raise VMSymbolicError("Precompiled contract %d not implemented" % address_val)
        else:
            for i in range(olen):
                succ.memory[ostart + i] = z3.BitVec('EXT_%d_%d_%d' % (succ.instruction_count, i, succ.xid), 8)
            log_address_val = address_val if concrete(address_val) else "<SYMBOLIC>"
            logging.info("Calling contract %s (%d_%d)" % (log_address_val, succ.instruction_count, succ.xid))
            succ.registers[self.res1_var] = z3.BitVec('CALLRESULT_%d_%d' % (succ.instruction_count, succ.xid), 256)

        succ.set_next_pc()
        return [succ]


class TAC_Call(TAC_BaseCall):
    __internal_name__ = "CALL"
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

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.constraints.append(z3.UGE(succ.balance, self.value_val))
        succ.balance -= self.value_val

        return self._handle(succ, value_val=self.value_val)


class TAC_Callcode(TAC_BaseCall):
    __internal_name__ = "CALLCODE"
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

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state
        return self._handle(succ)


class TAC_Delegatecall(TAC_BaseCall):
    __internal_name__ = "DELEGATECALL"
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
