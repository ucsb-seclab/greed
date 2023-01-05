import logging

from SEtaac import options
from SEtaac import utils
from SEtaac.TAC.base import TAC_Statement
from SEtaac.solver.shortcuts import *
from SEtaac.state import SymbolicEVMState
from SEtaac.utils.exceptions import VMSymbolicError

__all__ = ['TAC_Jump', 'TAC_Jumpi', 'TAC_Call', 'TAC_Callcode', 'TAC_Delegatecall', 'TAC_Staticcall', ]

log = logging.getLogger(__name__)


class TAC_Jump(TAC_Statement):
    __internal_name__ = "JUMP"
    __aliases__ = {'destination_var': 'arg1_var', 'destination_val': 'arg1_val'}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        state.pc = state.get_non_fallthrough_pc(self.destination_val)
        return [state]


class TAC_Jumpi(TAC_Statement):
    __internal_name__ = "JUMPI"
    __aliases__ = {'destination_var': 'arg1_var', 'destination_val': 'arg1_val',
                   'condition_var': 'arg2_var', 'condition_val': 'arg2_val'}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        dest = state.get_non_fallthrough_pc(self.destination_val)
        cond = self.condition_val
        
        if is_concrete(cond):
            # if the jump condition is concrete, use it to determine the jump target
            if bv_unsigned_value(cond) != 0:
                state.pc = dest
                return [state]
            else:
                state.set_next_pc()
                return [state]
        else:
            if options.LAZY_SOLVES:
                # just collect the constraints
                sat_true = True
                sat_false = True
            else:
                # let's check if both branches are sat
                sat_true = state.solver.is_formula_sat(NotEqual(cond, BVV(0, 256)))
                sat_false = state.solver.is_formula_sat(Equal(cond, BVV(0, 256)))

            if sat_true and sat_false:
                # actually fork here
                succ_true = state.copy()
                succ_false = state

                succ_true.pc = dest
                succ_true.add_constraint(NotEqual(cond, BVV(0, 256)))

                succ_false.set_next_pc()
                succ_false.add_constraint(Equal(cond, BVV(0, 256)))

                return [succ_true, succ_false]
            elif sat_true:
                # if only the true branch is sat, jump
                state.pc = dest
                state.add_constraint(NotEqual(cond, BVV(0, 256)))
                return [state]
            elif sat_false:
                # if only the false branch is sat, step to the fallthrough branch
                state.set_next_pc()
                state.add_constraint(Equal(cond, BVV(0, 256)))
                return [state]
            else:
                # nothing is sat
                log.fatal(f"JUMPI with UNSAT branches at ({state.pc})")
                state.halt = True
                return [state]


class TAC_BaseCall(TAC_Statement):
    __internal_name__ = "_CALL"

    # Metadata for _CALL statements.
    likely_known_target = None

    def _handle(self, state: SymbolicEVMState, gas_val=None, address_val=None, value_val=None,
                argsOffset_val=None, argsSize_val=None, retOffset_val=None, retSize_val=None,
                ):
        gas_val = gas_val if gas_val is not None else self.gas_val
        address_val = address_val if address_val is not None else self.address_val
        value_val = value_val if value_val is not None else self.value_val
        argsOffset_val = argsOffset_val if argsOffset_val is not None else self.argsOffset_val
        argsSize_val = argsSize_val if argsSize_val is not None else self.argsSize_val
        retOffset_val = retOffset_val if retOffset_val is not None else self.retOffset_val
        retSize_val = retSize_val if retSize_val is not None else self.retSize_val

        ostart = retOffset_val
        olen = retSize_val

        state.returndata['size'] = olen
        state.returndata['instruction_count'] = state.instruction_count
        
        if is_concrete(address_val) and bv_unsigned_value(address_val) == 0:
            logging.info("Calling into burn contract")
        elif is_concrete(address_val) and bv_unsigned_value(address_val) >= 1 and bv_unsigned_value(address_val) <= 8:
            # This is a pre-compiled contract
            #  --> https://www.evm.codes/precompiled?fork=arrowGlacier
            if bv_unsigned_value(address_val) == 1:
                # ECRecover precompiled contract
                # FIXME
                logging.info("Calling precompiled ecRecover contract")
                raise VMSymbolicError(f"Precompiled contract [ecRecover] not implemented")
            elif bv_unsigned_value(address_val) == 2:
                # SHA256 precompiled contract
                # FIXME
                logging.info("Calling precompiled SHA2-256 contract")
                raise VMSymbolicError(f"Precompiled contract [SHA2-256] not implemented")
            elif bv_unsigned_value(address_val) == 4:
                logging.info("Calling precompiled identity contract")
                istart = argsOffset_val
                ilen = argsSize_val
                state.memory.copy_return_data(istart, ilen, ostart, olen)
                # Assuming this always succeeds
                state.registers[self.res1_var] = BVV(1, 256)
            else:
                raise VMSymbolicError(f"Precompiled contract {bv_unsigned_value(address_val)} not implemented")
        elif is_concrete(olen):
            # If we have a concrete len for the return value we set the output memory to symbolic data
            for i in range(bv_unsigned_value(olen)):
                state.memory[BV_Add(ostart, BVV(i, 256))] = BVS(f'EXT_{state.instruction_count}_{i}_{state.xid}', 8)
            log_address_val = bv_unsigned_value(address_val) if is_concrete(address_val) else "<SYMBOLIC>"
            
            if log_address_val != "<SYMBOLIC>":
                logging.info(f"Calling contract {hex(log_address_val)} ({state.instruction_count}_{state.xid})")
        else:
            # FIXME: maybe consider a MAX_RETURN_SIZE option and use similar strategy used in SHA3
            raise VMSymbolicError("Unsupported symbolic retSize_val in CALL")

        if options.OPTIMISTIC_CALL_RESULTS:
            state.registers[self.res1_var] = BVV(1, 256)
        else:
            state.registers[self.res1_var] = BVS(f'CALLRESULT_{state.instruction_count}_{state.xid}', 256)

        state.set_next_pc()
        return [state]
    
    def set_likeyl_known_target_func(self, target_function):
        self.likely_known_target = target_function

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
        state.add_constraint(BV_UGE(state.balance, self.value_val))
        state.balance = BV_Sub(state.balance, self.value_val)
        return self._handle(state, value_val=self.value_val)


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
        return self._handle(state)


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
        value_val = utils.ctx_or_symbolic('CALLVALUE', state.ctx, state.xid)

        return self._handle(state, value_val=value_val)


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
        value_val = BVV(0, 256)

        return self._handle(state, value_val=value_val)
