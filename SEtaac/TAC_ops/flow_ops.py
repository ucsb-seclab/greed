
import z3

from SEtaac import utils
from SEtaac.utils import concrete, is_true, get_solver
from SEtaac.exceptions import ExternalData, SymbolicError, IntractablePath, VMException

from .base import TAC_Septenary, TAC_Senary, TAC_UnaryNoRes, TAC_BinaryNoRes
from ..state import SymbolicEVMState

__all__ = ['TAC_Jump', 'TAC_Jumpi', 'TAC_Call', 'TAC_Callcode', 'TAC_Return', 'TAC_Delegatecall', 'TAC_Staticall']

class TAC_Jump(TAC_UnaryNoRes):
    __internal_name__ = "JUMP"
    __aliases__ = {'destination_var': 'op1_var', 'destination_val': 'op1_val'}

    def handle(self, state:SymbolicEVMState):
        # TODO: implement symbolic jump
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
        # TODO: implement jumpi
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
                succ.pc = succ.next_statement()
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

                succ_false.pc = succ.next_statement()
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
                succ.pc = succ.next_statement()
                succ.constraints.append(cond == 0)

                return [succ]
            else:
                # nothing is sat
                return []

class TAC_Call(TAC_Septenary):
    __internal_name__ = "CALL"
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
    def handler(self, state:SymbolicEVMState):
        pass

class TAC_Callcode(TAC_Septenary):
    __internal_name__ = "CALLCODE"
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
    def handler(self, state:SymbolicEVMState):
        pass

class TAC_Delegatecall(TAC_Senary):
    __internal_name__ = "DELEGATECALL"
    __aliases__ = {
                   'gas_var'       : 'op1_var', 'gas_val'       : 'op1_val', 
                   'address_var'   : 'op2_var', 'address_val'   : 'op2_val',
                   'argsOffset_var': 'op3_var', 'argsOffset_val': 'op3_val',
                   'argsSize_var'  : 'op4_var', 'argsSize_val'  : 'op4_val',
                   'retOffset_var' : 'op5_var', 'retOffset_val' : 'op5_val',
                   'retSize_var'   : 'op6_var', 'retSize_val'   : 'op6_val',
                   'success_var'   : 'res_var', 'success_val'   : 'res_val'
                   }
    def handler(self, state:SymbolicEVMState):
        pass

class TAC_Staticcall(TAC_Senary):
    __internal_name__ = "STATICCALL"
    __aliases__ = {
                   'gas_var'       : 'op1_var', 'gas_val'       : 'op1_val', 
                   'address_var'   : 'op2_var', 'address_val'   : 'op2_val',
                   'argsOffset_var': 'op3_var', 'argsOffset_val': 'op3_val',
                   'argsSize_var'  : 'op4_var', 'argsSize_val'  : 'op4_val',
                   'retOffset_var' : 'op5_var', 'retOffset_val' : 'op5_val',
                   'retSize_var'   : 'op6_var', 'retSize_val'   : 'op6_val',
                   'success_var'   : 'res_var', 'success_val'   : 'res_val'
                   }
    def handler(self, state:SymbolicEVMState):
        pass

class TAC_Return(TAC_BinaryNoRes):
    __internal_name__ = "RETURN"
    __aliases__ = {
                   'offset_var'    : 'op1_var', 'offset_val'    : 'op1_val', 
                   'size_var'      : 'op2_var', 'size_val'      : 'op2_val',
                   }
    def handler(self, state:SymbolicEVMState):
        pass