
import z3

from SEtaac import utils
from SEtaac.utils import concrete, is_true, get_solver
from SEtaac.exceptions import ExternalData, SymbolicError, IntractablePath, VMException

from .base import TAC_NoOperands, TAC_NoOperandsNoRes, TAC_DynamicOps, TAC_DynamicOpsNoRes
from ..state import SymbolicEVMState


__all__ = ['TAC_Throw', 'TAC_Callprivate', 'TAC_Returnprivate', 'TAC_Phi', 'TAC_Const']

class TAC_Throw(TAC_NoOperandsNoRes):
    __internal_name__ = "THROW"
    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Callprivate(TAC_DynamicOps):
    __internal_name__ = "CALLPRIVATE"
    __aliases__ = {}
    
    def handle(self, state:SymbolicEVMState):
        # todo: use succ.callstack to implement callprivate and returnprivate
        # in returnprivate assert that we are returning from the last pushed context
        pass

class TAC_Returnprivate(TAC_DynamicOpsNoRes):
    __internal_name__ = "RETURNPRIVATE"
    __aliases__ = {}
     
    def __str__(self):        
        args_str = ''
        for arg in self.arg_vars:
            if not self.arg_vals.get(arg, None):
                args_str += "{}({})".format(arg,self.arg_vals[arg])
            else:
                args_str += "{}".format(arg)
            args_str += " "
        
        return "{} {}".format(self.__internal_name__, args_str)

class TAC_Phi(TAC_DynamicOps):
    __internal_name__ = "PHI"
    __aliases__ = {}
    
    def handler(self, state:SymbolicEVMState):
        successors = []
        succ = state.copy()
        # Let's say we have v6 = PHI v1,v2.
        # If 'v2' has not been defined yet, v6 = v1 for sure.
        # Otherwise, as of now we can over-approximate and consider both assigment 
        # possible and forking. 
        # FIXME: can we do better tho, this might end up exploding and leaf to
        #        impossible paths.
        for arg in self.args_var:
            # is this variable defined already?
            if state.registers.get(arg, None):
                succ = state.copy()
                succ.registers[self.res_var] = state.registers[arg]
                successors.append(succ)
        return successors
        

class TAC_Const(TAC_NoOperands):
    __internal_name__ = "CONST"
    __aliases__ = {}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        succ.registers[self.var] = self.val
        succ.set_next_pc()
        return [succ]