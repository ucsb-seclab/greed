
import z3

from SEtaac import utils
from SEtaac.utils import concrete, is_true, get_solver
from SEtaac.exceptions import ExternalData, SymbolicError, IntractablePath, VMException

from .base import TAC_NoOperands, TAC_NoOperandsNoRes, TAC_DynamicOps, TAC_DynamicOpsNoRes
from ..state import SymbolicEVMState


__all__ = ['TAC_Throw', 'TAC_Callprivate', 'TAC_Returnprivate', 'TAC_Phi', 'TAC_Const', 'TAC_Nop']

class TAC_Throw(TAC_NoOperandsNoRes):
    __internal_name__ = "THROW"
    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Callprivate(TAC_DynamicOps):
    __internal_name__ = "CALLPRIVATE"
    __aliases__ = {}
    
    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        # read target
        target_pc = succ.registers[self.arg_vars[0]]
        if not concrete(target_pc):
            raise SymbolicError("CALLPRIVATE with symbolic target")

        # read arg-alias map
        args = self.arg_vars[1:]
        args_alias = succ.project.functions[target_pc]
        args_alias_map = dict(zip(args_alias, args))

        for alias, arg in args_alias_map:
            succ.registers['v' + alias.replace('0x', '')] = succ.registers[arg]

        # push stack frame
        succ.callstack.append((target_pc, self.res_vars))

        return [succ]


class TAC_Returnprivate(TAC_DynamicOpsNoRes):
    __internal_name__ = "RETURNPRIVATE"
    __aliases__ = {}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        # read target
        target_pc = succ.registers[self.arg_vars[0]]
        if not concrete(target_pc):
            raise SymbolicError("RETURNPRIVATE with symbolic target")

        # pop stack frame
        saved_target, callprivate_return_vars = succ.callstack.pop()

        if saved_target != target_pc:
            raise VMException("Return address does not match the callstack")

        # set the return variables to their correct values
        returnprivate_args = self.arg_vars[1:]
        for callprivate_return_var, returnprivate_arg in zip(callprivate_return_vars, returnprivate_args):
            succ.registers[callprivate_return_var] = succ.registers[returnprivate_arg]

        return [succ]


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


class TAC_Nop(TAC_NoOperandsNoRes):
    __internal_name__ = "NOP"

    def handle(self, state: SymbolicEVMState):
        succ = state.copy()

        succ.set_next_pc()
        return [succ]
