
import z3

from SEtaac import utils
from SEtaac.utils import concrete, is_true, get_solver
from SEtaac.exceptions import ExternalData, SymbolicError, IntractablePath, VMException, VM_NoSuccessors

from .base import TAC_NoOperands, TAC_NoOperandsNoRes, TAC_DynamicOps, TAC_DynamicOpsNoRes
from ..state import SymbolicEVMState


__all__ = ['TAC_Throw', 'TAC_Callprivate', 'TAC_Returnprivate', 'TAC_Return', 'TAC_Phi', 'TAC_Const', 'TAC_Nop']

class TAC_Throw(TAC_NoOperandsNoRes):
    __internal_name__ = "THROW"
    def handle(self, state:SymbolicEVMState):
        pass

class TAC_Callprivate(TAC_DynamicOps):
    __internal_name__ = "CALLPRIVATE"
    __aliases__ = {}
    
    def handle(self, state:SymbolicEVMState):
        self.set_op_val(state)
        succ = state.copy()

        # read target
        dest_var = self.arg_vars[0]
        dest_val = self.arg_vals[dest_var]
        target_bb_id = hex(dest_val)
        target_bb = state.project.factory.block(target_bb_id)

        # read arg-alias map
        args = self.arg_vars[1:]
        args_alias = target_bb.function.arguments
        alias_arg_map = dict(zip(args_alias, args))

        for alias, arg in alias_arg_map.items():
            succ.registers['v' + alias.replace('0x', '')] = succ.registers[arg]

        # read destination
        dest = target_bb.first_ins.stmt_ident
        # if not concrete(dest):
        #     raise SymbolicError("CALLPRIVATE with symbolic target")

        # push stack frame
        try:
            saved_return_pc = succ.get_next_pc()
        except VM_NoSuccessors:
            fake_exit_bb = state.project.factory.block('fake_exit')
            saved_return_pc = fake_exit_bb.statements[0].stmt_ident

        succ.callstack.append((saved_return_pc, self.res_vars))

        # jump to target
        succ.pc = dest

        return [succ]


class TAC_Returnprivate(TAC_DynamicOpsNoRes):
    __internal_name__ = "RETURNPRIVATE"
    __aliases__ = {}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()

        # pop stack frame (read saved return pc from stack)
        saved_return_pc, callprivate_return_vars = succ.callstack.pop()

        # set the return variables to their correct values
        returnprivate_args = self.arg_vars[1:]
        for callprivate_return_var, returnprivate_arg in zip(callprivate_return_vars, returnprivate_args):
            succ.registers[callprivate_return_var] = succ.registers[returnprivate_arg]

        succ.pc = saved_return_pc
        return [succ]


class TAC_Return(TAC_Returnprivate):
    __internal_name__ = "RETURN"


class TAC_Phi(TAC_DynamicOps):
    __internal_name__ = "PHI"
    __aliases__ = {}
    
    def handle(self, state:SymbolicEVMState):
        successors = []
        # Let's say we have v6 = PHI v1,v2.
        # If 'v2' has not been defined yet, v6 = v1 for sure.
        # Otherwise, as of now we can over-approximate and consider both assigment 
        # possible and forking. 
        # FIXME: can we do better tho, this might end up exploding and leaf to
        #        impossible paths.
        var = self.res_vars[0]
        for arg in self.arg_vars:
            # is this variable defined already?
            if state.registers.get(arg, None):
                succ = state.copy()
                succ.registers[var] = succ.registers[arg]
                successors.append(succ)
        return successors
        

class TAC_Const(TAC_NoOperands):
    __internal_name__ = "CONST"
    __aliases__ = {}

    def handle(self, state:SymbolicEVMState):
        succ = state.copy()
        succ.registers[self.res_var] = self.res_val
        succ.set_next_pc()
        return [succ]


class TAC_Nop(TAC_NoOperandsNoRes):
    __internal_name__ = "NOP"

    def handle(self, state: SymbolicEVMState):
        succ = state.copy()

        succ.set_next_pc()
        return [succ]
