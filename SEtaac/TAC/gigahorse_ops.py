import logging

from SEtaac.TAC.base import TAC_Statement
from SEtaac.exceptions import VM_NoSuccessors
from SEtaac.state import SymbolicEVMState

__all__ = ['TAC_Throw', 'TAC_Callprivate', 'TAC_Returnprivate', 'TAC_Return', 'TAC_Phi', 'TAC_Const', 'TAC_Nop']

log = logging.getLogger(__name__)


class TAC_Throw(TAC_Statement):
    __internal_name__ = "THROW"

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.halt = True

        return [succ]


class TAC_Callprivate(TAC_Statement):
    __internal_name__ = "CALLPRIVATE"
    __aliases__ = {}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        # read target
        dest_var = self.arg_vars[0]
        dest_val = self.arg_vals[dest_var]
        target_bb_id = hex(dest_val)
        target_bb = succ.project.factory.block(target_bb_id)

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
            fake_exit_bb = succ.project.factory.block('fake_exit')
            saved_return_pc = fake_exit_bb.statements[0].stmt_ident

        succ.callstack.append((saved_return_pc, self.res_vars))

        # jump to target
        succ.pc = dest

        return [succ]


class TAC_Returnprivate(TAC_Statement):
    __internal_name__ = "RETURNPRIVATE"
    __aliases__ = {}

    @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

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


class TAC_Phi(TAC_Statement):
    __internal_name__ = "PHI"
    __aliases__ = {}

    # @TAC_Statement.handler_with_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        # wild assumption: always pick the most recently accessed var in PHI (top of the stack)
        # more rationale: PHI is emitted when the top of the stack is uncertain (e.g., there are two paths leading to
        # this block: A->C but also A->B->C, and B pushes something on the stack).
        # PHI outputs the variable that is EFFECTIVELY on the top of the stack, at this point in the execution
        # Our assumption here is that if variable b is written AFTER another variable a (in TAC), then in the original
        # EVM code it was pushed to the stack AFTER such variable a

        # WARNING: IF THERE ARE TWO IDENTICAL CONSECUTIVE PHI STATEMENTS, THIS IS VERY LIKELY TO BE BROKEN
        # (0x109C4f2CCc82C4d77Bde15F306707320294Aea3F)
        # target_var = self.res_vars[0]
        # last_written = state.registers.last_written(self.arg_vars)
        #
        # succ.registers[target_var] = self.arg_vals[last_written]
        
        succ.set_next_pc()
        return [succ]


class TAC_Const(TAC_Statement):
    __internal_name__ = "CONST"
    __aliases__ = {}

    @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.registers[self.res1_var] = self.res1_val

        succ.set_next_pc()
        return [succ]


class TAC_Nop(TAC_Statement):
    __internal_name__ = "NOP"

    # @TAC_Statement.handler_without_side_effects
    def handle(self, state: SymbolicEVMState):
        succ = state

        succ.set_next_pc()
        return [succ]
