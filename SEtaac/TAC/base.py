import logging

from SEtaac.exceptions import VMException
from SEtaac.state import SymbolicEVMState

log = logging.getLogger(__name__)


# This is the object exported from Gigahorse
class TAC_RawStatement:
    __name__ = "TAC_RawStatement"
    __internal_name__ = ""

    def __init__(self, tac_block_id: str, ident: str, opcode: str, operands: str = None, defs: list = None,
                 values: dict = None):
        self.tac_block_id = tac_block_id
        self.ident = ident
        self.opcode = opcode
        self.operands = operands if operands else list()
        self.defs = defs if defs else list()
        self.values = values if values else dict()

    def __str__(self):
        return f"TAC_RawStatement[blockid:{self.tac_block_id}|stmtid:{self.ident}] | opcode: {self.opcode} | " \
               f"operands:{self.operands} | defs:{self.defs} | values:{self.values}"


class Aliased:
    def __init__(self):
        __aliases__ = []

    def __getattr__(self, key):
        if key in object.__getattribute__(self, "__aliases__"):
            aliased_key = self.__aliases__[key]
            return object.__getattribute__(self, aliased_key)
        else:
            return object.__getattribute__(self, key)

    def __setattr__(self, key, value):
        if key in object.__getattribute__(self, "__aliases__"):
            aliased_key = self.__aliases__[key]
            object.__setattr__(self, aliased_key, value)
        else:
            object.__setattr__(self, key, value)


class TAC_Statement(Aliased):
    __internal_name__ = None
    __aliases__ = {}

    def __init__(self, block_id, stmt_id, uses=[], defs=[], values={}):
        super().__init__()
        self.block_ident = block_id
        self.stmt_ident = stmt_id

        # parse uses
        self.arg_vars = [v for v in uses]
        self.arg_vals = {v: values.get(v, None) for v in uses}
        self.num_args = len(self.arg_vars)

        self.raw_arg_vals = None

        # parse defs
        self.res_vars = [v for v in defs]
        self.res_vals = {v: values.get(v, None) for v in defs}
        self.num_ress = len(self.res_vars)

        # cast arg_vals to int
        self.arg_vals = {x: int(v, 16) if v else v for x, v in self.arg_vals.items()}
        # cast res_vals to int
        self.res_vals = {x: int(v, 16) if v else v for x, v in self.res_vals.items()}

        self.process_args()

    def process_args(self):
        # create arg vars/vals aliases
        for i in range(self.num_args):
            var = self.arg_vars[i]
            object.__setattr__(self, "arg{}_var".format(i + 1), var)
            object.__setattr__(self, "arg{}_val".format(i + 1), self.arg_vals[var])

        # create res vars/vals aliases
        for i in range(self.num_ress):
            var = self.res_vars[i]
            object.__setattr__(self, "res{}_var".format(i + 1), var)
            object.__setattr__(self, "res{}_val".format(i + 1), self.res_vals[var])

        # keep a copy of the arg_vals (for set_arg_val)
        self.raw_arg_vals = dict(self.arg_vals)

    def set_arg_val(self, state: SymbolicEVMState):
        # IMPORTANT: we need to reset this every time we re-execute this statement or we'll have the old registers
        # values in self.arg_vals (as set by this function)
        self.arg_vals = dict(self.raw_arg_vals)

        for i in range(self.num_args):
            var = self.arg_vars[i]
            arg_val = self.arg_vals[var]
            # todo: the fact that we are reading the original state's registers here (not succ) could cause issues e.g.,
            # if we need some kind of translation
            if var not in state.registers:
                raise VMException(f"Uninitialized var {var}")
            val = state.registers.get(var, None) if arg_val is None else arg_val
            self.arg_vals[var] = val
            object.__setattr__(self, "arg{}_val".format(i + 1), val)

        # log.debug(f"{self.arg_vals, self.res_vals}")

    @staticmethod
    def handler_without_side_effects(func):
        """
        Decorator that executes the basic functionalities for handlers without side effects
        (can just read and return statically computed results).
        """

        def wrap(self, state: SymbolicEVMState):
            self.set_arg_val(state)
            state.trace.append(state.curr_stmt)
            state.instruction_count += 1

            # If we already have all the results from the Gigahorse IR, just use it.
            if all([self.res_vals[var] is not None for var in self.res_vars]):
                succ = state

                # Grab vals from Gigahorse IR and registers if they are available.
                for var in self.res_vars:
                    succ.registers[var] = self.res_vals[var]

                succ.set_next_pc()
                return [succ]

            # otherwise, execute the actual handler
            successors = func(self, state)
            return successors

        return wrap

    @staticmethod
    def handler_with_side_effects(func):
        """
        Decorator that executes the basic functionalities for handlers with side effects
        (can't just read and return statically computed results).
        """

        def wrap(self, state: SymbolicEVMState):
            self.set_arg_val(state)
            state.trace.append(state.curr_stmt)
            state.instruction_count += 1

            # always execute the actual handler because we need the side-effects
            successors = func(self, state)
            return successors

        return wrap

    def __str__(self):
        args_str = ''
        for arg in self.arg_vars:
            args_str += "{}".format(arg)
            args_str += " "

        if not self.res_vars:
            res_str = ""
        else:
            res_str = ""
            for res in self.res_vars:
                res_str += "{}".format(res)
            res_str += " ="

        return "{} {} {}".format(res_str, self.__internal_name__, args_str).strip()

    def __repr__(self):
        return str(self)
