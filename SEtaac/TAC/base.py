import logging
from typing import List, Mapping, Callable

from SEtaac.utils.solver.shortcuts import BVV
from SEtaac.utils.exceptions import VMException
from SEtaac.state import SymbolicEVMState

log = logging.getLogger(__name__)


class Aliased(object):
    __aliases__ = {}

    def __getattr__(self, key: str):
        if key in object.__getattribute__(self, "__aliases__"):
            aliased_key = self.__aliases__[key]
            return object.__getattribute__(self, aliased_key)
        else:
            return object.__getattribute__(self, key)

    def __setattr__(self, key: str, value):
        if key in object.__getattribute__(self, "__aliases__"):
            aliased_key = self.__aliases__[key]
            object.__setattr__(self, aliased_key, value)
        else:
            object.__setattr__(self, key, value)


class TAC_Statement(Aliased):
    __internal_name__ = None

    def __init__(self, block_id: str, stmt_id: str, uses: List[str] = None, defs: List[str] = None,
                 values: Mapping[str, str] = None):
        uses = uses or list()
        defs = defs or list()
        values = values or list()

        self.block_id = block_id
        self.id = stmt_id

        # parse uses
        self.arg_vars = [v for v in uses]
        self.arg_vals = {v: values.get(v, None) for v in uses}
        self.num_args = len(self.arg_vars)

        self.raw_arg_vals = None

        # parse defs
        self.res_vars = [v for v in defs]
        self.res_vals = {v: values.get(v, None) for v in defs}
        self.num_ress = len(self.res_vars)

        # cast arg_vals to bvv
        for x, v in self.arg_vals.items():
            if v:
                self.arg_vals[x] = BVV(int(v, 16), 256)

        # cast res_vals to bvv
        for x, v in self.res_vals.items():
            if v:
                self.res_vals[x] = BVV(int(v, 16), 256)

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

        # args = {k:bv_unsigned_value(v) if v and is_concrete(v) else '<SYMBOL>' for k, v in self.arg_vals.items()}
        # ress = {k:bv_unsigned_value(v) if v and is_concrete(v) else '<SYMBOL>' for k, v in self.res_vals.items()}
        # log.debug(f"{args, ress}")

    @staticmethod
    def handler_without_side_effects(func: Callable[["TAC_Statement", SymbolicEVMState], List[SymbolicEVMState]]):
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
    def handler_with_side_effects(func: Callable[["TAC_Statement", SymbolicEVMState], List[SymbolicEVMState]]):
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
