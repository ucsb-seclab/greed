import threading

from greed import options
from greed.utils.exceptions import SolverTimeout


class Solver:
    @staticmethod
    def solver_timeout(func):
        def raise_solver_timeout(self):
            self.solver.stop_search()

        def wrap(self, *args, **kwargs):
            # start a timer to stop solving if the solver takes too long
            timer = threading.Timer(options.SOLVER_TIMEOUT, raise_solver_timeout, [self])
            timer.start()
            result = func(self, *args, **kwargs)
            timer.cancel()
            return result

        return wrap

    def BVSort(self, width):
        raise Exception("Not implemented")

    def BVV(self, value, width):
        raise Exception("Not implemented")

    def BVS(self, symbol, width):
        raise Exception("Not implemented")

    def bv_unsigned_value(self, bv):
        raise Exception("Not implemented")

    def get_bv_by_name(self, bv):
        raise Exception("Not implemented")

    def is_concrete(self, bv):
        raise Exception("Not implemented")

    def is_sat(self, ):
        raise Exception("Not implemented")

    def is_unsat(self, ):
        raise Exception("Not implemented")

    def is_formula_sat(self, formula):
        raise Exception("Not implemented")

    def are_formulas_sat(self, terms):
        raise Exception("Not implemented")

    def is_formula_unsat(self, formula):
        raise Exception("Not implemented")

    def is_formula_true(self, formula):
        raise Exception("Not implemented")

    def is_formula_false(self, formula):
        raise Exception("Not implemented")

    def push(self, ):
        raise Exception("Not implemented")

    def pop(self, ):
        raise Exception("Not implemented")

    def add_assertion(self, formula):
        raise Exception("Not implemented")

    def add_assertions(self, formulas):
        raise Exception("Not implemented")

    def Array(self, symbol, index_sort, value_sort):
        raise Exception("Not implemented")

    def If(self, cond, value_if_true, value_if_false):
        raise Exception("Not implemented")

    def Equal(self, a, b):
        raise Exception("Not implemented")

    def NotEqual(self, a, b):
        raise Exception("Not implemented")

    def Or(self, *terms):
        raise Exception("Not implemented")

    def And(self, *terms):
        raise Exception("Not implemented")

    def Not(self, a):
        raise Exception("Not implemented")

    def BV_Extract(self, start, end, bv):
        raise Exception("Not implemented")

    def BV_Concat(self, terms):
        raise Exception("Not implemented")

    def BV_Add(self, a, b):
        raise Exception("Not implemented")

    def BV_Sub(self, a, b):
        raise Exception("Not implemented")

    def BV_Mul(self, a, b):
        raise Exception("Not implemented")

    def BV_UDiv(self, a, b):
        raise Exception("Not implemented")

    def BV_SDiv(self, a, b):
        raise Exception("Not implemented")

    def BV_SMod(self, a, b):
        raise Exception("Not implemented")

    def BV_SRem(self, a, b):
        raise Exception("Not implemented")

    def BV_URem(self, a, b):
        raise Exception("Not implemented")

    def BV_Sign_Extend(self, a, b):
        raise Exception("Not implemented")

    def BV_Zero_Extend(self, a, b):
        raise Exception("Not implemented")

    def BV_UGE(self, a, b):
        raise Exception("Not implemented")

    def BV_ULE(self, a, b):
        raise Exception("Not implemented")

    def BV_UGT(self, a, b):
        raise Exception("Not implemented")

    def BV_ULT(self, a, b):
        raise Exception("Not implemented")

    def BV_SGE(self, a, b):
        raise Exception("Not implemented")

    def BV_SLE(self, a, b):
        raise Exception("Not implemented")

    def BV_SGT(self, a, b):
        raise Exception("Not implemented")

    def BV_SLT(self, a, b):
        raise Exception("Not implemented")

    def BV_And(self, a, b):
        raise Exception("Not implemented")

    def BV_Or(self, a, b):
        raise Exception("Not implemented")

    def BV_Xor(self, a, b):
        raise Exception("Not implemented")

    def BV_Not(self, a):
        raise Exception("Not implemented")

    def BV_Shl(self, a, b):
        raise Exception("Not implemented")

    def BV_Shr(self, a, b):
        raise Exception("Not implemented")

    def BV_Sar(self, a, b):
        raise Exception("Not implemented")

    def Array_Store(self, arr, index, elem):
        raise Exception("Not implemented")

    def Array_Select(self, arr, index):
        raise Exception("Not implemented")

    def eval(self, term):
        raise Exception("Not implemented")

    def copy(self):
        raise Exception("Not implemented")
