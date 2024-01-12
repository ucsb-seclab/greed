import logging
import threading

from greed import options
from greed.utils.exceptions import SolverTimeout

from yices.YicesException import YicesException

log = logging.getLogger(__name__)


class Solver:
    """
    This class represents a solver.
    Every solver must implement this interface.
    """
    @staticmethod
    def solver_timeout(func):
        def raise_solver_timeout(self):
            self.timed_out = True
            self.solver.stop_search()
            log.warning("Solver timeout, stopping search")

        def wrap(self, *args, **kwargs):
            # start a timer to stop solving if the solver takes too long
            timer = threading.Timer(options.SOLVER_TIMEOUT, raise_solver_timeout, [self])
            timer.start()
            try:
                result = func(self, *args, **kwargs)
                if self.timed_out:
                    raise SolverTimeout
                return result
            except YicesException:
                if self.timed_out:
                    raise SolverTimeout
                raise
            finally:
                timer.cancel()
                self.timed_out = False

        return wrap

    def BVSort(self, width):
        """
        Return a bitvector sort of the given width.
        Args:
            width: The width of the bitvector
        """
        raise Exception("Not implemented")

    def BVV(self, value, width):
        """
        Return a bitvector value of the given width.
        Args:
            value: The value of the bitvector
            width: The width of the bitvector
        """
        raise Exception("Not implemented")

    def BVS(self, symbol, width):
        """
        Return a bitvector symbol of the given width.
        Args:
            symbol: The name of the symbol
            width: The width of the symbol
        """
        raise Exception("Not implemented")

    def bv_unsigned_value(self, bv):
        """
        Return the unsigned value of the given bitvector.
        Args:
            bv: The bitvector to evaluate
        """
        raise Exception("Not implemented")

    def get_bv_by_name(self, bv):
        """
        Return the bitvector with the given name.
        Args:
            bv: The name of the bitvector
        """
        raise Exception("Not implemented")

    def is_concrete(self, bv):
        """
        Return True if the given bitvector is concrete.
        Args:
            bv: The bitvector to check
        """
        raise Exception("Not implemented")

    def is_sat(self, ):
        """
        Return True if the solver is in a satisfiable state.
        """
        raise Exception("Not implemented")

    def is_unsat(self, ):
        """
        Return True if the solver is in an unsatisfiable state.
        """
        raise Exception("Not implemented")

    def is_formula_sat(self, formula):
        """
        Return True if the given formula is satisfiable.
        Args:
            formula: The formula to check
        """
        raise Exception("Not implemented")

    def are_formulas_sat(self, terms):
        """
        Return True if the given formulas are satisfiable.
        Args:
            terms: The list of formulas to check
        """
        raise Exception("Not implemented")

    def is_formula_unsat(self, formula):
        """
        Return True if the given formula is unsatisfiable.
        Args:
            formula: The formula to check
        """
        raise Exception("Not implemented")

    def is_formula_true(self, formula):
        """
        Return True if the given formula is always True.
        Args:
            formula: The formula to check
        """
        raise Exception("Not implemented")

    def is_formula_false(self, formula):
        """
        Return True if the given formula is always False.
        Args:
            formula: The formula to check
        """
        raise Exception("Not implemented")

    def push(self, ):
        """
        Push a new context on the solver.
        """
        raise Exception("Not implemented")

    def pop(self, ):
        """
        Pop the current context from the solver.
        """
        raise Exception("Not implemented")

    def add_assertion(self, formula):
        """
        Add a formula to the solver.
        Args:
            formula: The formula to add
        """
        raise Exception("Not implemented")

    def add_assertions(self, formulas):
        """
        Add a list of formulas to the solver.
        Args:
            formulas: The list of formulas to add
        """
        raise Exception("Not implemented")

    def Array(self, symbol, index_sort, value_sort):
        """
        Return an SMT Array.
        Args:
            symbol: The symbol of the array
            index_sort: The index sort of the array
            value_sort: The value sort of the array
        """
        raise Exception("Not implemented")

    def If(self, cond, value_if_true, value_if_false):
        """
        Return an SMT If.
        Args:
            cond: The condition formula
            value_if_true: The value if the condition is True
            value_if_false: The value if the condition is False
        """
        raise Exception("Not implemented")

    def Equal(self, a, b):
        """
        Return an SMT Equal with the given terms.
        Args:
            a: The first term
            b: The second term
        """
        raise Exception("Not implemented")

    def NotEqual(self, a, b):
        """
        Return an SMT NotEqual with the given terms.
        Args:
            a: The first term
            b: The second term
        """
        raise Exception("Not implemented")

    def Or(self, *terms):
        """
        Return an SMT Or with the given terms.
        Args:
            terms: The terms to OR
        """
        raise Exception("Not implemented")

    def And(self, *terms):
        """
        Return an SMT And with the given terms.
        Args:
            terms: The terms to AND
        """
        raise Exception("Not implemented")

    def Not(self, a):
        """
        Return an SMT Not with the given term.
        Args:
            a: The term to NOT
        """
        raise Exception("Not implemented")

    def BV_Extract(self, start, end, bv):
        """
        Return a bitvector extract of the given bitvector.
        Args:
            start: The start of the extract
            end: The end of the extract
            bv: The bitvector to extract from
        """
        raise Exception("Not implemented")

    def BV_Concat(self, terms):
        """
        Return a bitvector concatenation of the given bitvectors.
        Args:
            terms: The bitvectors to concatenate
        """
        raise Exception("Not implemented")

    def BV_Add(self, a, b):
        """
        Return a bitvector addition of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_Sub(self, a, b):
        """
        Return a bitvector subtraction of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_Mul(self, a, b):
        """
        Return a bitvector multiplication of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_UDiv(self, a, b):
        """
        Return a bitvector unsigned division of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_SDiv(self, a, b):
        """
        Return a bitvector signed division of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_SMod(self, a, b):
        """
        Return a bitvector signed modulo of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_SRem(self, a, b):
        """
        Return a bitvector signed remainder of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_URem(self, a, b):
        """
        Return a bitvector unsigned remainder of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_Sign_Extend(self, a, b):
        """
        Return a bitvector sign extension of the given bitvector.
        Args:
            a: The bitvector to extend
            b: The width of the extension
        """
        raise Exception("Not implemented")

    def BV_Zero_Extend(self, a, b):
        """
        Return a bitvector zero extension of the given bitvector.
        Args:
            a: The bitvector to extend
            b: The width of the extension
        """
        raise Exception("Not implemented")

    def BV_UGE(self, a, b):
        """
        Return a bitvector unsigned greater or equal than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_ULE(self, a, b):
        """
        Return a bitvector unsigned less or equal than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_UGT(self, a, b):
        """
        Return a bitvector unsigned greater than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_ULT(self, a, b):
        """
        Return a bitvector unsigned less than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_SGE(self, a, b):
        """
        Return a bitvector signed greater or equal than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_SLE(self, a, b):
        """
        Return a bitvector signed less or equal than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_SGT(self, a, b):
        """
        Return a bitvector signed greater than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_SLT(self, a, b):
        """
        Return a bitvector signed less than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_And(self, a, b):
        """
        Return a bitvector bitwise and of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_Or(self, a, b):
        """
        Return a bitvector bitwise or of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_Xor(self, a, b):
        """
        Return a bitvector bitwise xor of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_Not(self, a):
        """
        Return a bitvector not of the given bitvector.
        Args:
            a: The bitvector to not
        """
        raise Exception("Not implemented")

    def BV_Shl(self, a, b):
        """
        Return a bitvector shift left of the given bitvector.
        Args:
            a: The bitvector to shift
            b: The shift amount
        """
        raise Exception("Not implemented")

    def BV_Shr(self, a, b):
        """
        Return a bitvector shift right of the given bitvector.
        Args:
            a: The bitvector to shift
            b: The shift amount
        """
        raise Exception("Not implemented")

    def BV_Sar(self, a, b):
        """
        Return a bitvector arithmetic shift right of the given bitvector.
        Args:
            a: The bitvector to shift
            b: The shift amount
        """
        raise Exception("Not implemented")

    def Array_Store(self, arr, index, elem):
        """
        Return an SMT Array_Store with the given terms.
        Args:
            arr: The array to store to
            index: The index to store to
            elem: The element to store
        """
        raise Exception("Not implemented")

    def Array_Select(self, arr, index):
        """
        Return an SMT Array_Select with the given terms.
        Args:
            arr: The array to select from
            index: The index to select from
        """
        raise Exception("Not implemented")

    def eval(self, term):
        """
        Evaluate the given term.
        Args:
            term: The term to evaluate
        """
        raise Exception("Not implemented")

    def copy(self):
        """
        Implement the cloning of the solver when forking.
        """
        raise Exception("Not implemented")
