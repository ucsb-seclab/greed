import logging
import threading
from typing import List, TypeVar

from greed import options
from greed.utils.exceptions import SolverTimeout

from yices.YicesException import YicesException

log = logging.getLogger(__name__)

class Term:
    children: List['Term']
    operator: str

    def dump_smt2(self) -> str:
        """
        Return the SMT-LIB2 representation of the term.
        """
        raise NotImplementedError()

    def dump(self, pp=False):
        """
        Return the string representation of the term.
        """
        raise NotImplementedError()

    def pp(self):
        """
        Return the pretty-printed string representation of the term.
        """
        # naive implementation
        return self.dump(pp=True)



class BoolTerm(Term):
    pass

class BVTerm(Term):
    @property
    def bitsize(self):
        raise NotImplementedError()

class ArrayTerm(Term):
    pass

class Sort:
    pass

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

    def BVSort(self, width) -> Sort:
        """
        Return a bitvector sort of the given width.
        Args:
            width: The width of the bitvector
        """
        raise Exception("Not implemented")

    def BVV(self, value: int, width: int) -> BVTerm:
        """
        Return a bitvector value of the given width.
        Args:
            value: The value of the bitvector
            width: The width of the bitvector
        """
        raise Exception("Not implemented")

    def BVS(self, symbol: str, width: int) -> BVTerm:
        """
        Return a bitvector symbol of the given width.
        Args:
            symbol: The name of the symbol
            width: The width of the symbol
        """
        raise Exception("Not implemented")

    def bv_unsigned_value(self, bv: BVTerm) -> int:
        """
        Return the unsigned value of the given bitvector.
        Args:
            bv: The bitvector to evaluate
        """
        raise Exception("Not implemented")

    def get_bv_by_name(self, bv: BVTerm) -> Term:
        """
        Return the bitvector with the given name.
        Args:
            bv: The name of the bitvector
        """
        raise Exception("Not implemented")

    def is_concrete(self, bv: BVTerm) -> bool:
        """
        Return True if the given bitvector is concrete.
        Args:
            bv: The bitvector to check
        """
        raise Exception("Not implemented")

    def is_sat(self, ) -> bool:
        """
        Return True if the solver is in a satisfiable state.
        """
        raise Exception("Not implemented")

    def is_unsat(self, ) -> bool:
        """
        Return True if the solver is in an unsatisfiable state.
        """
        raise Exception("Not implemented")

    def is_formula_sat(self, formula: BoolTerm) -> bool:
        """
        Return True if the given formula is satisfiable.
        Args:
            formula: The formula to check
        """
        raise Exception("Not implemented")

    def are_formulas_sat(self, terms: List[BoolTerm]) -> bool:
        """
        Return True if the given formulas are satisfiable.
        Args:
            terms: The list of formulas to check
        """
        raise Exception("Not implemented")

    def is_formula_unsat(self, formula: BoolTerm) -> bool:
        """
        Return True if the given formula is unsatisfiable.
        Args:
            formula: The formula to check
        """
        raise Exception("Not implemented")

    def is_formula_true(self, formula: BoolTerm) -> bool:
        """
        Return True if the given formula is always True.
        Args:
            formula: The formula to check
        """
        raise Exception("Not implemented")

    def is_formula_false(self, formula: BoolTerm) -> bool:
        """
        Return True if the given formula is always False.
        Args:
            formula: The formula to check
        """
        raise Exception("Not implemented")

    def push(self, ) -> None:
        """
        Push a new context on the solver.
        """
        raise Exception("Not implemented")

    def pop(self, ) -> None:
        """
        Pop the current context from the solver.
        """
        raise Exception("Not implemented")

    def add_assertion(self, formula: BoolTerm) -> None:
        """
        Add a formula to the solver.
        Args:
            formula: The formula to add
        """
        raise Exception("Not implemented")

    def add_assertions(self, formulas: List[BoolTerm]) -> None:
        """
        Add a list of formulas to the solver.
        Args:
            formulas: The list of formulas to add
        """
        raise Exception("Not implemented")

    def Array(self, symbol: str, index_sort: Sort, value_sort: Sort) -> ArrayTerm:
        """
        Return an SMT Array.
        Args:
            symbol: The symbol of the array
            index_sort: The index sort of the array
            value_sort: The value sort of the array
        """
        raise Exception("Not implemented")

    IF_T = TypeVar('IF_T', BoolTerm, BVTerm, ArrayTerm)
    def If(self, cond: BoolTerm, value_if_true: IF_T, value_if_false: IF_T) -> IF_T:
        """
        Return an SMT If.
        Args:
            cond: The condition formula
            value_if_true: The value if the condition is True
            value_if_false: The value if the condition is False
        """
        raise Exception("Not implemented")

    def Equal(self, a: BVTerm, b: BVTerm) -> BoolTerm:
        """
        Return an SMT Equal with the given terms.
        Args:
            a: The first term
            b: The second term
        """
        raise Exception("Not implemented")

    def NotEqual(self, a: BVTerm, b: BVTerm) -> BoolTerm:
        """
        Return an SMT NotEqual with the given terms.
        Args:
            a: The first term
            b: The second term
        """
        raise Exception("Not implemented")

    def Or(self, *terms: List[BoolTerm]) -> BoolTerm:
        """
        Return an SMT Or with the given terms.
        Args:
            terms: The terms to OR
        """
        raise Exception("Not implemented")

    def And(self, *terms: List[BoolTerm]) -> BoolTerm:
        """
        Return an SMT And with the given terms.
        Args:
            terms: The terms to AND
        """
        raise Exception("Not implemented")

    def Not(self, a: BoolTerm) -> BoolTerm:
        """
        Return an SMT Not with the given term.
        Args:
            a: The term to NOT
        """
        raise Exception("Not implemented")

    def BV_Extract(self, start: int, end: int, bv: BVTerm) -> BVTerm:
        """
        Return a bitvector extract of the given bitvector.
        Args:
            start: The start of the extract
            end: The end of the extract
            bv: The bitvector to extract from
        """
        raise Exception("Not implemented")

    def BV_Concat(self, terms: List[BVTerm]) -> BVTerm:
        """
        Return a bitvector concatenation of the given bitvectors.
        Args:
            terms: The bitvectors to concatenate
        """
        raise Exception("Not implemented")

    def BV_Add(self, a: BVTerm, b: BVTerm) -> BVTerm:
        """
        Return a bitvector addition of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_Sub(self, a: BVTerm, b: BVTerm) -> BVTerm:
        """
        Return a bitvector subtraction of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_Mul(self, a: BVTerm, b: BVTerm) -> BVTerm:
        """
        Return a bitvector multiplication of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_UDiv(self, a: BVTerm, b: BVTerm) -> BVTerm:
        """
        Return a bitvector unsigned division of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_SDiv(self, a: BVTerm, b: BVTerm) -> BVTerm:
        """
        Return a bitvector signed division of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_SMod(self, a: BVTerm, b: BVTerm) -> BVTerm:
        """
        Return a bitvector signed modulo of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_SRem(self, a: BVTerm, b: BVTerm) -> BVTerm:
        """
        Return a bitvector signed remainder of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_URem(self, a: BVTerm, b: BVTerm) -> BVTerm:
        """
        Return a bitvector unsigned remainder of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_Sign_Extend(self, a: BVTerm, b: int) -> BVTerm:
        """
        Return a bitvector sign extension of the given bitvector.
        Args:
            a: The bitvector to extend
            b: The width of the extension
        """
        raise Exception("Not implemented")

    def BV_Zero_Extend(self, a: BVTerm, b: int) -> BVTerm:
        """
        Return a bitvector zero extension of the given bitvector.
        Args:
            a: The bitvector to extend
            b: The width of the extension
        """
        raise Exception("Not implemented")

    def BV_UGE(self, a: BVTerm, b: BVTerm) -> BoolTerm:
        """
        Return a bitvector unsigned greater or equal than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_ULE(self, a: BVTerm, b: BVTerm) -> BoolTerm:
        """
        Return a bitvector unsigned less or equal than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_UGT(self, a: BVTerm, b: BVTerm) -> BoolTerm:
        """
        Return a bitvector unsigned greater than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_ULT(self, a: BVTerm, b: BVTerm) -> BoolTerm:
        """
        Return a bitvector unsigned less than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_SGE(self, a: BVTerm, b: BVTerm) -> BoolTerm:
        """
        Return a bitvector signed greater or equal than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_SLE(self, a: BVTerm, b: BVTerm) -> BoolTerm:
        """
        Return a bitvector signed less or equal than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_SGT(self, a: BVTerm, b: BVTerm) -> BoolTerm:
        """
        Return a bitvector signed greater than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_SLT(self, a: BVTerm, b: BVTerm) -> BoolTerm:
        """
        Return a bitvector signed less than of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_And(self, a: BVTerm, b: BVTerm) -> BVTerm:
        """
        Return a bitvector bitwise and of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_Or(self, a: BVTerm, b: BVTerm) -> BVTerm:
        """
        Return a bitvector bitwise or of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_Xor(self, a: BVTerm, b: BVTerm) -> BVTerm:
        """
        Return a bitvector bitwise xor of the given bitvectors.
        Args:
            a: The first bitvector
            b: The second bitvector
        """
        raise Exception("Not implemented")

    def BV_Not(self, a: BVTerm) -> BVTerm:
        """
        Return a bitvector not of the given bitvector.
        Args:
            a: The bitvector to not
        """
        raise Exception("Not implemented")

    def BV_Shl(self, a: BVTerm, b: BVTerm) -> BVTerm:
        """
        Return a bitvector shift left of the given bitvector.
        Args:
            a: The bitvector to shift
            b: The shift amount
        """
        raise Exception("Not implemented")

    def BV_Shr(self, a: BVTerm, b: BVTerm) -> BVTerm:
        """
        Return a bitvector shift right of the given bitvector.
        Args:
            a: The bitvector to shift
            b: The shift amount
        """
        raise Exception("Not implemented")

    def BV_Sar(self, a: BVTerm, b: BVTerm) -> BVTerm:
        """
        Return a bitvector arithmetic shift right of the given bitvector.
        Args:
            a: The bitvector to shift
            b: The shift amount
        """
        raise Exception("Not implemented")

    def Array_Store(self, arr: ArrayTerm, index: BVTerm, elem: BVTerm) -> ArrayTerm:
        """
        Return an SMT Array_Store with the given terms.
        Args:
            arr: The array to store to
            index: The index to store to
            elem: The element to store
        """
        raise Exception("Not implemented")

    def Array_Select(self, arr: ArrayTerm, index: BVTerm) -> BVTerm:
        """
        Return an SMT Array_Select with the given terms.
        Args:
            arr: The array to select from
            index: The index to select from
        """
        raise Exception("Not implemented")

    def eval(self, term: Term):
        """
        Evaluate the given term.
        Args:
            term: The term to evaluate
        """
        raise Exception("Not implemented")

    def copy(self) -> 'Solver':
        """
        Implement the cloning of the solver when forking.
        """
        raise Exception("Not implemented")
