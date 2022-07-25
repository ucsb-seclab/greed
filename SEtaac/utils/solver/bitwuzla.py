from contextlib import contextmanager

import pybitwuzla

from SEtaac.utils.solver.base import Solver


def resets_sat_status(func):
    def wrap(self, *args, **kwargs):
        # reset internal sat_status after calling the target method
        res = func(self, *args, **kwargs)
        self._sat_status = None
        return res
    return wrap


class Bitwuzla(Solver):
    """
    This is a singleton class
    """

    def __init__(self):
        # todo: force single instantiation
        self.solver = pybitwuzla.Bitwuzla()
        self.solver.set_option(pybitwuzla.Option.PRODUCE_MODELS, 1)
        self.solver.set_option(pybitwuzla.Option.INCREMENTAL, True)
        self.BVSort_cache = dict()
        self.BVV_cache = dict()
        self.BVS_cache = dict()

        self._sat_status = None

    def BVSort(self, width):
        if width not in self.BVSort_cache:
            self.BVSort_cache[width] = self.solver.mk_bv_sort(width)
        return self.BVSort_cache[width]

    def BVV(self, value, width):
        if (value, width) not in self.BVV_cache:
            self.BVV_cache[(value, width)] = self.solver.mk_bv_value(self.BVSort(width), value)
        return self.BVV_cache[(value, width)]

    def BVS(self, symbol, width):
        if (symbol, width) not in self.BVS_cache:
            self.BVS_cache[(symbol, width)] = self.solver.mk_const(self.BVSort(width), symbol=symbol)
        return self.BVS_cache[(symbol, width)]

    def bv_unsigned_value(self, bv):
        assert bv.is_bv_value()
        return int(bv.dump()[2:], 2)

    def is_concrete(self, bv):
        # FIXME We can remove this when we are sure this won't actually happen.
        assert bv.is_bv(), "NOT IMPLEMENTED. This currently only supports BitVectors"
        return bv.is_bv_value()

    def is_sat(self):
        # cache the last check_sat result so that we can check it when querying the solver's model, and we don't need
        # to call check_sat (and thus generate a new and possibly inconsistent model) every time we need to eval a term
        self._sat_status = self.solver.check_sat()
        return self._sat_status == pybitwuzla.Result.SAT

    def is_unsat(self):
        # cache the last check_sat result so that we can check it when querying the solver's model, and we don't need
        # to call check_sat (and thus generate a new and possibly inconsistent model) every time we need to eval a term
        self._sat_status = self.solver.check_sat()
        return self._sat_status == pybitwuzla.Result.UNSAT

    def substitute_terms(self, formula, substitute_map):
        return self.solver.substitute(formula, substitute_map)

    @resets_sat_status
    def is_formula_sat(self, formula):
        self.add_assumption(formula)
        return self.is_sat()

    @resets_sat_status
    def is_formula_unsat(self, formula):
        self.add_assumption(formula)
        return self.is_unsat()

    @resets_sat_status
    def is_formula_true(self, formula):
        return self.is_formula_unsat(self.Not(formula))

    @resets_sat_status
    def is_formula_false(self, formula):
        return self.is_formula_unsat(formula)

    @resets_sat_status
    def push(self):
        self.solver.push()

    @resets_sat_status
    def pop(self):
        self.solver.pop()

    @resets_sat_status
    def add_assertion(self, formula):
        self.solver.assert_formula(formula)

    @resets_sat_status
    def add_assertions(self, formulas):
        self.solver.assert_formula(*formulas)

    @resets_sat_status
    def add_assumption(self, formula):
        # assumptions are discarded after each call to .check_sat, assertions are not
        self.solver.assume_formula(formula)

    @resets_sat_status
    def add_assumptions(self, formulas):
        self.solver.assume_formula(*formulas)

    @resets_sat_status
    def reset_assumptions(self):
        self.solver.reset_assumptions()

    @resets_sat_status
    def fixate_assumptions(self):
        self.solver.fixate_assumptions()

    @resets_sat_status
    def simplify(self):
        self.solver.simplify()

    def Array(self, symbol, index_sort, value_sort):
        return self.solver.mk_const(self.solver.mk_array_sort(index_sort, value_sort), symbol=symbol)

    def ConstArray(self, symbol, index_sort, value_sort, default):
        res = self.solver.mk_const_array(self.solver.mk_array_sort(index_sort, value_sort), default)
        res.set_symbol(symbol)
        return res

    # CONDITIONAL OPERATIONS

    def If(self, cond, value_if_true, value_if_false):
        return self.solver.mk_term(pybitwuzla.Kind.ITE, [cond, value_if_true, value_if_false])

    # BOOLEAN OPERATIONS

    def Equal(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.EQUAL, [a, b])

    def NotEqual(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.DISTINCT, [a, b])

    def Or(self, *terms):
        return self.solver.mk_term(pybitwuzla.Kind.OR, terms)

    def And(self, *terms):
        return self.solver.mk_term(pybitwuzla.Kind.AND, terms)

    def Not(self, a):
        return self.solver.mk_term(pybitwuzla.Kind.NOT, [a])

    # BV OPERATIONS

    def bv_size(self, bv):
        return bv.get_sort().bv_get_size()

    def BV_Extract(self, start, end, bv):
        return self.solver.mk_term(pybitwuzla.Kind.BV_EXTRACT, [bv], [end, start])

    def BV_Concat(self, terms):
        return self.solver.mk_term(pybitwuzla.Kind.BV_CONCAT, terms)

    def BV_Add(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_ADD, [a, b])

    def BV_Sub(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_SUB, [a, b])

    def BV_Mul(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_MUL, [a, b])

    def BV_UDiv(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_UDIV, [a, b])

    def BV_SDiv(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_SDIV, [a, b])

    def BV_SMod(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_SMOD, [a, b])

    def BV_SRem(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_SREM, [a, b])

    def BV_URem(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_UREM, [a, b])

    def BV_Sign_Extend(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_SIGN_EXTEND, [a], [b])

    def BV_Zero_Extend(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_ZERO_EXTEND, [a], [b])

    def BV_UGE(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_UGE, [a, b])

    def BV_ULE(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_ULE, [a, b])

    def BV_UGT(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_UGT, [a, b])

    def BV_ULT(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_ULT, [a, b])

    def BV_SGE(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_SGE, [a, b])

    def BV_SLE(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_SLE, [a, b])

    def BV_SGT(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_SGT, [a, b])

    def BV_SLT(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_SLT, [a, b])

    def BV_And(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_AND, [a, b])

    def BV_Or(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_OR, [a, b])

    def BV_Xor(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_XOR, [a, b])

    def BV_Not(self, a):
        return self.solver.mk_term(pybitwuzla.Kind.BV_NOT, [a])

    def BV_Shl(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_SHL, [a, b])

    def BV_Shr(self, a, b):
        return self.solver.mk_term(pybitwuzla.Kind.BV_SHR, [a, b])

    def BV_Sar(self, a, b):
        # (n&msb) | (n>>shift)
        '''
        msb_set = self.BV_Extract(255, 255, a)
        shift_mask = self.BV_Shr(self.BVV(2 ** 256 - 1, 256), b)

        shifted = self.BV_Shr(a, b)
        res = self.If(msb_set,
                      self.BV_Or(shifted, self.BV_Not(shift_mask)),
                      self.BV_And(shifted, shift_mask))
        '''
        res_shift1 = self.BV_Shr(a, b)
        res_shift2 = self.BV_Extract(0, 255-self.bv_unsigned_value(b),res_shift1)
        res = self.BV_Sign_Extend(res_shift2, 256-self.bv_size(res_shift2))
        return res

    # ARRAY OPERATIONS

    def Array_Store(self, arr, index, elem):
        return self.solver.mk_term(pybitwuzla.Kind.ARRAY_STORE, [arr, index, elem])

    def Array_Select(self, arr, index):
        return self.solver.mk_term(pybitwuzla.Kind.ARRAY_SELECT, [arr, index])

    def eval_one(self, term, cast_to="int"):
        if self._sat_status is None:
            self._sat_status = self.solver.check_sat()
        assert self._sat_status == pybitwuzla.Result.SAT
        if cast_to == "int":
            return int(self.solver.get_value_str(term))
        else:
            return self.solver.get_value_str(term)
 
    def eval_one_array(self, array, length):
        raise Exception("this doesn't work for now because it does not consider the side effects of memory reads")
        # if self._sat_status is None:
        #     self._sat_status = self.solver.check_sat()
        # assert self._sat_status == pybitwuzla.Result.SAT
        #
        # return [int(self.solver.get_value_str(self.Array_Select(array, self.BVV(i, 256))), 2) for i in range(length)]
