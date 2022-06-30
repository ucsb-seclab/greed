from SEtaac.utils.solver.base import Solver

import sys

sys.path.insert(0, "/home/ruaronicola/bitwuzla/build/lib/")
import pybitwuzla


class Bitwuzla(Solver):
    """
    This is a singleton class, and all methods are static
    """

    BW = pybitwuzla.Bitwuzla()

    BW.set_option(pybitwuzla.Option.PRODUCE_MODELS, 1)
    BW.set_option(pybitwuzla.Option.INCREMENTAL, True)

    BVSort_cache = dict()
    BVV_cache = dict()
    BVS_cache = dict()


    @staticmethod
    def BVSort(width):
        if width not in Bitwuzla.BVSort_cache:
            Bitwuzla.BVSort_cache[width] = Bitwuzla.BW.mk_bv_sort(width)
        return Bitwuzla.BVSort_cache[width]

    @staticmethod
    def BVV(value, width):
        if (value, width) not in Bitwuzla.BVV_cache:
            Bitwuzla.BVV_cache[(value, width)] = Bitwuzla.BW.mk_bv_value(Bitwuzla.BVSort(width), value)
        return Bitwuzla.BVV_cache[(value, width)]

    @staticmethod
    def BVS(symbol, width):
        if (symbol, width) not in Bitwuzla.BVS_cache:
            Bitwuzla.BVS_cache[(symbol, width)] = Bitwuzla.BW.mk_const(Bitwuzla.BVSort(width), symbol=symbol)
        return Bitwuzla.BVS_cache[(symbol, width)]

    @staticmethod
    def bv_unsigned_value(bv):
        assert bv.is_bv_value()
        return int(bv.dump()[2:], 2)

    @staticmethod
    def get_clean_solver():
        print('WARNING: resetting all assumptions')
        Bitwuzla.reset_assumptions()
        return Bitwuzla

    @staticmethod
    def is_sat():
        return Bitwuzla.BW.check_sat() == pybitwuzla.Result.SAT

    @staticmethod
    def is_unsat():
        return Bitwuzla.BW.check_sat() == pybitwuzla.Result.UNSAT

    @staticmethod
    def is_formula_sat(formula):
        Bitwuzla.push()
        Bitwuzla.add_assumption(formula)
        sat = Bitwuzla.is_sat()
        Bitwuzla.pop()

        return sat

    @staticmethod
    def is_formula_unsat(formula):
        Bitwuzla.push()
        Bitwuzla.add_assumption(formula)
        sat = Bitwuzla.is_unsat()
        Bitwuzla.pop()

        return sat

    @staticmethod
    def is_formula_true(formula):
        return Bitwuzla.is_formula_unsat(Bitwuzla.Not(formula))

    @staticmethod
    def is_formula_false(formula):
        return Bitwuzla.is_formula_unsat(formula)

    @staticmethod
    def push():
        Bitwuzla.BW.push()

    @staticmethod
    def pop():
        Bitwuzla.BW.pop()

    @staticmethod
    def add_assumption(formula):
        # assumptions are discarded after each call to .check_sat
        Bitwuzla.BW.assume_formula(formula)

    @staticmethod
    def add_assumptions(formulas):
        Bitwuzla.BW.assume_formula(*formulas)

    @staticmethod
    def reset_assumptions():
        Bitwuzla.BW.reset_assumptions()

    @staticmethod
    def fixate_assumptions():
        Bitwuzla.BW.fixate_assumptions()

    @staticmethod
    def simplify():
        Bitwuzla.BW.simplify()

    @staticmethod
    def Array(symbol, index_sort, value_sort):
        return Bitwuzla.BW.mk_const(Bitwuzla.BW.mk_array_sort(index_sort, value_sort), symbol=symbol)

    @staticmethod
    def ConstArray(symbol, index_sort, value_sort, default):
        res = Bitwuzla.BW.mk_const_array(Bitwuzla.BW.mk_array_sort(index_sort, value_sort), default)
        res.set_symbol(symbol)
        return res

    # CONDITIONAL OPERATIONS

    @staticmethod
    def If(cond, value_if_true, value_if_false):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.ITE, [cond, value_if_true, value_if_false])

    # BOOLEAN OPERATIONS

    @staticmethod
    def Equal(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.EQUAL, [a, b])

    @staticmethod
    def NotEqual(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.DISTINCT, [a, b])

    @staticmethod
    def Or(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.OR, [a, b])

    @staticmethod
    def And(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.AND, [a, b])

    @staticmethod
    def Not(a):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.NOT, [a])

    # BV OPERATIONS

    @staticmethod
    def BV_Extract(start, end, bv):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_EXTRACT, [bv], [end, start])

    @staticmethod
    def BV_Concat(terms):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_CONCAT, terms)

    @staticmethod
    def BV_Add(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_ADD, [a, b])

    @staticmethod
    def BV_Sub(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_SUB, [a, b])

    @staticmethod
    def BV_Mul(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_MUL, [a, b])

    @staticmethod
    def BV_UDiv(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_UDIV, [a, b])

    @staticmethod
    def BV_SDiv(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_SDIV, [a, b])

    @staticmethod
    def BV_SMod(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_SMOD, [a, b])

    @staticmethod
    def BV_SRem(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_SREM, [a, b])

    @staticmethod
    def BV_URem(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_UREM, [a, b])

    @staticmethod
    def BV_Sign_Extend(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_SIGN_EXTEND, [a], [b])

    @staticmethod
    def BV_Zero_Extend(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_ZERO_EXTEND, [a], [b])

    @staticmethod
    def BV_UGE(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_UGE, [a, b])

    @staticmethod
    def BV_ULE(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_ULE, [a, b])

    @staticmethod
    def BV_UGT(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_UGT, [a, b])

    @staticmethod
    def BV_ULT(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_ULT, [a, b])

    @staticmethod
    def BV_SGE(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_SGE, [a, b])

    @staticmethod
    def BV_SLE(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_SLE, [a, b])

    @staticmethod
    def BV_SGT(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_SGT, [a, b])

    @staticmethod
    def BV_SLT(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_SLT, [a, b])

    @staticmethod
    def BV_And(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_AND, [a, b])

    @staticmethod
    def BV_Or(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_OR, [a, b])

    @staticmethod
    def BV_Xor(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_XOR, [a, b])

    @staticmethod
    def BV_Not(a):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_NOT, [a])

    @staticmethod
    def BV_Shl(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_SHL, [a, b])

    @staticmethod
    def BV_Shr(a, b):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.BV_SHR, [a, b])

    # ARRAY OPERATIONS

    @staticmethod
    def Array_Store(arr, index, elem):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.ARRAY_STORE, [arr, index, elem])

    @staticmethod
    def Array_Select(arr, index):
        return Bitwuzla.BW.mk_term(pybitwuzla.Kind.ARRAY_SELECT, [arr, index])
