import pyboolector
from pyboolector import Boolector

from SEtaac.utils.solver.base import Solver

class Boolector(Solver):
    """
    This is a singleton class, and all methods are static
    """

    BW = Boolector()
    bb = BW.Clone()
    BW.Set_opt(pyboolector.BTOR_OPT_INCREMENTAL, 1)
    BW.Set_opt(pyboolector.BTOR_OPT_MODEL_GEN, 1)

    BVSort_cache = dict()
    BVV_cache = dict()
    BVS_cache = dict()

    @staticmethod
    def BVSort(width):
        if width not in Boolector.BVSort_cache:
            Boolector.BVSort_cache[width] = Boolector.BW.BitVecSort(width)
        return Boolector.BVSort_cache[width]

    @staticmethod
    def BVV(value, width):
        if (value, width) not in Boolector.BVV_cache:
            Boolector.BVV_cache[(value, width)] = Boolector.BW.Const(value, width)
        return Boolector.BVV_cache[(value, width)]

    @staticmethod
    def BVS(symbol, width):
        if (symbol, width) not in Boolector.BVS_cache:
            Boolector.BVS_cache[(symbol, width)] = Boolector.BW.Var(Boolector.BVSort(width), symbol=symbol)
        return Boolector.BVS_cache[(symbol, width)]


    @staticmethod
    def bv_unsigned_value(bv):
        assert bv.bits
        return int(bv.bits, 2)

    @staticmethod
    def is_concrete(bv):
        if type(bv) is pyboolector.BoolectorConstNode:
            return True
        else:
            return False

    @staticmethod
    def is_sat():
        return Boolector.BW.Sat() == Boolector.BW.SAT

    @staticmethod
    def is_unsat():
        return Boolector.BW.Sat() == Boolector.BW.UNSAT

    @staticmethod
    def is_sat_formula(formula):
        Boolector.push()
        Boolector.add_assumption(formula)
        sat = Boolector.is_sat()
        Boolector.pop()

        return sat

    @staticmethod
    def push():
        Boolector.BW.Push()

    @staticmethod
    def pop():
        Boolector.BW.Pop()

    @staticmethod
    def add_assumption(formula):
        # assumptions are discarded after each call to .check_sat
        Boolector.BW.Assume(formula)

    @staticmethod
    def add_assumptions(formulas):
        Boolector.BW.Assume(*formulas)

    @staticmethod
    def reset_assumptions():
        Boolector.BW.Reset_assumptions()

    @staticmethod
    def fixate_assumptions():
        Boolector.BW.Fixate_assumptions()

    @staticmethod
    def simplify():
        Boolector.BW.Simplify()

    @staticmethod
    def get_clean_solver():
        print('WARNING: resetting all assumptions')
        Boolector.reset_assumptions()
        return Boolector

    @staticmethod
    def Array(symbol, index_sort, value_sort):
        return Boolector.BW.Array(Boolector.BW.ArraySort(index_sort, value_sort), symbol=symbol)

    @staticmethod
    def ConstArray(symbol, index_sort, value_sort, default):
        res = Boolector.BW.ConstArray(Boolector.BW.ArraySort(index_sort, value_sort), default)
        res.symbol = symbol
        return res

    # CONDITIONAL OPERATIONS

    @staticmethod
    def If(cond, value_if_true, value_if_false):
        return Boolector.BW.Cond(cond, value_if_true, value_if_false)

    # BOOLEAN OPERATIONS

    #@staticmethod
    #def Equal(a, b):
    #    return Boolector.BW.Eq(a, b)

    #@staticmethod
    #def NotEqual(a, b):
    #    return Boolector.BW.Ne(a, b)

    #@staticmethod
    #def Or(a, b):
    #    return Boolector.BW.Or(a, b)

    #@staticmethod
    #def And(a, b):
    #    return Boolector.BW.And(a, b)

    #@staticmethod
    #def Not(a):
    #    return Boolector.BW.Not(a)

    # BV OPERATIONS

    @staticmethod
    def Equal(a, b):
        return Boolector.BW.Eq(a, b)

    @staticmethod
    def NotEqual(a, b):
        return Boolector.BW.Ne(a, b)

    @staticmethod
    def BV_Extract(start, end, bv):
        return Boolector.BW.Slice(bv, end, start)

    @staticmethod
    def BV_Concat(terms):
        res = Boolector.BW.Concat(terms[0], terms[1])
        for i in range(2, len(terms)):
            res = Boolector.BW.Concat(res, terms[i])
        return res

    @staticmethod
    def BV_Add(a, b):
        return Boolector.BW.Add(a, b)

    @staticmethod
    def BV_Sub(a, b):
        return Boolector.BW.Sub(a, b)

    @staticmethod
    def BV_Mul(a, b):
        return Boolector.BW.Mul(a, b)

    @staticmethod
    def BV_UDiv(a, b):
        return Boolector.BW.Udiv(a, b)

    @staticmethod
    def BV_SDiv(a, b):
        return Boolector.BW.Sdiv(a, b)

    @staticmethod
    def BV_SMod(a, b):
        return Boolector.BW.Smod(a, b)

    @staticmethod
    def BV_SRem(a, b):
        return Boolector.BW.Srem(a, b)

    @staticmethod
    def BV_URem(a, b):
        return Boolector.BW.Urem(a, b)

    @staticmethod
    def BV_Sign_Extend(a, b):
        return Boolector.BW.Sext(a, b)

    @staticmethod
    def BV_Zero_Extend(a, b):
        return Boolector.BW.Uext(a, b)

    @staticmethod
    def BV_UGE(a, b):
        return Boolector.BW.Ugte(a, b)

    @staticmethod
    def BV_ULE(a, b):
        return Boolector.BW.Ulte(a, b)

    @staticmethod
    def BV_UGT(a, b):
        return Boolector.BW.Ugt(a, b)

    @staticmethod
    def BV_ULT(a, b):
        return Boolector.BW.Ult(a, b)

    @staticmethod
    def BV_SGE(a, b):
        return Boolector.BW.Sgte(a, b)

    @staticmethod
    def BV_SLE(a, b):
        return Boolector.BW.Slte(a, b)

    @staticmethod
    def BV_SGT(a, b):
        return Boolector.BW.Sgt(a, b)

    @staticmethod
    def BV_SLT(a, b):
        return Boolector.BW.Slt(a, b)

    @staticmethod
    def BV_And(a, b):
        return Boolector.BW.And(a, b)

    @staticmethod
    def BV_Or(a, b):
        return Boolector.BW.Or(a, b)

    @staticmethod
    def BV_Xor(a, b):
        return Boolector.BW.Xor(a, b)

    @staticmethod
    def BV_Not(a):
        return Boolector.BW.Not(a)

    @staticmethod
    def BV_Shl(a, b):
        return Boolector.BW.Sll(a, b)

    @staticmethod
    def BV_Shr(a, b):
        return Boolector.BW.Srl(a, b)

    # ARRAY OPERATIONS

    @staticmethod
    def Array_Store(arr, index, elem):
        return Boolector.BW.Write(arr, index, elem)

    @staticmethod
    def Array_Select(arr, index):
        return Boolector.BW.Read(arr, index)

    @staticmethod
    def eval_one_array(array, length):
        Boolector.is_sat()
        return [int(Boolector.Array_Select(array, Boolector.BVV(i, 256)).assignment, 2) for i in
                range(length)]
