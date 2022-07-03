import pyboolector

from SEtaac.utils.solver.base import Solver


class Boolector(Solver):
    """
    This is a singleton class, and all methods are static
    """

    def __init__(self):
        # todo: force single instantiation
        self.solver = pyboolector.Boolector()
        self.solver.Set_opt(pyboolector.BTOR_OPT_INCREMENTAL, 1)
        self.solver.Set_opt(pyboolector.BTOR_OPT_MODEL_GEN, 1)
        self.BVSort_cache = dict()
        self.BVV_cache = dict()
        self.BVS_cache = dict()

    def BVSort(self, width):
        if width not in self.BVSort_cache:
            self.BVSort_cache[width] = self.solver.BitVecSort(width)
        return self.BVSort_cache[width]

    def BVV(self, value, width):
        if (value, width) not in self.BVV_cache:
            self.BVV_cache[(value, width)] = self.solver.Const(value, width)
        return self.BVV_cache[(value, width)]

    def BVS(self, symbol, width):
        if (symbol, width) not in self.BVS_cache:
            self.BVS_cache[(symbol, width)] = self.solver.Var(self.BVSort(width), symbol=symbol)
        return self.BVS_cache[(symbol, width)]

    def bv_unsigned_value(self, bv):
        assert bv.bits
        return int(bv.bits, 2)

    def is_concrete(self, bv):
        if type(bv) is pyboolector.BoolectorConstNode:
            return True
        else:
            return False

    def is_sat(self, ):
        return self.solver.Sat() == self.solver.SAT

    def is_unsat(self, ):
        return self.solver.Sat() == self.solver.UNSAT

    def is_sat_formula(self, formula):
        self.push()
        self.add_assertion(formula)
        sat = self.is_sat()
        self.pop()

        return sat

    def push(self, ):
        self.solver.Push()

    def pop(self, ):
        self.solver.Pop()

    def add_assertion(self, formula):
        self.solver.Assert(formula)

    def add_assertions(self, formulas):
        self.solver.Assert(*formulas)

    def add_assumption(self, formula):
        # assumptions are discarded after each call to .check_sat, assertions are not
        self.solver.Assume(formula)

    def add_assumptions(self, formulas):
        self.solver.Assume(*formulas)

    def reset_assumptions(self, ):
        self.solver.Reset_assumptions()

    def fixate_assumptions(self, ):
        self.solver.Fixate_assumptions()

    def simplify(self, ):
        self.solver.Simplify()

    def new_solver_context(self, ):
        print('WARNING: resetting all assumptions')
        self.reset_assumptions()
        return Boolector

    def Array(self, symbol, index_sort, value_sort):
        return self.solver.Array(self.solver.ArraySort(index_sort, value_sort), symbol=symbol)

    def ConstArray(self, symbol, index_sort, value_sort, default):
        res = self.solver.ConstArray(self.solver.ArraySort(index_sort, value_sort), default)
        res.symbol = symbol
        return res

    # CONDITIONAL OPERATIONS

    def If(self, cond, value_if_true, value_if_false):
        return self.solver.Cond(cond, value_if_true, value_if_false)

    # BOOLEAN OPERATIONS

    # def Equalself, (a, b):
    #    return self.solver.Eq(a, b)

    # def NotEqualself, (a, b):
    #    return self.solver.Ne(a, b)

    # def Orself, (a, b):
    #    return self.solver.Or(a, b)

    # def Andself, (a, b):
    #    return self.solver.And(a, b)

    # def Notself, (a):
    #    return self.solver.Not(a)

    # BV OPERATIONS

    def Equal(self, a, b):
        return self.solver.Eq(a, b)

    def NotEqual(self, a, b):
        return self.solver.Ne(a, b)

    def BV_Extract(self, start, end, bv):
        return self.solver.Slice(bv, end, start)

    def BV_Concat(self, terms):
        res = self.solver.Concat(terms[0], terms[1])
        for i in range(2, len(terms)):
            res = self.solver.Concat(res, terms[i])
        return res

    def BV_Add(self, a, b):
        return self.solver.Add(a, b)

    def BV_Sub(self, a, b):
        return self.solver.Sub(a, b)

    def BV_Mul(self, a, b):
        return self.solver.Mul(a, b)

    def BV_UDiv(self, a, b):
        return self.solver.Udiv(a, b)

    def BV_SDiv(self, a, b):
        return self.solver.Sdiv(a, b)

    def BV_SMod(self, a, b):
        return self.solver.Smod(a, b)

    def BV_SRem(self, a, b):
        return self.solver.Srem(a, b)

    def BV_URem(self, a, b):
        return self.solver.Urem(a, b)

    def BV_Sign_Extend(self, a, b):
        return self.solver.Sext(a, b)

    def BV_Zero_Extend(self, a, b):
        return self.solver.Uext(a, b)

    def BV_UGE(self, a, b):
        return self.solver.Ugte(a, b)

    def BV_ULE(self, a, b):
        return self.solver.Ulte(a, b)

    def BV_UGT(self, a, b):
        return self.solver.Ugt(a, b)

    def BV_ULT(self, a, b):
        return self.solver.Ult(a, b)

    def BV_SGE(self, a, b):
        return self.solver.Sgte(a, b)

    def BV_SLE(self, a, b):
        return self.solver.Slte(a, b)

    def BV_SGT(self, a, b):
        return self.solver.Sgt(a, b)

    def BV_SLT(self, a, b):
        return self.solver.Slt(a, b)

    def BV_And(self, a, b):
        return self.solver.And(a, b)

    def BV_Or(self, a, b):
        return self.solver.Or(a, b)

    def BV_Xor(self, a, b):
        return self.solver.Xor(a, b)

    def BV_Not(self, a):
        return self.solver.Not(a)

    def BV_Shl(self, a, b):
        return self.solver.Sll(a, b)

    def BV_Shr(self, a, b):
        return self.solver.Srl(a, b)

    # ARRAY OPERATIONS

    def Array_Store(self, arr, index, elem):
        return self.solver.Write(arr, index, elem)

    def Array_Select(self, arr, index):
        return self.solver.Read(arr, index)

    def eval_one_array(self, array, length):
        self.is_sat()
        return [int(self.Array_Select(array, self.BVV(i, 256)).assignment, 2) for i in
                range(length)]
