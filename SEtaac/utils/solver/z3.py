import z3

from SEtaac.utils.solver.base import Solver

def simplify_result(func):
    def wrapper(*args, **kwargs):
        res = func(*args, **kwargs)
        return z3.simplify(res)
    return wrapper

class Z3(Solver):
    """
    This is a singleton class, and all methods are static
    """

    def __init__(self):
        self.solver = z3.SolverFor('QF_ABV')
        self.BVSort_cache = dict()
        self.BVV_cache = dict()
        self.BVS_cache = dict()

    def BVSort(self, width):
        if width not in self.BVSort_cache:
            self.BVSort_cache[width] = z3.BitVecSort(width)
        return self.BVSort_cache[width]

    def BVV(self, value, width):
        if (value, width) not in self.BVV_cache:
            self.BVV_cache[(value, width)] = z3.BitVecVal(value, width)
        return self.BVV_cache[(value, width)]

    def BVS(self, symbol, width):
        if (symbol, width) not in self.BVS_cache:
            self.BVS_cache[(symbol, width)] = z3.BitVec(symbol, width)
        return self.BVS_cache[(symbol, width)]

    def bv_unsigned_value(self, bv):
        return int(bv.as_binary_string(), 2)

    def is_concrete(self, bv):
        return z3.is_bv_value(bv)

    def is_sat(self, ):
        return self.solver.check() == z3.sat

    def is_unsat(self, ):
        return self.solver.check() == z3.unsat

    def is_formula_sat(self, formula):
        self.push()
        self.add_assertion(formula)
        sat = self.is_sat()
        self.pop()

        return sat
    
    def bv_size(self, bv):
        return bv.size()

    def push(self, ):
        # Create a Z3 backtracking point
        self.solver.push()

    def pop(self, ):
        # Remove a Z3 backtracking point
        self.solver.pop()

    def add_assertion(self, formula):
        self.solver.add(formula)

    def add_assertions(self, formulas):
        self.solver.add(*formulas)

    def add_assumption(self, formula):
        raise Exception

    def add_assumptions(self, formulas):
        raise Exception

    def reset_assumptions(self, ):
        raise Exception

    def fixate_assumptions(self, ):
        raise Exception

    def simplify(self, formula):
        return z3.simplify(formula)

    def new_solver_context(self, ):
        return Z3

    def Array(self, symbol, index_sort, value_sort):
        return z3.Array(symbol, index_sort, value_sort)

    def ConstArray(self, symbol, index_sort, value_sort, default):
        raise Exception

    # CONDITIONAL OPERATIONS

    @simplify_result
    def If(self, cond, value_if_true, value_if_false):
        return z3.If(cond, value_if_true, value_if_false)

    # BOOLEAN OPERATIONS

    #def Equal(self, a, b):
    #    return self.solver.mk_term(pybitwuzla.Kind.EQUAL, [a, b])

    #def NotEqual(self, a, b):
    #    return self.solver.mk_term(pybitwuzla.Kind.DISTINCT, [a, b])

    def Or(self, *terms):
        return z3.Or(*terms)

    def And(self, *terms):
        return z3.And(*terms)

    def Not(self, term):
        return z3.Not(term)

    # BV OPERATIONS

    @simplify_result
    def Equal(self, a, b):
        return z3.BitVecRef.__eq__(a,b)
    
    @simplify_result
    def NotEqual(self, a, b):
        return z3.BitVecRef.__ne__(a,b)

    @simplify_result
    def BV_Extract(self, start, end, bv):
        # Z3 extract is (start_offset, length, symbol)
        return z3.Extract(end, start, bv)

    @simplify_result
    def BV_Concat(self, terms):
        res = z3.Concat(terms[0], terms[1])
        for i in range(2, len(terms)):
            res = z3.Concat(res, terms[i])
        return res

    @simplify_result
    def BV_Add(self, a, b):
        return z3.BitVecRef.__add__(a,b)

    @simplify_result
    def BV_Sub(self, a, b):
        return z3.BitVecRef.__sub__(a,b)

    @simplify_result
    def BV_Mul(self, a, b):
        return z3.BitVecRef.__mul__(a,b)

    @simplify_result
    def BV_UDiv(self, a, b):
        return z3.UDiv(a, b)

    @simplify_result
    def BV_SDiv(self, a, b):
        return z3.BitVecRef.__div__(a,b)

    @simplify_result
    def BV_SMod(self, a, b):
        return z3.BitVecRef.__mod__(a,b)

    @simplify_result
    def BV_SRem(self, a, b):
        return z3.SRem(a,b)

    @simplify_result
    def BV_URem(self, a, b):
        return z3.URem(a, b)

    @simplify_result
    def BV_Sign_Extend(self, a, b):
        return z3.SignExt(b,a)

    @simplify_result
    def BV_Zero_Extend(self, a, b):
        return z3.ZeroExt(b,a)

    @simplify_result
    def BV_UGE(self, a, b):
        return z3.UGE(a, b)

    @simplify_result
    def BV_ULE(self, a, b):
        return z3.ULE(a, b)

    @simplify_result
    def BV_UGT(self, a, b):
        return z3.UGT(a, b)

    @simplify_result
    def BV_ULT(self, a, b):
        return z3.ULT(a, b)

    @simplify_result
    def BV_SGE(self, a, b):
        return z3.BitVecRef.__ge__(a,b)

    @simplify_result
    def BV_SLE(self, a, b):
        return z3.BitVecRef.__le__(a,b)

    @simplify_result
    def BV_SGT(self, a, b):
        return z3.BitVecRef.__gt__(a,b)

    @simplify_result
    def BV_SLT(self, a, b):
        return z3.BitVecRef.__lt__(a,b)

    @simplify_result
    def BV_And(self, a, b):
        return z3.BitVecRef.__and__(a,b)

    @simplify_result
    def BV_Or(self, a, b):
        return z3.BitVecRef.__or__(a,b)

    @simplify_result
    def BV_Xor(self, a, b):
        return z3.BitVecRef.__xor__(a,b)

    @simplify_result
    def BV_Not(self, a):
        return z3.BitVecRef.__invert__(a)

    @simplify_result
    def BV_Shl(self, a, b):
        return z3.BitVecRef.__lshift__(a,b)

    @simplify_result
    def BV_Shr(self, a, b):
        return z3.BitVecRef.__rshift__(a,b)

    # ARRAY OPERATIONS

    def Array_Store(self, arr, index, elem):
        return z3.Store(arr, index, elem)

    def Array_Select(self, arr, index):
        return z3.Select(arr, index)

    def eval_one_array(self, array, length):
        self.is_sat()
        return [int(self.Array_Select(array, self.BVV(i, 256)).assignment, 2) for i in
                range(length)]
