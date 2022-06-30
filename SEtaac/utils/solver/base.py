class Solver:
    """
    This is a singleton class, and all methods are static
    """

    @staticmethod
    def BVSort(width):
        raise Exception("Not implemented")

    @staticmethod
    def BVV(value, width):
        raise Exception("Not implemented")

    @staticmethod
    def BVS(symbol, width):
        raise Exception("Not implemented")

    @staticmethod
    def bv_unsigned_value(bv):
        raise Exception("Not implemented")

    @staticmethod
    def get_clean_solver():
        raise Exception("Not implemented")

    @staticmethod
    def is_sat():
        raise Exception("Not implemented")

    @staticmethod
    def is_unsat():
        raise Exception("Not implemented")

    @staticmethod
    def is_formula_sat(formula):
        raise Exception("Not implemented")

    @staticmethod
    def is_formula_unsat(formula):
        raise Exception("Not implemented")

    @staticmethod
    def is_formula_true(formula):
        raise Exception("Not implemented")

    @staticmethod
    def is_formula_false(formula):
        raise Exception("Not implemented")

    @staticmethod
    def push():
        raise Exception("Not implemented")

    @staticmethod
    def pop():
        raise Exception("Not implemented")

    @staticmethod
    def add_assumption(formula):
        raise Exception("Not implemented")

    @staticmethod
    def add_assumptions(formulas):
        raise Exception("Not implemented")

    @staticmethod
    def reset_assumptions():
        raise Exception("Not implemented")

    @staticmethod
    def fixate_assumptions():
        raise Exception("Not implemented")

    @staticmethod
    def simplify():
        raise Exception("Not implemented")

    @staticmethod
    def Array(symbol, index_sort, value_sort):
        raise Exception("Not implemented")

    @staticmethod
    def ConstArray(symbol, index_sort, value_sort, default):
        raise Exception("Not implemented")

    @staticmethod
    def If(cond, value_if_true, value_if_false):
        raise Exception("Not implemented")

    @staticmethod
    def Equal(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def NotEqual(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def Or(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def And(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def Not(a):
        raise Exception("Not implemented")

    @staticmethod
    def BV_Extract(start, end, bv):
        raise Exception("Not implemented")

    @staticmethod
    def BV_Concat(terms):
        raise Exception("Not implemented")

    @staticmethod
    def BV_Add(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_Sub(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_Mul(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_UDiv(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_SDiv(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_SMod(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_SRem(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_URem(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_Sign_Extend(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_Zero_Extend(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_UGE(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_ULE(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_UGT(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_ULT(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_SGE(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_SLE(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_SGT(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_SLT(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_And(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_Or(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_Xor(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_Not(a):
        raise Exception("Not implemented")

    @staticmethod
    def BV_Shl(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def BV_Shr(a, b):
        raise Exception("Not implemented")

    @staticmethod
    def Array_Store(arr, index, elem):
        raise Exception("Not implemented")

    @staticmethod
    def Array_Select(arr, index):
        raise Exception("Not implemented")