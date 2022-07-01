from SEtaac.utils.solver.base import Solver

def set_solver(solver):
    global SOLVER
    SOLVER = solver


def get_clean_solver():
    global SOLVER
    if SOLVER is Solver:
        raise Exception("Please set a solver first (e.g., set_solver(Bitwuzla))")
    return SOLVER.get_clean_solver()


def ctx_or_symbolic(v, ctx, xid):
    return ctx.get(v, BVS(f'{v}_{xid}', 256))


# TYPES


def BVSort(width):
    return SOLVER.BVSort(width)


def BVV(value, width):
    return SOLVER.BVV(value, width)


def BVS(symbol, width):
    return SOLVER.BVS(symbol, width)


def Array(symbol, index_sort, value_sort):
    return SOLVER.Array(symbol, index_sort, value_sort)


def ConstArray(symbol, index_sort, value_sort, default):
    return SOLVER.ConstArray(symbol, index_sort, value_sort, default)


# CONDITIONAL OPERATIONS


def If(cond, value_if_true, value_if_false):
    return SOLVER.If(cond, value_if_true, value_if_false)


# BOOLEAN OPERATIONS


def Equal(a, b):
    return SOLVER.Equal(a, b)


def NotEqual(a, b):
    return SOLVER.NotEqual(a, b)


def Or(a, b):
    return SOLVER.Or(a, b)


def And(a, b):
    return SOLVER.And(a, b)


def Not(a):
    return SOLVER.Not(a)


# BV OPERATIONS


def bv_unsigned_value(bv):
    return SOLVER.bv_unsigned_value(bv)


def is_concrete(bv):
    return SOLVER.is_concrete(bv)


def BV_Extract(start, end, bv):
    return SOLVER.BV_Extract(start, end, bv)


def BV_Concat(terms):
    return SOLVER.BV_Concat(terms)


def BV_Add(a, b):
    return SOLVER.BV_Add(a, b)


def BV_Sub(a, b):
    return SOLVER.BV_Sub(a, b)


def BV_Mul(a, b):
    return SOLVER.BV_Mul(a, b)


def BV_UDiv(a, b):
    return SOLVER.BV_UDiv(a, b)


def BV_SDiv(a, b):
    return SOLVER.BV_SDiv(a, b)


def BV_SMod(a, b):
    return SOLVER.BV_SMod(a, b)


def BV_SRem(a, b):
    return SOLVER.BV_SRem(a, b)


def BV_URem(a, b):
    return SOLVER.BV_URem(a, b)


def BV_Sign_Extend(a, b):
    return SOLVER.BV_Sign_Extend(a, b)


def BV_Zero_Extend(a, b):
    return SOLVER.BV_Zero_Extend(a, b)


def BV_UGE(a, b):
    return SOLVER.BV_UGE(a, b)


def BV_ULE(a, b):
    return SOLVER.BV_ULE(a, b)


def BV_UGT(a, b):
    return SOLVER.BV_UGT(a, b)


def BV_ULT(a, b):
    return SOLVER.BV_ULT(a, b)


def BV_SGE(a, b):
    return SOLVER.BV_SGE(a, b)


def BV_SLE(a, b):
    return SOLVER.BV_SLE(a, b)


def BV_SGT(a, b):
    return SOLVER.BV_SGT(a, b)


def BV_SLT(a, b):
    return SOLVER.BV_SLT(a, b)


def BV_And(a, b):
    return SOLVER.BV_And(a, b)


def BV_Or(a, b):
    return SOLVER.BV_Or(a, b)


def BV_Xor(a, b):
    return SOLVER.BV_Xor(a, b)


def BV_Not(a):
    return SOLVER.BV_Not(a)


def BV_Shl(a, b):
    return SOLVER.BV_Shl(a, b)


def BV_Shr(a, b):
    return SOLVER.BV_Shr(a, b)


# ARRAY OPERATIONS


def Array_Store(arr, index, elem):
    return SOLVER.Array_Store(arr, index, elem)


def Array_Select(arr, index):
    return SOLVER.Array_Select(arr, index)
