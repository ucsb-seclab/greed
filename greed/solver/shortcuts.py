__all__ = [
    "ctx_or_symbolic", "concretize", "BVSort", "BVV", "BVS", "Array", "If", "Equal", "NotEqual", "Or", "And",
    "Not", "bv_unsigned_value", "get_bv_by_name", "is_concrete", "BV_Extract", "BV_Concat", "BV_Add", "BV_Sub",
    "BV_Mul", "BV_UDiv", "BV_SDiv", "BV_SMod", "BV_SRem", "BV_URem", "BV_Sign_Extend", "BV_Zero_Extend",
    "BV_UGE", "BV_ULE", "BV_UGT", "BV_ULT", "BV_SGE", "BV_SLE", "BV_SGT", "BV_SLT", "BV_And", "BV_Or",
    "BV_Xor", "BV_Not", "BV_Shl", "BV_Shr", "BV_Sar", "Array_Store", "Array_Select"
]


from greed import options

if options.SOLVER == options.SOLVER_YICES2:
    from greed.solver.yices2 import Yices2
    _SOLVER = Yices2()
else:
    raise Exception(f"Unsupported solver {options.SOLVER}. Aborting.")


def ctx_or_symbolic(v, ctx, xid, nbits=256):
    if v not in ctx:
        assert nbits <= 256
        ctx[v] = BVS(f'{v}_{xid}', nbits)
        if nbits < 256:
            ctx[v] = BV_Zero_Extend(ctx[v], 256-nbits)
    return ctx[v]


def concretize(state, val, force=False):
    if is_concrete(val):
        return val
    else:
        try:
            val_sol = state.solver.eval(val, raw=True)
            if state.solver.is_formula_true(Equal(val, val_sol)):
                # one possible solution
                return val_sol
            elif force is True:
                # multiple possible solutions
                state.add_constraint(Equal(val, val_sol))
                return val_sol
        except:
            return None


# TYPES


def BVSort(width):
    return _SOLVER.BVSort(width)


def BVV(value, width):
    return _SOLVER.BVV(value, width)


def BVS(symbol, width):
    return _SOLVER.BVS(symbol, width)


def Array(symbol, index_sort, value_sort):
    return _SOLVER.Array(symbol, index_sort, value_sort)


# CONDITIONAL OPERATIONS


def If(cond, value_if_true, value_if_false):
    return _SOLVER.If(cond, value_if_true, value_if_false)


# BOOLEAN OPERATIONS


def Equal(a, b):
    return _SOLVER.Equal(a, b)


def NotEqual(a, b):
    return _SOLVER.NotEqual(a, b)


def Or(*terms):
    return _SOLVER.Or(*terms)


def And(*terms):
    return _SOLVER.And(*terms)


def Not(a):
    return _SOLVER.Not(a)


# BV OPERATIONS


def bv_unsigned_value(bv):
    return _SOLVER.bv_unsigned_value(bv)


def get_bv_by_name(symbol):
    return _SOLVER.get_bv_by_name(symbol)


def is_concrete(bv):
    return _SOLVER.is_concrete(bv)


def BV_Extract(start, end, bv):
    return _SOLVER.BV_Extract(start, end, bv)


def BV_Concat(terms):
    return _SOLVER.BV_Concat(terms)


def BV_Add(a, b):
    return _SOLVER.BV_Add(a, b)


def BV_Sub(a, b):
    return _SOLVER.BV_Sub(a, b)


def BV_Mul(a, b):
    return _SOLVER.BV_Mul(a, b)


def BV_UDiv(a, b):
    return _SOLVER.BV_UDiv(a, b)


def BV_SDiv(a, b):
    return _SOLVER.BV_SDiv(a, b)


def BV_SMod(a, b):
    return _SOLVER.BV_SMod(a, b)


def BV_SRem(a, b):
    return _SOLVER.BV_SRem(a, b)


def BV_URem(a, b):
    return _SOLVER.BV_URem(a, b)


def BV_Sign_Extend(a, b):
    return _SOLVER.BV_Sign_Extend(a, b)


def BV_Zero_Extend(a, b):
    return _SOLVER.BV_Zero_Extend(a, b)


def BV_UGE(a, b):
    return _SOLVER.BV_UGE(a, b)


def BV_ULE(a, b):
    return _SOLVER.BV_ULE(a, b)


def BV_UGT(a, b):
    return _SOLVER.BV_UGT(a, b)


def BV_ULT(a, b):
    return _SOLVER.BV_ULT(a, b)


def BV_SGE(a, b):
    return _SOLVER.BV_SGE(a, b)


def BV_SLE(a, b):
    return _SOLVER.BV_SLE(a, b)


def BV_SGT(a, b):
    return _SOLVER.BV_SGT(a, b)


def BV_SLT(a, b):
    return _SOLVER.BV_SLT(a, b)


def BV_And(a, b):
    return _SOLVER.BV_And(a, b)


def BV_Or(a, b):
    return _SOLVER.BV_Or(a, b)


def BV_Xor(a, b):
    return _SOLVER.BV_Xor(a, b)


def BV_Not(a):
    return _SOLVER.BV_Not(a)


def BV_Shl(a, b):
    return _SOLVER.BV_Shl(a, b)


def BV_Shr(a, b):
    return _SOLVER.BV_Shr(a, b)


def BV_Sar(a, b):
    return _SOLVER.BV_Sar(a, b)


# ARRAY OPERATIONS


def Array_Store(arr, index, elem):
    return _SOLVER.Array_Store(arr, index, elem)


def Array_Select(arr, index):
    return _SOLVER.Array_Select(arr, index)
