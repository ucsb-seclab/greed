from SEtaac.utils.solver.base import Solver

_SOLVER = Solver()
_num_contexts = 0


def set_solver(solver):
    global _SOLVER
    _SOLVER = solver()


class new_solver_context:
    def __init__(self, state=None):
        self._state = state
        self.solver_context = None

    def __enter__(self):
        global _SOLVER
        global _num_contexts

        if _num_contexts != 0:
            raise Exception("Illegal nested context detected")
        _num_contexts += 1

        _SOLVER.push()

        class SolverContext(_SOLVER.__class__):
            def __init__(self, parent):
                self.__parent = parent
                self.__invalid = False

            @property
            def solver(self):
                if self.__invalid:
                    raise Exception("Access to invalid context")
                return self.__parent.solver

            @property
            def BVSort_cache(self):
                if self.__invalid:
                    raise Exception("Access to invalid context")
                return self.__parent.BVSort_cache

            @property
            def BVV_cache(self):
                if self.__invalid:
                    raise Exception("Access to invalid context")
                return self.__parent.BVV_cache

            @property
            def BVS_cache(self):
                if self.__invalid:
                    raise Exception("Access to invalid context")
                return self.__parent.BVS_cache

            def invalidate(self):
                self.__invalid = True

        self.solver_context = SolverContext(_SOLVER)

        if self._state is not None:
            self.solver_context.add_assertions(self._state.constraints)

        return self.solver_context

    def __exit__(self, exc_type, exc_val, exc_tb):
        global _SOLVER
        global _num_contexts

        _num_contexts -= 1

        _SOLVER.pop()

        self.solver_context.invalidate()


def ctx_or_symbolic(v, ctx, xid):
    if v not in ctx:
        ctx[v] = BVS(f'{v}_{xid}', 256)
    return ctx[v]


# GENERIC OPS


def substitute_terms(formula, substitute_map):
    return _SOLVER.substitute_terms(formula, substitute_map)


# TYPES


def BVSort(width):
    return _SOLVER.BVSort(width)


def BVV(value, width):
    return _SOLVER.BVV(value, width)


def BVS(symbol, width):
    return _SOLVER.BVS(symbol, width)


def Array(symbol, index_sort, value_sort):
    return _SOLVER.Array(symbol, index_sort, value_sort)


def ConstArray(symbol, index_sort, value_sort, default):
    return _SOLVER.ConstArray(symbol, index_sort, value_sort, default)


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
