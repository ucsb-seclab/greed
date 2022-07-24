from typing import List

import yices

from SEtaac.utils.solver.base import Solver


def resets_sat_status(func):
    def wrap(self, *args, **kwargs):
        # reset internal sat_status after calling the target method
        res = func(self, *args, **kwargs)
        self._sat_status = None
        return res
    return wrap


class YicesTerm:
    def __init__(self, yices_id, name=None, value=None):
        self.id = yices_id
        self.name = name
        self.value = value

    def __str__(self):
        classname = self.__class__.__name__
        name_str = f" name:{self.name}" if self.name is not None else ""
        value_str = f" value:{self.value}" if self.value is not None else ""
        return f"{classname} (#{self.id}){name_str}{value_str}"

    def __repr__(self):
        return str(self)

    def __int__(self):
        return self.id


class YicesTermBool(YicesTerm):
    pass


class YicesTermBV(YicesTerm):
    pass


class YicesTermArray(YicesTerm):
    pass


class YicesType:
    def __init__(self, yices_id, name):
        self.id = yices_id
        self.name = name

    def __int__(self):
        return self.id

    def __str__(self):
        return f"YicesType {self.name} (#{self.id})"

    def __repr__(self):
        return str(self)


class YicesTypeBV(YicesType):
    pass


class YicesTypeArray(YicesType):
    pass


class Yices2(Solver):
    """
    This is a singleton class
    """

    def __init__(self):
        cfg = yices.Config()
        cfg.default_config_for_logic('QF_ABV')
        self.solver = yices.Context(cfg)

        self.BVSort_cache = dict()
        self.BVV_cache = dict()
        self.BVS_cache = dict()

        self._sat_status = None

    def BVSort(self, width: int) -> YicesTypeBV:
        assert isinstance(width, int)
        if width not in self.BVSort_cache:
            yices_id = yices.Types.bv_type(width)
            self.BVSort_cache[width] = YicesTypeBV(yices_id=yices_id, name=f"BV{width}")
        return self.BVSort_cache[width]

    def BVV(self, value: int, width: int) -> YicesTermBV:
        assert isinstance(value, int)
        assert isinstance(width, int)
        if (value, width) not in self.BVV_cache:
            # IMPORTANT: bvconst_integer under the hood calls yices_bvconst_int64 and overflows so we cannot use it
            # yices_id = yices.Terms.bvconst_integer(width, value)
            yices_id = yices.Terms.parse_bvbin(format(value, '#0258b')[2:])
            self.BVV_cache[(value, width)] = YicesTermBV(yices_id=yices_id, value=value)
        return self.BVV_cache[(value, width)]

    def BVS(self, symbol: str, width: int) -> YicesTermBV:
        assert isinstance(symbol, str)
        assert isinstance(width, int)
        if (symbol, width) not in self.BVS_cache:
            yices_id = yices.Terms.new_uninterpreted_term(self.BVSort(width), name=symbol)
            self.BVS_cache[(symbol, width)] = YicesTermBV(yices_id=yices_id, name=symbol)
        return self.BVS_cache[(symbol, width)]

    def bv_unsigned_value(self, bv):
        assert self.is_concrete(bv), "Invalid bv_unsigned_value of non constant bitvector"

        # works, but yices.Terms.bv_const_value(bv) could be a cleaner (though slower) option
        res_str = yices.Terms.to_string(bv, width=-1)
        return int(res_str[2:], 2)

    def is_concrete(self, bv):
        return yices.Terms.constructor(bv) == yices.Constructor.BV_CONSTANT

    def is_sat(self) -> bool:
        # cache the last check_sat result so that we can check it when querying the solver's model, and we don't need
        # to call check_sat (and thus generate a new and possibly inconsistent model) every time we need to eval a term
        self._sat_status = self.solver.check_context()
        return self._sat_status == yices.Status.SAT

    def is_unsat(self) -> bool:
        # cache the last check_sat result so that we can check it when querying the solver's model, and we don't need
        # to call check_sat (and thus generate a new and possibly inconsistent model) every time we need to eval a term
        self._sat_status = self.solver.check_context()
        return self._sat_status == yices.Status.UNSAT

    @resets_sat_status
    def is_formula_sat(self, formula: YicesTerm) -> bool:
        return self.solver.check_context_with_assumptions(None, [formula]) == yices.Status.SAT

    @resets_sat_status
    def is_formula_unsat(self, formula: YicesTerm) -> bool:
        return self.solver.check_context_with_assumptions(None, [formula]) == yices.Status.UNSAT

    @resets_sat_status
    def is_formula_true(self, formula: YicesTerm) -> bool:
        return self.is_formula_unsat(self.Not(formula))

    @resets_sat_status
    def is_formula_false(self, formula: YicesTerm) -> bool:
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
        self.solver.assert_formulas(formulas)

    def Array(self, symbol, index_sort: YicesTypeBV, value_sort: YicesTypeBV) -> YicesTermArray:
        assert isinstance(index_sort, YicesTypeBV)
        assert isinstance(value_sort, YicesTypeBV)
        # WARNING: in yices apparently arrays are functions
        array_type = yices.Types.new_function_type([index_sort], value_sort)
        yices_id = yices.Terms.new_variable(array_type, name=symbol)
        return YicesTermArray(yices_id=yices_id, name=symbol)

    # CONDITIONAL OPERATIONS

    def If(self, cond: YicesTermBool, value_if_true: YicesTerm, value_if_false: YicesTerm) -> YicesTerm:
        assert isinstance(cond, YicesTermBool)
        assert isinstance(value_if_true, YicesTerm)
        assert isinstance(value_if_false, YicesTerm)
        assert type(value_if_true) == type(value_if_false)
        yices_id = yices.Terms.ite(cond, value_if_true, value_if_false)
        return value_if_true.__class__(yices_id=yices_id)

    # BOOLEAN OPERATIONS

    def Equal(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bveq_atom(a, b)
        return YicesTermBool(yices_id=yices_id)

    def NotEqual(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvneq_atom(a, b)
        return YicesTermBool(yices_id=yices_id)

    # def Or(self, *terms: List[YicesTermBool]) -> YicesTermBool:
    #     for term in terms:
    #         assert isinstance(term, YicesTermBool)
    #     return yices.Terms.bvor(terms)
    #
    # def And(self, *terms: List[YicesTermBool]) -> YicesTermBool:
    #     for term in terms:
    #         assert isinstance(term, YicesTermBool)
    #     return yices.Terms.bvand(terms)
    #
    # def Not(self, a: YicesTermBool) -> YicesTermBool:
    #     assert isinstance(a, YicesTermBool)
    #     return yices.Terms.bvnot(a)

    # BV OPERATIONS

    def BV_Extract(self, start: int, end: int, bv: YicesTermBV) -> YicesTermBV:
        assert isinstance(start, int)
        assert isinstance(end, int)
        assert isinstance(bv, YicesTermBV)
        yices_id = yices.Terms.bvextract(bv, start, end)
        return YicesTermBV(yices_id=yices_id)

    # def BV_Concat(self, terms):
    #     return self.solver.mk_term(pybitwuzla.Kind.BV_CONCAT, terms)
    #
    def BV_Add(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvadd(a, b)
        return YicesTermBV(yices_id=yices_id)

    def BV_Sub(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvsub(a, b)
        return YicesTermBV(yices_id=yices_id)

    def BV_Mul(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvmul(a, b)
        return YicesTermBV(yices_id=yices_id)

    def BV_UDiv(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvdiv(a, b)
        return YicesTermBV(yices_id=yices_id)

    def BV_SDiv(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvsdiv(a, b)
        return YicesTermBV(yices_id=yices_id)

    def BV_SMod(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvsmod(a, b)
        return YicesTermBV(yices_id=yices_id)

    def BV_SRem(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvsrem(a, b)
        return YicesTermBV(yices_id=yices_id)

    def BV_URem(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvrem(a, b)
        return YicesTermBV(yices_id=yices_id)

    def BV_Sign_Extend(self, a: YicesTermBV, b: int) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, int)
        yices_id = yices.Terms.sign_extend(a, b)
        return YicesTermBV(yices_id=yices_id)

    def BV_Zero_Extend(self, a: YicesTermBV, b: int) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, int)
        yices_id = yices.Terms.zero_extend(a, b)
        return YicesTermBV(yices_id=yices_id)

    def BV_UGE(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvge_atom(a, b)
        return YicesTermBool(yices_id=yices_id)

    def BV_ULE(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvle_atom(a, b)
        return YicesTermBool(yices_id=yices_id)

    def BV_UGT(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvgt_atom(a, b)
        return YicesTermBool(yices_id=yices_id)

    def BV_ULT(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvlt_atom(a, b)
        return YicesTermBool(yices_id=yices_id)

    def BV_SGE(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvsge_atom(a, b)
        return YicesTermBool(yices_id=yices_id)

    def BV_SLE(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvsle_atom(a, b)
        return YicesTermBool(yices_id=yices_id)

    def BV_SGT(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvsgt_atom(a, b)
        return YicesTermBool(yices_id=yices_id)

    def BV_SLT(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvslt_atom(a, b)
        return YicesTermBool(yices_id=yices_id)

    def BV_And(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvand([a, b])
        return YicesTermBV(yices_id=yices_id)

    def BV_Or(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvor([a, b])
        return YicesTermBV(yices_id=yices_id)

    def BV_Xor(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvxor([a, b])
        return YicesTermBV(yices_id=yices_id)

    def BV_Not(self, a: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        yices_id = yices.Terms.bvnot(a)
        return YicesTermBV(yices_id=yices_id)

    def BV_Shl(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvshl(a, b)
        return YicesTermBV(yices_id=yices_id)

    def BV_Shr(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvlshr(a, b)
        return YicesTermBV(yices_id=yices_id)

    def BV_Sar(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvashr(a, b)
        return YicesTermBV(yices_id=yices_id)

    # ARRAY OPERATIONS

    def Array_Store(self, arr: YicesTermArray, index: YicesTermBV, elem: YicesTermBV) -> YicesTermArray:
        assert isinstance(arr, YicesTermArray)
        assert isinstance(index, YicesTermBV)
        assert isinstance(elem, YicesTermBV)
        # WARNING: in yices apparently arrays are functions
        yices_id = yices.Terms.update(arr, [index], elem)
        return YicesTermArray(yices_id=yices_id)

    def Array_Select(self, arr: YicesTermArray, index: YicesTermBV) -> YicesTermBV:
        assert isinstance(arr, YicesTermArray)
        assert isinstance(index, YicesTermBV)
        yices_id = yices.Terms.application(arr, [index])
        return YicesTermBV(yices_id=yices_id)

    # def eval_one(self, term, cast_to="int"):
    #     if self._sat_status is None:
    #         self._sat_status = self.solver.check_sat()
    #     assert self._sat_status == pybitwuzla.Result.SAT
    #     if cast_to == "int":
    #         return int(self.solver.get_value_str(term))
    #     else:
    #         return self.solver.get_value_str(term)
    #
    # def eval_one_array(self, array, length):
    #     raise Exception("this doesn't work for now because it does not consider the side effects of memory reads")
    #     # if self._sat_status is None:
    #     #     self._sat_status = self.solver.check_sat()
    #     # assert self._sat_status == pybitwuzla.Result.SAT
    #     #
    #     # return [int(self.solver.get_value_str(self.Array_Select(array, self.BVV(i, 256))), 2) for i in range(length)]
