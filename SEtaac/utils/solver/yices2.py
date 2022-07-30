from typing import List

import yices

from SEtaac.utils.solver.solver import Solver


class YicesTerm:
    def __init__(self, yices_id, name=None, value=None):
        self.id = yices_id
        self.name = name
        self.value = value

    def dump(self):
        return yices.Terms.to_string(self.id, width=-1, height=-1, offset=0)

    def __str__(self):
        classname = self.__class__.__name__
        name_str = f" name:{self.name}" if self.name is not None else ""
        value_str = f" value:{self.value}" if self.value is not None else ""
        return f"{classname} (#{self.id}){name_str}{value_str}"

    def __repr__(self):
        return str(self)

    def __int__(self):
        return self.id

    def __eq__(self, other):
        return self.id == other.id

    def __hash__(self):
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
        self.assertions = list()

    def BVSort(self, width: int) -> YicesTypeBV:
        assert isinstance(width, int)
        yices_id = yices.Types.bv_type(width)
        return YicesTypeBV(yices_id=yices_id, name=f"BV{width}")

    def BVV(self, value: int, width: int) -> YicesTermBV:
        assert isinstance(value, int)
        assert isinstance(width, int)
        # IMPORTANT: bvconst_integer under the hood calls yices_bvconst_int64 and overflows so we cannot use it
        # yices_id = yices.Terms.bvconst_integer(width, value)
        yices_id = yices.Terms.parse_bvbin(format(value % (2**width), f'#0{width+2}b')[2:])
        return YicesTermBV(yices_id=yices_id, value=value)

    def BVS(self, symbol: str, width: int) -> YicesTermBV:
        assert isinstance(symbol, str)
        assert isinstance(width, int)
        yices_id = yices.Terms.new_uninterpreted_term(self.BVSort(width).id, name=symbol)
        return YicesTermBV(yices_id=yices_id, name=symbol)

    def bv_unsigned_value(self, bv: YicesTermBV) -> int:
        assert isinstance(bv, YicesTermBV)
        assert self.is_concrete(bv), "Invalid bv_unsigned_value of non constant bitvector"

        # works, but yices.Terms.bv_const_value(bv) could be a cleaner (though slower) option
        res_str = yices.Terms.to_string(bv.id, width=-1)
        return int(res_str[2:], 2)

    def is_concrete(self, bv: YicesTermBV) -> bool:
        assert isinstance(bv, YicesTermBV)
        return yices.Terms.constructor(bv.id) == yices.Constructor.BV_CONSTANT

    def is_sat(self) -> bool:
        # cache the last check_sat result so that we can check it when querying the solver's model, and we don't need
        # to call check_sat (and thus generate a new and possibly inconsistent model) every time we need to eval a term
        status = self.solver.check_context()
        return status == yices.Status.SAT

    def is_unsat(self) -> bool:
        # cache the last check_sat result so that we can check it when querying the solver's model, and we don't need
        # to call check_sat (and thus generate a new and possibly inconsistent model) every time we need to eval a term
        status = self.solver.check_context()
        return status == yices.Status.UNSAT

    def is_formula_sat(self, formula: YicesTermBool) -> bool:
        assert isinstance(formula, YicesTermBool)
        return self.solver.check_context_with_assumptions(None, [formula.id]) == yices.Status.SAT

    def is_formula_unsat(self, formula: YicesTermBool) -> bool:
        assert isinstance(formula, YicesTermBool)
        return self.solver.check_context_with_assumptions(None, [formula.id]) == yices.Status.UNSAT

    def is_formula_true(self, formula: YicesTermBool) -> bool:
        assert isinstance(formula, YicesTermBool)
        return self.is_formula_unsat(self.Not(formula).id)

    def is_formula_false(self, formula: YicesTermBool) -> bool:
        assert isinstance(formula, YicesTermBool)
        return self.is_formula_unsat(formula.id)

    def push(self):
        self.solver.push()

    def pop(self):
        self.solver.pop()

    def add_assertion(self, formula: YicesTermBool):
        self.solver.assert_formula(formula.id)
        self.assertions.append(formula)

    def add_assertions(self, formulas: List[YicesTermBool]):
        self.solver.assert_formulas([formula.id for formula in formulas])
        self.assertions += formulas

    def Array(self, symbol, index_sort: YicesTypeBV, value_sort: YicesTypeBV) -> YicesTermArray:
        assert isinstance(index_sort, YicesTypeBV)
        assert isinstance(value_sort, YicesTypeBV)
        # WARNING: in yices apparently arrays are functions
        array_type = yices.Types.new_function_type([index_sort.id], value_sort.id)
        yices_id = yices.Terms.new_uninterpreted_term(array_type, name=symbol)
        return YicesTermArray(yices_id=yices_id, name=symbol)

    # CONDITIONAL OPERATIONS

    def If(self, cond: YicesTermBool, value_if_true: YicesTerm, value_if_false: YicesTerm) -> YicesTerm:
        assert isinstance(cond, YicesTermBool)
        assert isinstance(value_if_true, YicesTerm)
        assert isinstance(value_if_false, YicesTerm)
        assert type(value_if_true) == type(value_if_false)
        yices_id = yices.Terms.ite(cond.id, value_if_true.id, value_if_false.id)
        return value_if_true.__class__(yices_id=yices_id)

    # BOOLEAN OPERATIONS

    def Equal(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bveq_atom(a.id, b.id)
        return YicesTermBool(yices_id=yices_id)

    def NotEqual(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvneq_atom(a.id, b.id)
        return YicesTermBool(yices_id=yices_id)

    def And(self, *terms: List[YicesTermBool]) -> YicesTermBool:
        for term in terms:
            assert isinstance(term, YicesTermBool)
        yices_id = yices.Terms.yand([term.id for term in terms])
        return YicesTermBool(yices_id=yices_id)

    def Or(self, *terms: List[YicesTermBool]) -> YicesTermBool:
        for term in terms:
            assert isinstance(term, YicesTermBool)
        yices_id = yices.Terms.yor([term.id for term in terms])
        return YicesTermBool(yices_id=yices_id)

    def Not(self, a: YicesTermBool) -> YicesTermBool:
        assert isinstance(a, YicesTermBool)
        yices_id = yices.Terms.ynot(a.id)
        return YicesTermBool(yices_id=yices_id)

    # BV OPERATIONS

    def BV_Extract(self, start: int, end: int, bv: YicesTermBV) -> YicesTermBV:
        assert isinstance(start, int)
        assert isinstance(end, int)
        assert isinstance(bv, YicesTermBV)
        yices_id = yices.Terms.bvextract(bv.id, start, end)
        return YicesTermBV(yices_id=yices_id)

    def BV_Concat(self, terms: List[YicesTermBV]) -> YicesTermBV:
        for term in terms:
            assert isinstance(term, YicesTermBV)
        yices_id = yices.Terms.bvconcat([term.id for term in terms])
        return YicesTermBV(yices_id=yices_id)

    def BV_Add(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvadd(a.id, b.id)
        return YicesTermBV(yices_id=yices_id)

    def BV_Sub(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvsub(a.id, b.id)
        return YicesTermBV(yices_id=yices_id)

    def BV_Mul(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvmul(a.id, b.id)
        return YicesTermBV(yices_id=yices_id)

    def BV_UDiv(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvdiv(a.id, b.id)
        return YicesTermBV(yices_id=yices_id)

    def BV_SDiv(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvsdiv(a.id, b.id)
        return YicesTermBV(yices_id=yices_id)

    def BV_SMod(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvsmod(a.id, b.id)
        return YicesTermBV(yices_id=yices_id)

    def BV_SRem(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvsrem(a.id, b.id)
        return YicesTermBV(yices_id=yices_id)

    def BV_URem(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvrem(a.id, b.id)
        return YicesTermBV(yices_id=yices_id)

    def BV_Sign_Extend(self, a: YicesTermBV, b: int) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, int)
        yices_id = yices.Terms.sign_extend(a.id, b)
        return YicesTermBV(yices_id=yices_id)

    def BV_Zero_Extend(self, a: YicesTermBV, b: int) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, int)
        yices_id = yices.Terms.zero_extend(a.id, b)
        return YicesTermBV(yices_id=yices_id)

    def BV_UGE(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvge_atom(a.id, b.id)
        return YicesTermBool(yices_id=yices_id)

    def BV_ULE(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvle_atom(a.id, b.id)
        return YicesTermBool(yices_id=yices_id)

    def BV_UGT(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvgt_atom(a.id, b.id)
        return YicesTermBool(yices_id=yices_id)

    def BV_ULT(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvlt_atom(a.id, b.id)
        return YicesTermBool(yices_id=yices_id)

    def BV_SGE(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvsge_atom(a.id, b.id)
        return YicesTermBool(yices_id=yices_id)

    def BV_SLE(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvsle_atom(a.id, b.id)
        return YicesTermBool(yices_id=yices_id)

    def BV_SGT(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvsgt_atom(a.id, b.id)
        return YicesTermBool(yices_id=yices_id)

    def BV_SLT(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvslt_atom(a.id, b.id)
        return YicesTermBool(yices_id=yices_id)

    def BV_And(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvand([a.id, b.id])
        return YicesTermBV(yices_id=yices_id)

    def BV_Or(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvor([a.id, b.id])
        return YicesTermBV(yices_id=yices_id)

    def BV_Xor(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvxor([a.id, b.id])
        return YicesTermBV(yices_id=yices_id)

    def BV_Not(self, a: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        yices_id = yices.Terms.bvnot(a.id)
        return YicesTermBV(yices_id=yices_id)

    def BV_Shl(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvshl(a.id, b.id)
        return YicesTermBV(yices_id=yices_id)

    def BV_Shr(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvlshr(a.id, b.id)
        return YicesTermBV(yices_id=yices_id)

    def BV_Sar(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV)
        assert isinstance(b, YicesTermBV)
        yices_id = yices.Terms.bvashr(a.id, b.id)
        return YicesTermBV(yices_id=yices_id)

    # ARRAY OPERATIONS

    def Array_Store(self, arr: YicesTermArray, index: YicesTermBV, elem: YicesTermBV) -> YicesTermArray:
        assert isinstance(arr, YicesTermArray)
        assert isinstance(index, YicesTermBV)
        assert isinstance(elem, YicesTermBV)
        # WARNING: in yices apparently arrays are functions
        yices_id = yices.Terms.update(arr.id, [index.id], elem.id)
        return YicesTermArray(yices_id=yices_id)

    def Array_Select(self, arr: YicesTermArray, index: YicesTermBV) -> YicesTermBV:
        assert isinstance(arr, YicesTermArray)
        assert isinstance(index, YicesTermBV)
        yices_id = yices.Terms.application(arr.id, [index.id])
        return YicesTermBV(yices_id=yices_id)

    def eval_one(self, term):
        assert self.is_sat()
        model = yices.Model.from_context(self.solver, 1)

        return YicesTerm(model.get_value_as_term(term)).dump()

    # def eval_one_array(self, array, length):
    #     raise Exception("this doesn't work for now because it does not consider the side effects of memory reads")
    #     assert self.is_sat()
    #     return [int(self.solver.get_value_str(self.Array_Select(array, self.BVV(i, 256))), 2) for i in range(length)]

    def copy(self):
        new_solver = Yices2()
        new_solver.add_assertions(self.assertions)

        return new_solver