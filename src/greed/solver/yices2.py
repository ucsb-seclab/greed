import re
from typing import List

import yices

from greed.solver import Solver

"""
Solver interface implementation for Yices2, refer to the Solver interface for documentation.
"""

class YicesTerm:
    def __init__(self, yices_id, operator=None, children=None, name=None, value=None):
        self.id = yices_id
        self.name = name
        self._value = value
        self.children = children if children else []
        self.num_children = len(self.children)
        self.operator = operator
        self.is_simplified = False

    @property
    def value(self):
        if self._value is not None:
            return self._value
        elif yices.Terms.constructor(self.id) == yices.Constructor.BV_CONSTANT:
            res_str = yices.Terms.to_string(self.id, width=-1)
            self._value = int(res_str[2:], 2)

            return self._value
        else:
            # raise Exception(f'Symbolic term has no .value')
            return None

    def dump(self, pp=False):
        _dump = yices.Terms.to_string(self.id, width=-1, height=-1, offset=0)
        if pp is True:
            for match in re.findall(r'0b\d*', _dump):
                _dump = _dump.replace(match, str(int(match[2:], 2)))
        return _dump

    def pp(self):
        if self.value is not None:
            return self.value
        elif self.name is not None:
            return self.name
        else:
            return f"<SYMBOL #{self.id}>"

    def __str__(self):
        operator = self.operator
        name_str = f" name:{self.name}" if self.name is not None else ""
        value_str = f" value:{hex(self.value)}" if self.value is not None else ""
        return f"(#{self.id}) {operator}{name_str}{value_str}"

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
    @property
    def bitsize(self):
        return yices.Terms.bitsize(self.id)


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
    Backend for Yices2

    For the list of options see here.
    https://github.com/SRI-CSL/yices2/blob/bc50bebdc3aabb161328bbfc234a10da6dd3d5c4/doc/sphinx/source/context-operations.rst

    self.solver.enable_option("var-elim")
    self.solver.enable_option("arith-elim")
    self.solver.enable_option("flatten")
    self.solver.enable_option("assert-ite-bounds")
    self.solver.enable_option("eager-arith-lemmas")
    self.solver.enable_option("keep-ite")
    self.solver.enable_option("bvarith-elim")
    self.solver.enable_option("break-symmetries")

    cfg.set_config("arith-solver", 'simplex')
    """

    def __init__(self):
        cfg = yices.Config()
        cfg.default_config_for_logic('QF_ABV')
        self.solver = yices.Context(cfg)
        self.timed_out = False

    def BVSort(self, width: int) -> YicesTypeBV:
        assert isinstance(width, int), f"Expected type int, got {type(width)}"
        yices_id = yices.Types.bv_type(width)
        return YicesTypeBV(yices_id=yices_id, name=f"BV{width}")

    def BVV(self, value: int, width: int) -> YicesTermBV:
        assert isinstance(value, int), f"Expected type int, got {type(value)}"
        assert isinstance(width, int), f"Expected type int, got {type(width)}"
        # IMPORTANT: bvconst_integer under the hood calls yices_bvconst_int64 and overflows so we cannot use it
        # yices_id = yices.Terms.bvconst_integer(width, value)
        yices_id = yices.Terms.parse_bvbin(format(value % (2**width), f'#0{width+2}b')[2:])
        res = YicesTermBV(operator="bvv", yices_id=yices_id, value=value)
        res.is_simplified = True
        return res

    def BVS(self, symbol: str, width: int) -> YicesTermBV:
        assert isinstance(symbol, str), f"Expected type str, got {type(symbol)}"
        assert isinstance(width, int), f"Expected type int, got {type(width)}"
        # assert yices.Terms.get_by_name(symbol) is None
        yices_id = yices.Terms.new_uninterpreted_term(self.BVSort(width).id, name=symbol)
        return YicesTermBV(operator="bvs", yices_id=yices_id, name=symbol)

    def bv_unsigned_value(self, bv: YicesTermBV) -> int:
        assert isinstance(bv, YicesTermBV), f"Expected type YicesTermBV, got {type(bv)}"
        assert self.is_concrete(bv), "Invalid bv_unsigned_value of non constant bitvector"

        # works, but yices.Terms.bv_const_value(bv) could be a cleaner (though slower) option
        res_str = yices.Terms.to_string(bv.id, width=-1)
        return int(res_str[2:], 2)

    def get_bv_by_name(self, symbol):
        id = yices.Terms.get_by_name(symbol)
        if id is None:
            return None
        else:
            return YicesTermBV(operator="bvs", yices_id=id, name=symbol)

    def is_concrete(self, bv: YicesTermBV) -> bool:
        assert isinstance(bv, YicesTermBV), f"Expected type YicesTermBV, got {type(bv)}"
        return yices.Terms.constructor(bv.id) == yices.Constructor.BV_CONSTANT

    @Solver.solver_timeout
    def is_sat(self) -> bool:
        # cache the last check_sat result so that we can check it when querying the solver's model, and we don't need
        # to call check_sat (and thus generate a new and possibly inconsistent model) every time we need to eval a term
        status = self.solver.check_context()
        return status == yices.Status.SAT

    @Solver.solver_timeout
    def is_unsat(self) -> bool:
        # cache the last check_sat result so that we can check it when querying the solver's model, and we don't need
        # to call check_sat (and thus generate a new and possibly inconsistent model) every time we need to eval a term
        status = self.solver.check_context()
        return status == yices.Status.UNSAT

    @Solver.solver_timeout
    def is_formula_sat(self, formula: YicesTermBool) -> bool:
        assert isinstance(formula, YicesTermBool), f"Expected type YicesTermBool, got {type(formula)}"
        status = self.solver.check_context_with_assumptions(None, [formula.id])
        return status == yices.Status.SAT

    @Solver.solver_timeout
    def are_formulas_sat(self, terms: List[YicesTermBool]) -> bool:
        for term in terms:
            assert isinstance(term, YicesTermBool), f"Expected type YicesTermBool, got {type(term)}"
        status = self.solver.check_context_with_assumptions(None, [term.id for term in terms])
        return status == yices.Status.SAT

    @Solver.solver_timeout
    def is_formula_unsat(self, formula: YicesTermBool) -> bool:
        assert isinstance(formula, YicesTermBool), f"Expected type YicesTermBool, got {type(formula)}"
        status = self.solver.check_context_with_assumptions(None, [formula.id])
        return status == yices.Status.UNSAT

    def is_formula_true(self, formula: YicesTermBool) -> bool:
        assert isinstance(formula, YicesTermBool), f"Expected type YicesTermBool, got {type(formula)}"
        return self.is_formula_unsat(self.Not(formula))

    def is_formula_false(self, formula: YicesTermBool) -> bool:
        assert isinstance(formula, YicesTermBool), f"Expected type YicesTermBool, got {type(formula)}"
        return self.is_formula_unsat(formula)

    def push(self):
        self.solver.push()

    def pop(self):
        self.solver.pop()

    def add_assertion(self, formula: YicesTermBool):
        self.solver.assert_formula(formula.id)

    def add_assertions(self, formulas: List[YicesTermBool]):
        for f in formulas:
            self.add_assertion(f)

    def Array(self, symbol, index_sort: YicesTypeBV, value_sort: YicesTypeBV) -> YicesTermArray:
        assert isinstance(index_sort, YicesTypeBV), f"Expected type YicesTypeBV, got {type(index_sort)}"
        assert isinstance(value_sort, YicesTypeBV), f"Expected type YicesTypeBV, got {type(value_sort)}"
        # WARNING: in yices apparently arrays are functions
        array_type = yices.Types.new_function_type([index_sort.id], value_sort.id)
        yices_id = yices.Terms.new_uninterpreted_term(array_type, name=symbol)
        return YicesTermArray(operator="array", children=[symbol, index_sort, value_sort], yices_id=yices_id, name=symbol)

    # CONDITIONAL OPERATIONS

    def If(self, cond: YicesTermBool, value_if_true: YicesTerm, value_if_false: YicesTerm) -> YicesTerm:
        assert isinstance(cond, YicesTermBool), f"Expected type YicesTermBool, got {type(cond)}"
        assert isinstance(value_if_true, YicesTerm), f"Expected type YicesTerm, got {type(value_if_true)}"
        assert isinstance(value_if_false, YicesTerm), f"Expected type YicesTerm, got {type(value_if_false)}"
        assert type(value_if_true) == type(value_if_false)
        _returntype = value_if_true.__class__
        yices_id = yices.Terms.ite(cond.id, value_if_true.id, value_if_false.id)
        return _returntype(operator="if", children=[cond, value_if_true, value_if_false], yices_id=yices_id)

    # BOOLEAN OPERATIONS

    def Equal(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bveq_atom(a.id, b.id)
        return YicesTermBool(operator="equal", children=[a, b], yices_id=yices_id)

    def NotEqual(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvneq_atom(a.id, b.id)
        return YicesTermBool(operator="not-equal", children=[a, b], yices_id=yices_id)

    def And(self, *terms: YicesTermBool) -> YicesTermBool:
        for term in terms:
            assert isinstance(term, YicesTermBool), f"Expected type YicesTermBool, got {type(term)}"
        yices_id = yices.Terms.yand([term.id for term in terms])
        return YicesTermBool(operator="and", children=[term for term in terms], yices_id=yices_id)

    def Or(self, *terms: YicesTermBool) -> YicesTermBool:
        for term in terms:
            assert isinstance(term, YicesTermBool), f"Expected type YicesTermBool, got {type(term)}"
        yices_id = yices.Terms.yor([term.id for term in terms])
        return YicesTermBool(operator="or", children=[term for term in terms], yices_id=yices_id)

    def Not(self, a: YicesTermBool) -> YicesTermBool:
        assert isinstance(a, YicesTermBool), f"Expected type YicesTermBool, got {type(a)}"
        yices_id = yices.Terms.ynot(a.id)
        return YicesTermBool(operator="not", children=[a], yices_id=yices_id)

    # BV OPERATIONS

    def BV_Extract(self, start: int, end: int, bv: YicesTermBV) -> YicesTermBV:
        assert isinstance(start, int), f"Expected type int, got {type(start)}"
        assert isinstance(end, int), f"Expected type int, got {type(end)}"
        assert isinstance(bv, YicesTermBV), f"Expected type YicesTermBV, got {type(bv)}"
        yices_id = yices.Terms.bvextract(bv.id, start, end)
        return YicesTermBV(operator="bv-extract", children=[start, end, bv], yices_id=yices_id)

    def BV_Concat(self, terms: List[YicesTermBV]) -> YicesTermBV:
        for term in terms:
            assert isinstance(term, YicesTermBV), f"Expected type YicesTermBV, got {type(term)}"
        yices_id = yices.Terms.bvconcat([term.id for term in terms])
        return YicesTermBV(operator="bv-concat", children=[term for term in terms], yices_id=yices_id)

    def BV_Add(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvadd(a.id, b.id)
        return YicesTermBV(operator="bvadd", children=[a, b], yices_id=yices_id)

    def BV_Sub(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvsub(a.id, b.id)
        return YicesTermBV(operator="bvsub", children=[a, b], yices_id=yices_id)

    def BV_Mul(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvmul(a.id, b.id)
        return YicesTermBV(operator="bvmul", children=[a, b], yices_id=yices_id)

    def BV_UDiv(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvdiv(a.id, b.id)
        return YicesTermBV(operator="bvudiv", children=[a, b], yices_id=yices_id)

    def BV_SDiv(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvsdiv(a.id, b.id)
        return YicesTermBV(operator="bvsdiv", children=[a, b], yices_id=yices_id)

    def BV_SMod(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvsmod(a.id, b.id)
        return YicesTermBV(operator="bvsmod", children=[a, b], yices_id=yices_id)

    def BV_SRem(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvsrem(a.id, b.id)
        return YicesTermBV(operator="bvsrem", children=[a, b], yices_id=yices_id)

    def BV_URem(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvrem(a.id, b.id)
        return YicesTermBV(operator="bvurem", children=[a, b], yices_id=yices_id)

    def BV_Sign_Extend(self, a: YicesTermBV, b: int) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, int), f"Expected type int, got {type(b)}"
        yices_id = yices.Terms.sign_extend(a.id, b)
        return YicesTermBV(operator="bvsign-extend", children=[a, b], yices_id=yices_id)

    def BV_Zero_Extend(self, a: YicesTermBV, b: int) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, int), f"Expected type int, got {type(b)}"
        yices_id = yices.Terms.zero_extend(a.id, b)
        return YicesTermBV(operator="bvzero-extend", children=[a, b], yices_id=yices_id)

    def BV_UGE(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvge_atom(a.id, b.id)
        return YicesTermBool(operator="bvuge", children=[a, b], yices_id=yices_id)

    def BV_ULE(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvle_atom(a.id, b.id)
        return YicesTermBool(operator="bvule", children=[a, b], yices_id=yices_id)

    def BV_UGT(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvgt_atom(a.id, b.id)
        return YicesTermBool(operator="bvugt", children=[a, b], yices_id=yices_id)

    def BV_ULT(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvlt_atom(a.id, b.id)
        return YicesTermBool(operator="bvult", children=[a, b], yices_id=yices_id)

    def BV_SGE(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvsge_atom(a.id, b.id)
        return YicesTermBool(operator="bvsge", children=[a, b], yices_id=yices_id)

    def BV_SLE(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvsle_atom(a.id, b.id)
        return YicesTermBool(operator="bvsle", children=[a, b], yices_id=yices_id)

    def BV_SGT(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvsgt_atom(a.id, b.id)
        return YicesTermBool(operator="bvsgt", children=[a, b], yices_id=yices_id)

    def BV_SLT(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBool:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvslt_atom(a.id, b.id)
        return YicesTermBool(operator="bvslt", children=[a, b], yices_id=yices_id)

    def BV_And(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvand([a.id, b.id])
        return YicesTermBV(operator="bvand", children=[a, b], yices_id=yices_id)

    def BV_Or(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvor([a.id, b.id])
        return YicesTermBV(operator="bvor", children=[a, b], yices_id=yices_id)

    def BV_Xor(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvxor([a.id, b.id])
        return YicesTermBV(operator="bvxor", children=[a, b], yices_id=yices_id)

    def BV_Not(self, a: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        yices_id = yices.Terms.bvnot(a.id)
        return YicesTermBV(operator="bvnot", children=[a], yices_id=yices_id)

    def BV_Shl(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvshl(a.id, b.id)
        return YicesTermBV(operator="bvshl", children=[a, b], yices_id=yices_id)

    def BV_Shr(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvlshr(a.id, b.id)
        return YicesTermBV(operator="bvshr", children=[a, b], yices_id=yices_id)

    def BV_Sar(self, a: YicesTermBV, b: YicesTermBV) -> YicesTermBV:
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"
        yices_id = yices.Terms.bvashr(a.id, b.id)
        return YicesTermBV(operator="bvsar", children=[a, b], yices_id=yices_id)

    # ARRAY OPERATIONS

    def Array_Store(self, arr: YicesTermArray, index: YicesTermBV, elem: YicesTermBV) -> YicesTermArray:
        assert isinstance(arr, YicesTermArray), f"Expected type YicesTermArray, got {type(arr)}"
        assert isinstance(index, YicesTermBV), f"Expected type YicesTermBV, got {type(index)}"
        assert isinstance(elem, YicesTermBV), f"Expected type YicesTermBV, got {type(elem)}"
        # WARNING: in yices apparently arrays are functions
        yices_id = yices.Terms.update(arr.id, [index.id], elem.id)
        return YicesTermArray(operator="store", children=[arr, index, elem], yices_id=yices_id)

    def Array_Select(self, arr: YicesTermArray, index: YicesTermBV) -> YicesTermBV:
        assert isinstance(arr, YicesTermArray), f"Expected type YicesTermArray, got {type(arr)}"
        assert isinstance(index, YicesTermBV), f"Expected type YicesTermBV, got {type(index)}"
        yices_id = yices.Terms.application(arr.id, [index.id])
        return YicesTermBV(operator="select", children=[arr, index], yices_id=yices_id)

    def eval(self, term: YicesTerm, raw=False):
        assert self.is_sat(), "Formula is UNSAT"
        model = yices.Model.from_context(self.solver, 1)
        if raw:
            return YicesTermBV(model.get_value_as_term(term.id))
        else:
            return self.bv_unsigned_value(YicesTermBV(model.get_value_as_term(term.id)))

    def copy(self):
        new_solver = Yices2()
        return new_solver
