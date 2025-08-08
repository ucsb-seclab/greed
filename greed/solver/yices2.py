import re
from typing import List, Optional

import yices

from greed.solver import ArrayTerm, BoolTerm, BVTerm, Solver, Sort, Term

"""
Solver interface implementation for Yices2, refer to the Solver interface for documentation.
"""


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

    _assertions_by_frame: List[List["YicesTermBool"]]

    def __init__(self):
        cfg = yices.Config()
        cfg.default_config_for_logic("QF_ABV")
        self.solver = yices.Context(cfg)
        self.timed_out = False
        self._assertions_by_frame = [[]]

    def BVSort(self, width: int) -> "YicesTypeBV":
        assert isinstance(width, int), f"Expected type int, got {type(width)}"
        return YicesTypeBV(width)

    def BVV(self, value: int, width: int) -> "YicesTermBV":
        assert isinstance(value, int), f"Expected type int, got {type(value)}"
        assert isinstance(width, int), f"Expected type int, got {type(width)}"
        return YicesTermBVV(value, width)

    def BVS(self, symbol: str, width: int) -> "YicesTermBV":
        assert isinstance(symbol, str), f"Expected type str, got {type(symbol)}"
        assert isinstance(width, int), f"Expected type int, got {type(width)}"

        return YicesTermBVS(symbol, width)

    def bv_unsigned_value(self, bv: "YicesTermBV") -> int:
        assert isinstance(bv, YicesTermBV), f"Expected type YicesTermBV, got {type(bv)}"
        assert self.is_concrete(
            bv
        ), "Invalid bv_unsigned_value of non constant bitvector"

        # works, but yices.Terms.bv_const_value(bv) could be a cleaner (though slower) option
        res_str = yices.Terms.to_string(bv.id, width=-1)
        return int(res_str[2:], 2)

    def get_bv_by_name(self, symbol) -> Optional["YicesTermBV"]:
        id = yices.Terms.get_by_name(symbol)
        if id is None:
            return None
        else:
            return YicesTermBVS(symbol, yices.Terms.bitsize(id), yices_id=id)

    def is_concrete(self, bv: "YicesTermBV") -> bool:
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
    def is_formula_sat(self, formula: "YicesTermBool") -> bool:
        assert isinstance(
            formula, YicesTermBool
        ), f"Expected type YicesTermBool, got {type(formula)}"
        status = self.solver.check_context_with_assumptions(None, [formula.id])
        return status == yices.Status.SAT

    @Solver.solver_timeout
    def are_formulas_sat(self, terms: List["YicesTermBool"]) -> bool:
        for term in terms:
            assert isinstance(
                term, YicesTermBool
            ), f"Expected type YicesTermBool, got {type(term)}"
        status = self.solver.check_context_with_assumptions(
            None, [term.id for term in terms]
        )
        return status == yices.Status.SAT

    @Solver.solver_timeout
    def is_formula_unsat(self, formula: "YicesTermBool") -> bool:
        assert isinstance(
            formula, YicesTermBool
        ), f"Expected type YicesTermBool, got {type(formula)}"
        status = self.solver.check_context_with_assumptions(None, [formula.id])
        return status == yices.Status.UNSAT

    def is_formula_true(self, formula: "YicesTermBool") -> bool:
        assert isinstance(
            formula, YicesTermBool
        ), f"Expected type YicesTermBool, got {type(formula)}"
        return self.is_formula_unsat(self.Not(formula))

    def is_formula_false(self, formula: "YicesTermBool") -> bool:
        assert isinstance(
            formula, YicesTermBool
        ), f"Expected type YicesTermBool, got {type(formula)}"
        return self.is_formula_unsat(formula)

    def push(self):
        self._assertions_by_frame.append([])
        self.solver.push()

    def pop(self):
        self._assertions_by_frame.pop()
        self.solver.pop()

    def add_assertion(self, formula: "YicesTermBool"):
        assert isinstance(
            formula, YicesTermBool
        ), f"Expected type YicesTermBool, got {type(formula)}"

        # add the assertion to the current frame
        self._assertions_by_frame[-1].append(formula)
        self.solver.assert_formula(formula.id)

    def add_assertions(self, formulas: List["YicesTermBool"]):
        for f in formulas:
            self.add_assertion(f)

    def Array(
        self, symbol, index_sort: "YicesTypeBV", value_sort: "YicesTypeBV"
    ) -> "YicesTermArray":
        assert isinstance(
            index_sort, YicesTypeBV
        ), f"Expected type YicesTypeBV, got {type(index_sort)}"
        assert isinstance(
            value_sort, YicesTypeBV
        ), f"Expected type YicesTypeBV, got {type(value_sort)}"
        # WARNING: in yices apparently arrays are functions

        return YicesTermArray(symbol, index_sort, value_sort)

    # CONDITIONAL OPERATIONS

    def If(
        self,
        cond: "YicesTermBool",
        value_if_true: "YicesTerm",
        value_if_false: "YicesTerm",
    ) -> "YicesTerm":
        assert isinstance(
            cond, YicesTermBool
        ), f"Expected type YicesTermBool, got {type(cond)}"
        assert isinstance(
            value_if_true, YicesTerm
        ), f"Expected type YicesTerm, got {type(value_if_true)}"
        assert isinstance(
            value_if_false, YicesTerm
        ), f"Expected type YicesTerm, got {type(value_if_false)}"

        if isinstance(value_if_true, YicesTermBV) and isinstance(
            value_if_false, YicesTermBV
        ):
            term_cls = YicesTermBVIf
            assert (
                value_if_true.bitsize == value_if_false.bitsize
            ), "Expected same bit size"
        elif isinstance(value_if_true, YicesTermBool) and isinstance(
            value_if_false, YicesTermBool
        ):
            term_cls = YicesTermBoolIf
            pass
        else:
            raise ValueError("Expected same type")

        return term_cls(cond, value_if_true, value_if_false)

    # BOOLEAN OPERATIONS

    def Equal(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBool":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermEquals(a, b)

    def NotEqual(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBool":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermNotEquals(a, b)

    def And(self, *terms: "YicesTermBool") -> "YicesTermBool":
        for term in terms:
            assert isinstance(
                term, YicesTermBool
            ), f"Expected type YicesTermBool, got {type(term)}"

        return YicesTermAnd(*terms)

    def Or(self, *terms: "YicesTermBool") -> "YicesTermBool":
        for term in terms:
            assert isinstance(
                term, YicesTermBool
            ), f"Expected type YicesTermBool, got {type(term)}"

        return YicesTermOr(*terms)

    def Not(self, a: "YicesTermBool") -> "YicesTermBool":
        assert isinstance(
            a, YicesTermBool
        ), f"Expected type YicesTermBool, got {type(a)}"

        return YicesTermNot(a)

    # BV OPERATIONS

    def BV_Extract(self, start: int, end: int, bv: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(start, int), f"Expected type int, got {type(start)}"
        assert isinstance(end, int), f"Expected type int, got {type(end)}"
        assert isinstance(bv, YicesTermBV), f"Expected type YicesTermBV, got {type(bv)}"

        return YicesTermBVExtract(bv, start, end)

    def BV_Concat(self, terms: List["YicesTermBV"]) -> "YicesTermBV":
        for term in terms:
            assert isinstance(
                term, YicesTermBV
            ), f"Expected type YicesTermBV, got {type(term)}"

        return YicesTermBVConcat(*terms)

    def BV_Add(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVAdd(a, b)

    def BV_Sub(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVSub(a, b)

    def BV_Mul(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVMul(a, b)

    def BV_UDiv(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVUDiv(a, b)

    def BV_SDiv(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVSDiv(a, b)

    def BV_SMod(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVSMod(a, b)

    def BV_SRem(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVSRem(a, b)

    def BV_URem(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVURem(a, b)

    def BV_Sign_Extend(self, a: "YicesTermBV", b: int) -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, int), f"Expected type int, got {type(b)}"

        return YicesTermBVSignExtend(a, b)

    def BV_Zero_Extend(self, a: "YicesTermBV", b: int) -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, int), f"Expected type int, got {type(b)}"

        return YicesTermBVZeroExtend(a, b)

    def BV_UGE(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBool":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVUGE(a, b)

    def BV_ULE(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBool":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVULE(a, b)

    def BV_UGT(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBool":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVUGT(a, b)

    def BV_ULT(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBool":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVULT(a, b)

    def BV_SGE(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBool":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVSGE(a, b)

    def BV_SLE(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBool":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVSLE(a, b)

    def BV_SGT(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBool":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVSGT(a, b)

    def BV_SLT(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBool":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVSLT(a, b)

    def BV_And(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVAnd(a, b)

    def BV_Or(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVOr(a, b)

    def BV_Xor(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVXor(a, b)

    def BV_Not(self, a: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"

        return YicesTermBVNot(a)

    def BV_Shl(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVShl(a, b)

    def BV_Shr(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVShr(a, b)

    def BV_Sar(self, a: "YicesTermBV", b: "YicesTermBV") -> "YicesTermBV":
        assert isinstance(a, YicesTermBV), f"Expected type YicesTermBV, got {type(a)}"
        assert isinstance(b, YicesTermBV), f"Expected type YicesTermBV, got {type(b)}"

        return YicesTermBVSar(a, b)

    # ARRAY OPERATIONS

    def Array_Store(
        self, arr: "YicesTermArray", index: "YicesTermBV", elem: "YicesTermBV"
    ) -> "YicesTermArray":
        assert isinstance(
            arr, YicesTermArray
        ), f"Expected type YicesTermArray, got {type(arr)}"
        assert isinstance(
            index, YicesTermBV
        ), f"Expected type YicesTermBV, got {type(index)}"
        assert isinstance(
            elem, YicesTermBV
        ), f"Expected type YicesTermBV, got {type(elem)}"

        return YicesTermArrayStore(arr, index, elem)

    def Array_Select(
        self, arr: "YicesTermArray", index: "YicesTermBV"
    ) -> "YicesTermBV":
        assert isinstance(
            arr, YicesTermArray
        ), f"Expected type YicesTermArray, got {type(arr)}"
        assert isinstance(
            index, YicesTermBV
        ), f"Expected type YicesTermBV, got {type(index)}"

        return YicesTermArraySelect(arr, index)

    def eval(self, term: "YicesTerm", raw=False):
        assert self.is_sat(), "Formula is UNSAT"
        model = yices.Model.from_context(self.solver, 1)
        new_term_id = model.get_value_as_term(term.id)
        ret = YicesTermBVV.from_term_id(new_term_id)
        if raw:
            return ret
        else:
            return ret.value

    def copy(self):
        new_solver = Yices2()
        return new_solver

    def dispose(self):
        if self.solver.context:
            self.solver.dispose()

    def __del__(self):
        # garbage collect the solver context
        self.dispose()

    def __getstate__(self):
        return {
            "_assertions_by_frame": self._assertions_by_frame,
        }

    def __setstate__(self, state):
        self.__init__()

        for i, frame in enumerate(state["_assertions_by_frame"]):
            self.add_assertions(frame)

            if i < len(state["_assertions_by_frame"]) - 1:
                self.push()

    def __repr__(self):
        n_assertions = sum([len(frame) for frame in self._assertions_by_frame])
        n_frames = len(self._assertions_by_frame)
        return f"<Yices2 solver; {n_assertions} assertions in {n_frames} frames>"


class YicesTerm(Term):
    id: int
    operator: str
    children: List["YicesTerm"]

    def __init__(self, yices_id, operator=None, children=None, name=None, value=None):
        self.id = yices_id
        self.children = children if children else []
        self.num_children = len(self.children)
        self.operator = operator
        self.is_simplified = False

    @property
    def value(self):
        if hasattr(self, '_value'):
            return self._value
        elif yices.Terms.constructor(self.id) == yices.Constructor.BV_CONSTANT:
            res_str = yices.Terms.to_string(self.id, width=-1)
            self._value = int(res_str[2:], 2)

            return self._value
        else:
            # raise Exception(f'Symbolic term has no .value')
            return None

    def dump_smt2(self):
        """
        Dump the term to a string in SMT2 format
        """
        raise NotImplementedError("dump_smt2() not implemented")

    def dump(self, pp=False):
        _dump = yices.Terms.to_string(self.id, width=-1, height=-1, offset=0)
        if pp is True:
            for match in re.findall(r"0b\d*", _dump):
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
        name_str = (
            f" name:{self.name}" if getattr(self, "name", None) is not None else ""
        )
        value_str = (
            f" value:{hex(self.value)}"
            if getattr(self, "value", None) is not None
            else ""
        )
        return f"(#{self.id}) {operator}{name_str}{value_str}"

    def __repr__(self):
        return str(self)

    def __int__(self):
        return self.id

    def __eq__(self, other):
        return self.id == other.id

    def __hash__(self):
        return self.id


class YicesTermBool(BoolTerm, YicesTerm):
    pass


class YicesTermNot(YicesTermBool):
    arg: YicesTermBool

    def __init__(self, arg: YicesTermBool):
        yices_id = yices.Terms.ynot(arg.id)
        super().__init__(operator="not", children=[arg], yices_id=yices_id)
        self.arg = arg

    def dump_smt2(self):
        return f"(not {self.arg.dump_smt2()})"

    def __getstate__(self):
        return {"arg": self.arg}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermAnd(YicesTermBool):
    args: List[YicesTermBool]

    def __init__(self, *args: YicesTermBool):
        yices_id = yices.Terms.yand([arg.id for arg in args])
        super().__init__(operator="and", children=list(args), yices_id=yices_id)
        self.args = list(args)

    def dump_smt2(self):
        and_args = ' '.join([arg.dump_smt2() for arg in self.args])
        return f"(and {and_args})"

    def __getstate__(self):
        return {"args": self.args}

    def __setstate__(self, state):
        self.__init__(*state["args"])


class YicesTermOr(YicesTermBool):
    args: List[YicesTermBool]

    def __init__(self, *args: YicesTermBool):
        yices_id = yices.Terms.yor([arg.id for arg in args])
        super().__init__(operator="or", children=list(args), yices_id=yices_id)
        self.args = list(args)

    def dump_smt2(self):
        or_args = ' '.join([arg.dump_smt2() for arg in self.args])
        return f"(or {or_args})"

    def __getstate__(self):
        return {"args": self.args}

    def __setstate__(self, state):
        self.__init__(*state["args"])


class YicesTermEquals(YicesTermBool):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bveq_atom(lhs.id, rhs.id)
        super().__init__(operator="equal", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(= {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermNotEquals(YicesTermBool):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvneq_atom(lhs.id, rhs.id)
        super().__init__(operator="not-equal", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(not (= {self.lhs.dump_smt2()} {self.rhs.dump_smt2()}))"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBV(BVTerm, YicesTerm):
    @property
    def bitsize(self):
        return yices.Terms.bitsize(self.id)


class YicesTermBVV(YicesTermBV):
    def __init__(self, value: int, bitsize: int, yices_id=None):
        if yices_id is None:
            yices_id = yices.Terms.parse_bvbin(
                format(value % (2**bitsize), f"#0{bitsize+2}b")[2:]
            )

        super().__init__(operator="bvv", children=[], yices_id=yices_id)
        self._value = value
        self._bitsize = bitsize

    @property
    def value(self) -> int:
        return self._value

    @property
    def bitsize(self) -> int:
        return self._bitsize

    def dump_smt2(self):
        bitsize = self.bitsize
        if bitsize % 8 == 0:
            # output in hex, padding with zeroes
            num_hexdigits = bitsize // 4
            return f"#x{self.value:0{num_hexdigits}x}"
        else:
            # output in binary
            return f"#b{self.value:0{bitsize}b}"

    def __getstate__(self):
        return {"value": self.value, "bitsize": self.bitsize}

    def __setstate__(self, state):
        self.__init__(**state)

    @classmethod
    def from_term_id(cls, term_id: int):
        """
        Construct a BVV from a yices term id, which might happen
        if we are evaluating a model, for example.
        """
        assert yices.Constructor.BV_CONSTANT == yices.Terms.constructor(term_id)
        bitsize = yices.Terms.bitsize(term_id)
        res_str = yices.Terms.to_string(term_id, width=-1)
        value = int(res_str[2:], 2)
        return cls(value=value, bitsize=bitsize, yices_id=term_id)


class YicesTermBVS(YicesTermBV):
    name: str

    def __init__(self, name: str, bitsize: int, yices_id=None):
        if yices_id is None:
            yices_id = yices.Terms.new_uninterpreted_term(
                yices.Types.bv_type(bitsize), name=name
            )

        super().__init__(operator="bvs", children=[], yices_id=yices_id)
        self.name = name

    def dump_smt2(self):
        return self.name

    def __getstate__(self):
        return {"name": self.name, "bitsize": self.bitsize}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVExtract(YicesTermBV):
    term: "YicesTermBV"
    start: int
    end: int

    def __init__(self, term: "YicesTermBV", start: int, end: int):
        yices_id = yices.Terms.bvextract(term.id, start, end)
        super().__init__(operator="bv-extract", children=[term], yices_id=yices_id)
        self.term = term
        self.start = start
        self.end = end

    def dump_smt2(self):
        return f"((_ extract {self.start} {self.end}) {self.term.dump_smt2()})"

    def __getstate__(self):
        return {"term": self.term, "start": self.start, "end": self.end}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVConcat(YicesTermBV):
    args: List["YicesTermBV"]

    def __init__(self, *args: "YicesTermBV"):
        yices_id = yices.Terms.bvconcat([arg.id for arg in args])
        super().__init__(operator="bv-concat", children=list(args), yices_id=yices_id)
        self.args = list(args)

    def dump_smt2(self):
        return f"(concat {' '.join([arg.dump_smt2() for arg in self.args])})"

    def __getstate__(self):
        return {"args": self.args}

    def __setstate__(self, state):
        self.__init__(*state["args"])

class YicesTermBVIf(YicesTermBV):
    condition: "YicesTermBool"
    value_if_true: "YicesTermBV"
    value_if_false: "YicesTermBV"

    def __init__(
        self,
        condition: "YicesTermBool",
        value_if_true: "YicesTermBV",
        value_if_false: "YicesTermBV",
    ):
        yices_id = yices.Terms.ite(condition.id, value_if_true.id, value_if_false.id)
        super().__init__(
            operator="if",
            children=[condition, value_if_true, value_if_false],
            yices_id=yices_id,
        )
        self.condition = condition
        self.value_if_true = value_if_true
        self.value_if_false = value_if_false

    def dump_smt2(self):
        return f"(ite {self.condition.dump_smt2()} {self.value_if_true.dump_smt2()} {self.value_if_false.dump_smt2()})"

    def __getstate__(self):
        return {
            "condition": self.condition,
            "value_if_true": self.value_if_true,
            "value_if_false": self.value_if_false,
        }

    def __setstate__(self, state):
        self.__init__(**state)

class YicesTermBoolIf(YicesTermBool):
    condition: "YicesTermBool"
    value_if_true: "YicesTermBool"
    value_if_false: "YicesTermBool"

    def __init__(
        self,
        condition: "YicesTermBool",
        value_if_true: "YicesTermBool",
        value_if_false: "YicesTermBool",
    ):
        yices_id = yices.Terms.ite(condition.id, value_if_true.id, value_if_false.id)
        super().__init__(
            operator="if",
            children=[condition, value_if_true, value_if_false],
            yices_id=yices_id,
        )
        self.condition = condition
        self.value_if_true = value_if_true
        self.value_if_false = value_if_false

    def dump_smt2(self):
        return f"(ite {self.condition.dump_smt2()} {self.value_if_true.dump_smt2()} {self.value_if_false.dump_smt2()})"

    def __getstate__(self):
        return {
            "condition": self.condition,
            "value_if_true": self.value_if_true,
            "value_if_false": self.value_if_false,
        }

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVAdd(YicesTermBV):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvadd(lhs.id, rhs.id)
        super().__init__(operator="bvadd", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvadd {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVSub(YicesTermBV):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvsub(lhs.id, rhs.id)
        super().__init__(operator="bvsub", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvsub {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVMul(YicesTermBV):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvmul(lhs.id, rhs.id)
        super().__init__(operator="bvmul", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvmul {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVUDiv(YicesTermBV):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvdiv(lhs.id, rhs.id)
        super().__init__(operator="bvudiv", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvudiv {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVSDiv(YicesTermBV):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvsdiv(lhs.id, rhs.id)
        super().__init__(operator="bvsdiv", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvsdiv {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVSMod(YicesTermBV):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvsmod(lhs.id, rhs.id)
        super().__init__(operator="bvsmod", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvsmod {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVSRem(YicesTermBV):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvsrem(lhs.id, rhs.id)
        super().__init__(operator="bvsrem", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvsrem {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVURem(YicesTermBV):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvrem(lhs.id, rhs.id)
        super().__init__(operator="bvurem", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvurem {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVSignExtend(YicesTermBV):
    arg: "YicesTermBV"

    def __init__(self, arg: "YicesTermBV", bitsize: int):
        yices_id = yices.Terms.sign_extend(arg.id, bitsize)
        super().__init__(
            operator="bvsign-extend", children=[arg, bitsize], yices_id=yices_id
        )
        self.arg = arg

    def dump_smt2(self):
        return f"((_ sign_extend {self.bitsize}) {self.arg.dump_smt2()})"

    def __getstate__(self):
        return {"arg": self.arg, "bitsize": self.bitsize}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVZeroExtend(YicesTermBV):
    arg: "YicesTermBV"
    extend_by: int

    def __init__(self, arg: "YicesTermBV", extend_by: int):
        yices_id = yices.Terms.zero_extend(arg.id, extend_by)
        super().__init__(
            operator="bvzero-extend", children=[arg, extend_by], yices_id=yices_id
        )
        self.arg = arg
        self.extend_by = extend_by

    def dump_smt2(self):
        return f"((_ zero_extend {self.extend_by}) {self.arg.dump_smt2()})"

    def __getstate__(self):
        return {"arg": self.arg, "extend_by": self.extend_by}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVUGT(YicesTermBool):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvgt_atom(lhs.id, rhs.id)
        super().__init__(operator="bvugt", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvugt {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVUGE(YicesTermBool):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvge_atom(lhs.id, rhs.id)
        super().__init__(operator="bvuge", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvuge {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVULT(YicesTermBool):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvlt_atom(lhs.id, rhs.id)
        super().__init__(operator="bvult", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvult {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVULE(YicesTermBool):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvle_atom(lhs.id, rhs.id)
        super().__init__(operator="bvule", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvule {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVSGT(YicesTermBool):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvsgt_atom(lhs.id, rhs.id)
        super().__init__(operator="bvsgt", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvsgt {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVSGE(YicesTermBool):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvsge_atom(lhs.id, rhs.id)
        super().__init__(operator="bvsge", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvsge {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVSLT(YicesTermBool):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvslt_atom(lhs.id, rhs.id)
        super().__init__(operator="bvslt", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvslt {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVSLE(YicesTermBool):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvsle_atom(lhs.id, rhs.id)
        super().__init__(operator="bvsle", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvsle {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVAnd(YicesTermBV):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvand([lhs.id, rhs.id])
        super().__init__(operator="bvand", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvand {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVOr(YicesTermBV):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvor([lhs.id, rhs.id])
        super().__init__(operator="bvor", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvor {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVXor(YicesTermBV):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvxor([lhs.id, rhs.id])
        super().__init__(operator="bvxor", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvxor {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVNot(YicesTermBV):
    arg: "YicesTermBV"

    def __init__(self, arg: "YicesTermBV"):
        yices_id = yices.Terms.bvnot(arg.id)
        super().__init__(operator="bvnot", children=[arg], yices_id=yices_id)
        self.arg = arg

    def dump_smt2(self):
        return f"(bvnot {self.arg.dump_smt2()})"

    def __getstate__(self):
        return {"arg": self.arg}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVShl(YicesTermBV):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvshl(lhs.id, rhs.id)
        super().__init__(operator="bvshl", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvshl {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVShr(YicesTermBV):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvlshr(lhs.id, rhs.id)
        super().__init__(operator="bvshr", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvlshr {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermBVSar(YicesTermBV):
    lhs: "YicesTermBV"
    rhs: "YicesTermBV"

    def __init__(self, lhs: "YicesTermBV", rhs: "YicesTermBV"):
        yices_id = yices.Terms.bvashr(lhs.id, rhs.id)
        super().__init__(operator="bvashr", children=[lhs, rhs], yices_id=yices_id)
        self.lhs = lhs
        self.rhs = rhs

    def dump_smt2(self):
        return f"(bvashr {self.lhs.dump_smt2()} {self.rhs.dump_smt2()})"

    def __getstate__(self):
        return {"lhs": self.lhs, "rhs": self.rhs}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermArray(ArrayTerm, YicesTerm):

    def __init__(self, name: str, domain: "YicesType", range: "YicesType"):
        array_type = yices.Types.new_function_type([domain.id], range.id)
        yices_id = yices.Terms.new_uninterpreted_term(array_type, name=name)

        super().__init__(
            operator="array", children=[name, domain, range], yices_id=yices_id
        )

        self.name = name
        self.domain = domain
        self.range = range

    def dump_smt2(self):
        # NOTE: We're going to ignore arg 0 (the name) for now --
        # as we only use arrays within expressions, not as top-level declarations (?)
        return f"(Array {self.children[1].dump_smt2()} {self.children[2].dump_smt2()})"

    def __getstate__(self):
        return {"name": self.name, "domain": self.domain, "range": self.range}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermArraySelect(YicesTermBV):

    def __init__(self, arr: "YicesTermArray", index: "YicesTermBV"):
        yices_id = yices.Terms.application(arr.id, [index.id])
        super().__init__(operator="select", children=[arr, index], yices_id=yices_id)
        self.arr = arr
        self.index = index

    def dump_smt2(self):
        return f"(select {self.arr.dump_smt2()} {self.index.dump_smt2()})"

    def __getstate__(self):
        return {"arr": self.arr, "index": self.index}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesTermArrayStore(YicesTermArray):

    def __init__(
        self, arr: "YicesTermArray", index: "YicesTermBV", elem: "YicesTermBV"
    ):

        yices_id = yices.Terms.update(arr.id, [index.id], elem.id)

        # skip over super class, as we don't want to call it
        super(YicesTermArray, self).__init__(
            operator="store", children=[arr, index, elem], yices_id=yices_id
        )

        self.arr = arr
        self.index = index
        self.elem = elem

    def dump_smt2(self):
        return f"(store {self.arr.dump_smt2()} {self.index.dump_smt2()} {self.elem.dump_smt2()})"

    def __getstate__(self):
        return {"arr": self.arr, "index": self.index, "elem": self.elem}

    def __setstate__(self, state):
        self.__init__(**state)


class YicesType:
    id: int
    name: str

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
    bitsize: int
    name: str

    def __init__(self, bitsize):
        yices_id = yices.Types.bv_type(bitsize)
        name = f"bv{bitsize}"
        super().__init__(yices_id, name)
        self.bitsize = bitsize

    def __getstate__(self):
        return {"bitsize": self.bitsize}

    def __setstate__(self, state):
        self.__init__(**state)

