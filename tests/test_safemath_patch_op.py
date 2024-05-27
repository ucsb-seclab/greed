"""
Tests the safemath patch instructions
"""

from greed.analyses.safemath_funcs.patch.safe_ops import (
    SymProcedureSafeAdd,
    SymProcedureSafeAddSigned,
    SymProcedureSafeMul,
    SymProcedureSafeMulSigned,
    SymProcedureSafeDiv,
    SymProcedureSafeSub,
    SymProcedureSafeSubSigned,
)
from greed.solver.shortcuts import *
from greed.state import SymbolicEVMState
from greed.utils.extra import gen_exec_id

MAX_UNSIGNED_WORD = 2**256 - 1
MAX_SIGNED_WORD = 2**255 - 1
MIN_SIGNED_WORD = -(2**255)


def test_safemath_add():
    """
    Tests the safe add symprocedure
    """
    symproc = SymProcedureSafeAdd("block_id", "stmt_id", ("a", "b"), ("c",))
    project = MockProject()
    state = SymbolicEVMState(gen_exec_id(), project)

    a = BVS("a", 256)
    b = BVS("b", 256)

    state.registers["a"] = a
    state.registers["b"] = b

    # Fully symbolic a, b
    (state,) = symproc.handle(state)
    state: SymbolicEVMState

    c = state.registers["c"]

    assert state.solver.is_sat()

    # Test a few different cases
    positive_cases = [
        (0, 0, 0),
        (1, 0, 1),
        (0, 1, 1),
        (1, 1, 2),
        (MAX_UNSIGNED_WORD, 0, MAX_UNSIGNED_WORD),
        (0, MAX_UNSIGNED_WORD, MAX_UNSIGNED_WORD),
    ]
    for a_val, b_val, c_val in positive_cases:
        assumption = And(
            Equal(a, BVV(a_val, 256)),
            Equal(b, BVV(b_val, 256)),
            Equal(c, BVV(c_val, 256)),
        )
        assert state.solver.is_formula_sat(
            assumption
        ), f"Failed for {a_val}, {b_val}, {c_val}"

    # Test the generic assumption
    assumption = Equal(c, BV_Add(a, b))
    assert state.solver.is_formula_true(assumption), "Failed for generic case"

    # Test the overflow case
    overflow_assumption = BV_UGT(a, c)  # a > a + b (should be overflow)
    assert not state.solver.is_formula_sat(
        overflow_assumption
    ), "Failed for overflow case"


def test_safemath_add_signed():
    """
    Tests the safe add symprocedure
    """
    symproc = SymProcedureSafeAddSigned("block_id", "stmt_id", ("a", "b"), ("c",))
    project = MockProject()
    state = SymbolicEVMState(gen_exec_id(), project)

    a = BVS("a", 256)
    b = BVS("b", 256)

    state.registers["a"] = a
    state.registers["b"] = b

    # Fully symbolic a, b
    (state,) = symproc.handle(state)
    state: SymbolicEVMState

    c = state.registers["c"]

    assert state.solver.is_sat()

    # Test a few different cases
    positive_cases = [
        (0, 0, 0),
        (1, 0, 1),
        (0, 1, 1),
        (1, 1, 2),
        (1, -1, 0),
        (-1, 1, 0),
        (MAX_SIGNED_WORD, 0, MAX_SIGNED_WORD),
        (0, MAX_SIGNED_WORD, MAX_SIGNED_WORD),
        (MIN_SIGNED_WORD, 0, MIN_SIGNED_WORD),
        (0, MIN_SIGNED_WORD, MIN_SIGNED_WORD),
        (MAX_SIGNED_WORD, -1, MAX_SIGNED_WORD - 1),
    ]
    for a_val, b_val, c_val in positive_cases:
        a_uval = int.from_bytes(a_val.to_bytes(32, "big", signed=True), "big")
        b_uval = int.from_bytes(b_val.to_bytes(32, "big", signed=True), "big")
        c_uval = int.from_bytes(c_val.to_bytes(32, "big", signed=True), "big")

        assumption = And(
            Equal(a, BVV(a_uval, 256)),
            Equal(b, BVV(b_uval, 256)),
            Equal(c, BVV(c_uval, 256)),
        )
        assert state.solver.is_formula_sat(
            assumption
        ), f"Failed for {a_val}, {b_val}, {c_val}"

    # Test the generic assumption
    assumption = Equal(c, BV_Add(a, b))
    assert state.solver.is_formula_true(assumption), "Failed for generic case"

    # Test the overflow case
    overflow_assumption = And(
        BV_SGT(b, BVV(0, 256)), BV_SGT(a, c)  # a > a + b (should be overflow)
    )
    assert not state.solver.is_formula_sat(
        overflow_assumption
    ), "Failed for overflow case"

    # Test the underflow case
    underflow_assumption = And(
        BV_SLT(b, BVV(0, 256)), BV_SLT(a, c)  # a < a + b (should be underflow)
    )
    assert not state.solver.is_formula_sat(
        underflow_assumption
    ), "Failed for underflow case"

    # Go again but this time use one symbolic and one concrete value
    b = BVV(1, 256)

    state = SymbolicEVMState(gen_exec_id(), project)
    state.registers["a"] = a
    state.registers["b"] = b

    (state,) = symproc.handle(state)
    state: SymbolicEVMState

    c = state.registers["c"]

    assert state.solver.is_sat()

    # Test a few different cases
    positive_cases = [
        (0, 1),
        (-1, 0),
        (MIN_SIGNED_WORD, MIN_SIGNED_WORD + 1),
        (MAX_SIGNED_WORD - 1, MAX_SIGNED_WORD),
    ]
    for a_val, c_val in positive_cases:
        a_uval = int.from_bytes(a_val.to_bytes(32, "big", signed=True), "big")
        c_uval = int.from_bytes(c_val.to_bytes(32, "big", signed=True), "big")

        assumption = And(
            Equal(a, BVV(a_uval, 256)),
            Equal(c, BVV(c_uval, 256)),
        )
        assert state.solver.is_formula_sat(assumption), f"Failed for {a_val}, {c_val}"

    # Test overflow case
    overflow_assumption = BV_SGT(a, c)  # a > a + b (should be overflow)
    assert not state.solver.is_formula_sat(
        overflow_assumption
    ), "Failed for overflow case"

    # Now test -1 as the concrete value
    b = BVV(int.from_bytes((-1).to_bytes(32, "big", signed=True), "big"), 256)
    print("b", b)

    state = SymbolicEVMState(gen_exec_id(), project)
    state.registers["a"] = a
    state.registers["b"] = b

    (state,) = symproc.handle(state)
    c = state.registers["c"]

    assert state.solver.is_sat()

    # Test a few different cases
    positive_cases = [
        (0, -1),
        (1, 0),
        (MAX_SIGNED_WORD, MAX_SIGNED_WORD - 1),
        (MIN_SIGNED_WORD + 1, MIN_SIGNED_WORD),
    ]
    for a_val, c_val in positive_cases:
        a_uval = int.from_bytes(a_val.to_bytes(32, "big", signed=True), "big")
        c_uval = int.from_bytes(c_val.to_bytes(32, "big", signed=True), "big")

        assumption = And(
            Equal(a, BVV(a_uval, 256)),
            Equal(c, BVV(c_uval, 256)),
        )
        print(assumption.dump_smt2())

        assert state.solver.is_formula_sat(assumption), f"Failed for {a_val}, {c_val}"

    # Test underflow case
    underflow_assumption = BV_SLT(a, c)  # a < a + b (should be underflow)
    assert not state.solver.is_formula_sat(
        underflow_assumption
    ), "Failed for underflow case"


def test_safemath_sub():
    """
    Tests the safe add symprocedure
    """
    symproc = SymProcedureSafeSub("block_id", "stmt_id", ("a", "b"), ("c",))
    project = MockProject()
    state = SymbolicEVMState(gen_exec_id(), project)

    a = BVS("a", 256)
    b = BVS("b", 256)

    state.registers["a"] = a
    state.registers["b"] = b

    # Fully symbolic a, b
    (state,) = symproc.handle(state)
    state: SymbolicEVMState

    c = state.registers["c"]

    assert state.solver.is_sat()

    # Test a few different cases
    positive_cases = [
        (0, 0, 0),
        (1, 0, 1),
        (1, 1, 0),
        (2, 1, 1),
        (MAX_UNSIGNED_WORD, 0, MAX_UNSIGNED_WORD),
        (MAX_UNSIGNED_WORD, MAX_UNSIGNED_WORD, 0),
    ]
    for a_val, b_val, c_val in positive_cases:
        assumption = And(
            Equal(a, BVV(a_val, 256)),
            Equal(b, BVV(b_val, 256)),
            Equal(c, BVV(c_val, 256)),
        )
        assert state.solver.is_formula_sat(
            assumption
        ), f"Failed for {a_val}, {b_val}, {c_val}"

    # Test the generic assumption
    assumption = Equal(c, BV_Sub(a, b))
    assert state.solver.is_formula_true(assumption), "Failed for generic case"

    # Test the underflow case
    underflow_assumption = BV_ULT(a, c)  # a < a - b (should be underflow)
    assert not state.solver.is_formula_sat(
        underflow_assumption
    ), "Failed for underflow case"


def test_safemath_sub_signed():
    symproc = SymProcedureSafeSubSigned("block_id", "stmt_id", ("a", "b"), ("c",))
    project = MockProject()
    state = SymbolicEVMState(gen_exec_id(), project)

    a = BVS("a", 256)
    b = BVS("b", 256)

    state.registers["a"] = a
    state.registers["b"] = b

    # Fully symbolic a, b
    (state,) = symproc.handle(state)
    state: SymbolicEVMState

    c = state.registers["c"]

    assert state.solver.is_sat()

    # Test a few different cases
    positive_cases = [
        (0, 0, 0),
        (1, 0, 1),
        (0, 1, -1),
        (1, 1, 0),
        (-1, 1, -2),
        (-1, -1, 0),
        (MAX_SIGNED_WORD, 0, MAX_SIGNED_WORD),
        (MAX_SIGNED_WORD, 1, MAX_SIGNED_WORD - 1),
        (MIN_SIGNED_WORD, 0, MIN_SIGNED_WORD),
        (MIN_SIGNED_WORD, -1, MIN_SIGNED_WORD + 1),
        (MAX_SIGNED_WORD, MAX_SIGNED_WORD, 0),
        (MIN_SIGNED_WORD, MIN_SIGNED_WORD, 0),
    ]
    for a_val, b_val, c_val in positive_cases:
        a_uval = int.from_bytes(a_val.to_bytes(32, "big", signed=True), "big")
        b_uval = int.from_bytes(b_val.to_bytes(32, "big", signed=True), "big")
        c_uval = int.from_bytes(c_val.to_bytes(32, "big", signed=True), "big")

        assumption = And(
            Equal(a, BVV(a_uval, 256)),
            Equal(b, BVV(b_uval, 256)),
            Equal(c, BVV(c_uval, 256)),
        )
        assert state.solver.is_formula_sat(
            assumption
        ), f"Failed for {a_val}, {b_val}, {c_val}"

    # Assertions taken from https://stackoverflow.com/a/70503136

    # Test the generic assumption
    assumption = Equal(c, BV_Sub(a, b))
    assert state.solver.is_formula_true(assumption), "Failed for generic case"

    # Test the underflow case
    underflow_assumption = And(
        BV_SGT(b, BVV(0, 256)), BV_SLT(a, BV_Add(BVV(MIN_SIGNED_WORD, 256), b))
    )
    assert not state.solver.is_formula_sat(
        underflow_assumption
    ), "Failed for underflow case"

    # Test the overflow case
    overflow_assumption = And(
        BV_SLT(b, BVV(0, 256)), BV_SGT(a, BV_Add(BVV(MAX_SIGNED_WORD, 256), b))
    )
    assert not state.solver.is_formula_sat(
        overflow_assumption
    ), "Failed for overflow case"

def test_safemath_mul():
    symproc = SymProcedureSafeMul("block_id", "stmt_id", ("a", "b"), ("c",))
    project = MockProject()
    state = SymbolicEVMState(gen_exec_id(), project)

    a = BVS("a", 256)
    b = BVS("b", 256)

    state.registers["a"] = a
    state.registers["b"] = b

    # Fully symbolic a, b
    (state,) = symproc.handle(state)
    state: SymbolicEVMState

    c = state.registers["c"]

    assert state.solver.is_sat()

    # Test a few different cases
    positive_cases = [
        (0, 0, 0),
        (1, 0, 0),
        (0, 1, 0),
        (1, 1, 1),
        (2, 2, 4),
        (MAX_UNSIGNED_WORD, 0, 0),
        (0, MAX_UNSIGNED_WORD, 0),
        (MAX_UNSIGNED_WORD, 1, MAX_UNSIGNED_WORD),
        (1, MAX_UNSIGNED_WORD, MAX_UNSIGNED_WORD),
    ]
    for a_val, b_val, c_val in positive_cases:
        assumption = And(
            Equal(a, BVV(a_val, 256)),
            Equal(b, BVV(b_val, 256)),
            Equal(c, BVV(c_val, 256)), 
        )
        assert state.solver.is_formula_sat(
            assumption
        ), f"Failed for {a_val}, {b_val}, {c_val}"

    # Test the generic assumption
    assumption = Equal(c, BV_Mul(a, b))
    assert state.solver.is_formula_true(assumption), "Failed for generic case"

    # Test the overflow case
    a_extended = BV_Zero_Extend(a, 256)
    b_extended = BV_Zero_Extend(b, 256)
    c_extended = BV_Mul(a_extended, b_extended)
    overflow_assumption = And(
        BV_ULT(a_extended, BVV(MAX_UNSIGNED_WORD, 512)),
        BV_ULT(b_extended, BVV(MAX_UNSIGNED_WORD, 512)),
        BV_UGT(c_extended, BVV(MAX_UNSIGNED_WORD, 512)),
    )
    assert not state.solver.is_formula_sat(
        overflow_assumption
    ), "Failed for overflow case"

def test_safemath_mul_signed():
    symproc = SymProcedureSafeMulSigned("block_id", "stmt_id", ("a", "b"), ("c",))
    project = MockProject()
    state = SymbolicEVMState(gen_exec_id(), project)

    a = BVS("a", 256)
    b = BVS("b", 256)

    state.registers["a"] = a
    state.registers["b"] = b

    # Fully symbolic a, b
    (state,) = symproc.handle(state)
    state: SymbolicEVMState

    c = state.registers["c"]

    assert state.solver.is_sat()

    # Test a few different cases
    positive_cases = [
        (0, 0, 0),
        (1, 0, 0),
        (0, 1, 0),
        (1, 1, 1),
        (2, 2, 4),
        (-1, 0, 0),
        (0, -1, 0),
        (-1, -1, 1),
        (1, -1, -1),
        (-1, 1, -1),
        (2, -1, -2),
        (-2, 1, -2),
        (MAX_SIGNED_WORD, 0, 0),
        (0, MAX_SIGNED_WORD, 0),
        (MIN_SIGNED_WORD, 0, 0),
        (0, MIN_SIGNED_WORD, 0),
        (MAX_SIGNED_WORD, 1, MAX_SIGNED_WORD),
        (MIN_SIGNED_WORD, 1, MIN_SIGNED_WORD),
        (MAX_SIGNED_WORD, -1, MIN_SIGNED_WORD + 1),
        (MIN_SIGNED_WORD + 1, -1, MAX_SIGNED_WORD),
    ]
    for a_val, b_val, c_val in positive_cases:
        a_uval = int.from_bytes(a_val.to_bytes(32, "big", signed=True), "big")
        b_uval = int.from_bytes(b_val.to_bytes(32, "big", signed=True), "big")
        c_uval = int.from_bytes(c_val.to_bytes(32, "big", signed=True), "big")

        assumption = And(
            Equal(a, BVV(a_uval, 256)),
            Equal(b, BVV(b_uval, 256)),
            Equal(c, BVV(c_uval, 256)),
        )
        assert state.solver.is_formula_sat(
            assumption
        ), f"Failed for {a_val}, {b_val}, {c_val}"

    # Test the generic assumption
    assumption = Equal(c, BV_Mul(a, b))
    assert state.solver.is_formula_true(assumption), "Failed for generic case"

    # NOTE: proving no overflow takes too long for yices, so we'll have
    # to just spot-check some cases
    for a_val in range(MIN_SIGNED_WORD, MAX_SIGNED_WORD, (MAX_SIGNED_WORD - MIN_SIGNED_WORD) // 12):
        b_val = (MAX_SIGNED_WORD + 1) // a_val
        while b_val * a_val < (MAX_SIGNED_WORD + 1):
            if b_val > 0:
                b_val += 1
            else:
                b_val -= 1

        a_uval = int.from_bytes(a_val.to_bytes(32, "big", signed=True), "big")
        b_uval = int.from_bytes(b_val.to_bytes(32, "big", signed=True), "big")

        assumption = And(
            Equal(a, BVV(a_uval, 256)),
            Equal(b, BVV(b_uval, 256)),
        )
        assert not state.solver.is_formula_sat(assumption), f"Failed for {a_val}, {b_val} (positive case)"

        b_val = (MIN_SIGNED_WORD - 1) // a_val
        while b_val * a_val > (MIN_SIGNED_WORD - 1):
            if b_val > 0:
                b_val += 1
            else:
                b_val -= 1
        
        b_uval = int.from_bytes(b_val.to_bytes(32, "big", signed=True), "big")

        assumption = And(
            Equal(a, BVV(a_uval, 256)),
            Equal(b, BVV(b_uval, 256)),
        )
        assert not state.solver.is_formula_sat(assumption), f"Failed for {a_val}, {b_val} (negative case)"


def test_safemath_div():
    symproc = SymProcedureSafeDiv("block_id", "stmt_id", ("a", "b"), ("c",))
    project = MockProject()
    state = SymbolicEVMState(gen_exec_id(), project)

    a = BVS("a", 256)
    b = BVS("b", 256)

    state.registers["a"] = a
    state.registers["b"] = b

    # Fully symbolic a, b
    (state,) = symproc.handle(state)
    state: SymbolicEVMState

    c = state.registers["c"]

    assert state.solver.is_sat()

    # Test a few different cases
    positive_cases = [
        (0, 1, 0),
        (1, 1, 1),
        (2, 1, 2),
        (2, 2, 1),
        (2, 4, 0),
        (MAX_UNSIGNED_WORD, 1, MAX_UNSIGNED_WORD),
        (MAX_UNSIGNED_WORD, MAX_UNSIGNED_WORD, 1),
    ]
    for a_val, b_val, c_val in positive_cases:
        assumption = And(
            Equal(a, BVV(a_val, 256)),
            Equal(b, BVV(b_val, 256)),
            Equal(c, BVV(c_val, 256)),
        )
        assert state.solver.is_formula_sat(
            assumption
        ), f"Failed for {a_val}, {b_val}, {c_val}"

    # Test the generic assumption
    assumption = Equal(c, BV_UDiv(a, b))
    assert state.solver.is_formula_true(assumption), "Failed for generic case"

    # Test the division by zero case
    div_by_zero_assumption = Equal(b, BVV(0, 256))
    assert not state.solver.is_formula_sat(
        div_by_zero_assumption
    ), "Failed for division by zero case"

    # Go again but concretize 1 to 0
    b = BVV(0, 256)
    state = SymbolicEVMState(gen_exec_id(), project)
    state.registers["a"] = a
    state.registers["b"] = b

    assert symproc.handle(state) == []

    # Go again but concretize b to 2
    b = BVV(2, 256)
    state = SymbolicEVMState(gen_exec_id(), project)
    state.registers["a"] = a
    state.registers["b"] = b

    (state,) = symproc.handle(state)
    c = state.registers["c"]

    positive_cases = [
        (1, 0),
        (2, 1),
        (4, 2),
    ]
    for a_val, c_val in positive_cases:
        assumption = And(
            Equal(a, BVV(a_val, 256)),
            Equal(c, BVV(c_val, 256)),
        )
        assert state.solver.is_formula_sat(
            assumption
        ), f"Failed for {a_val}, {c_val}"



class MockProject:
    def __init__(self):
        self.code = b""
        self.factory = MockFactory()


class MockFactory:
    def statement(self, _):
        return None

