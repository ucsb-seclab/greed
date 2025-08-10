import pickle
import os

import yices
from greed.solver.yices2 import Yices2, YicesTermBool


def test_serialize_deserialize_bvv():
    solver = Yices2()
    bvv = solver.BVV(241, 256)
    assert bvv.bitsize == 256
    assert bvv.value == 241

    serialized = pickle.dumps(bvv)
    deserialized = pickle.loads(serialized)

    assert bvv.value == deserialized.value
    assert bvv.bitsize == deserialized.bitsize


def test_serialize_deserialize_equals():
    solver = Yices2()
    bvv1 = solver.BVV(241, 256)
    bvv2 = solver.BVV(241, 256)
    bvv3 = solver.BVV(242, 256)
    bvv4 = solver.BVV(243, 256)

    should_be_eq = solver.Equal(bvv1, bvv2)
    should_not_be_eq = solver.Equal(bvv1, bvv3)

    model = yices.Model.from_context(solver.solver, 1)

    model_val_eq = model.get_bool_value(should_be_eq.id)
    assert model_val_eq == True

    model_val_neq = model.get_bool_value(should_not_be_eq.id)
    assert model_val_neq == False

    serialized_eq = pickle.dumps(should_be_eq)
    deserialized_eq = pickle.loads(serialized_eq)

    serialized_neq = pickle.dumps(should_not_be_eq)
    deserialized_neq = pickle.loads(serialized_neq)

    # ensure that it still evaluates to the same value

    model = yices.Model.from_context(solver.solver, 1)

    model_val_eq_deser = model.get_bool_value(deserialized_eq.id)
    assert model_val_eq_deser == True

    model_val_neq_deser = model.get_bool_value(deserialized_neq.id)
    assert model_val_neq_deser == False


def test_serialize_deserialize_not_equals():
    solver = Yices2()

    bvv1 = solver.BVV(241, 256)
    bvv2 = solver.BVV(241, 256)
    bvv3 = solver.BVV(242, 256)
    bvv4 = solver.BVV(243, 256)

    should_be_eq = solver.NotEqual(bvv1, bvv2)
    should_not_be_eq = solver.NotEqual(bvv3, bvv4)

    serialized_eq = pickle.dumps(should_be_eq)
    deserialized_eq = pickle.loads(serialized_eq)

    serialized_neq = pickle.dumps(should_not_be_eq)
    deserialized_neq = pickle.loads(serialized_neq)

    # ensure that it evaluates to expected bool values
    model = yices.Model.from_context(solver.solver, 1)

    model_val_eq = model.get_bool_value(deserialized_eq.id)
    assert model_val_eq == False

    model_val_neq = model.get_bool_value(deserialized_neq.id)
    assert model_val_neq == True


def helper_get_true_value(solver) -> YicesTermBool:
    # we don't have a literal for 'true' so instead construct it by
    # doing equality with itself
    bvv = solver.BVV(1, 256)
    return solver.Equal(bvv, bvv)


def helper_get_false_value(solver) -> YicesTermBool:
    # we don't have a literal for 'false' so instead construct it by
    # doing equality with itself
    bvv = solver.BVV(1, 256)
    return solver.NotEqual(bvv, bvv)


def test_serialize_deserialize_and():
    solver = Yices2()

    true_val = helper_get_true_value(solver)
    false_val = helper_get_false_value(solver)

    # 'True and False' => False
    result = solver.And(true_val, false_val)

    ser = pickle.dumps(result)
    deser = pickle.loads(ser)

    model = yices.Model.from_context(solver.solver, 1)
    model_val = model.get_bool_value(deser.id)
    assert model_val == False

    # 'True and True' => True
    result = solver.And(true_val, true_val)

    ser = pickle.dumps(result)
    deser = pickle.loads(ser)

    model = yices.Model.from_context(solver.solver, 1)
    model_val = model.get_bool_value(deser.id)
    assert model_val == True


def test_serialize_deserialize_or():
    solver = Yices2()

    true_val = helper_get_true_value(solver)
    false_val = helper_get_false_value(solver)

    # 'True or False' => True
    result = solver.Or(true_val, false_val)

    ser = pickle.dumps(result)
    deser = pickle.loads(ser)

    model = yices.Model.from_context(solver.solver, 1)
    model_val = model.get_bool_value(deser.id)
    assert model_val == True

    # 'False or False' => False
    result = solver.Or(false_val, false_val)

    ser = pickle.dumps(result)
    deser = pickle.loads(ser)

    model = yices.Model.from_context(solver.solver, 1)
    model_val = model.get_bool_value(deser.id)
    assert model_val == False


def test_serialize_deserialize_not():
    solver = Yices2()

    true_val = helper_get_true_value(solver)
    false_val = helper_get_false_value(solver)

    # 'not True' => False
    result = solver.Not(true_val)

    ser = pickle.dumps(result)
    deser = pickle.loads(ser)

    model = yices.Model.from_context(solver.solver, 1)
    model_val = model.get_bool_value(deser.id)
    assert model_val == False

    # 'not False' => True
    result = solver.Not(false_val)

    ser = pickle.dumps(result)
    deser = pickle.loads(ser)

    model = yices.Model.from_context(solver.solver, 1)
    model_val = model.get_bool_value(deser.id)
    assert model_val == True

def test_serialize_deserialize_add():
    solver = Yices2()

    bvv1 = solver.BVV(102, 256)
    bvv2 = solver.BVV(104, 256)

    result = solver.BV_Add(bvv1, bvv2)

    ser = pickle.dumps(result)
    deser = pickle.loads(ser)

    val = solver.eval(deser)

    assert val == 206

def test_serialize_deserialize_sub():
    solver = Yices2()

    bvv1 = solver.BVV(106, 256)
    bvv2 = solver.BVV(104, 256)

    result = solver.BV_Sub(bvv1, bvv2)

    ser = pickle.dumps(result)
    deser = pickle.loads(ser)

    val = solver.eval(deser)

    assert val == 2

def test_x_equal_123():
    solver = Yices2()
    with open(BIG_ASSERTION_X_EQUAL_123_PICKLE_FNAME, "rb") as f:
        conjunction = pickle.load(f)
        solver.add_assertion(conjunction)
        assert solver.is_sat() == True
        x = solver.get_bv_by_name("x")
        assert x is not None

        x_val = solver.eval(x)
        assert x_val == 123

def test_solver_x_equal_123():
    with open(SOLVER_X_EQUAL_123_PICKLE_FNAME, "rb") as f:
        solver = pickle.load(f)
        assert solver.is_sat() == True
        x = solver.get_bv_by_name("x")
        assert x is not None

        x_val = solver.eval(x)
        assert x_val == 123

def test_solver_multiple_frames():
    with open(SOLVER_MULTIPLE_FRAMES_PICKLE_FNAME, "rb") as f:
        solver: Yices2 = pickle.load(f)
        assert solver.is_sat() == True

        x = solver.get_bv_by_name("x")

        formula_x_eq_350 = solver.Equal(x, solver.BVV(350, 256))
        formula_x_eq_250 = solver.Equal(x, solver.BVV(250, 256))
        formula_x_eq_150 = solver.Equal(x, solver.BVV(150, 256))
        formula_x_eq_50 = solver.Equal(x, solver.BVV(50, 256))

        # first frame, we already asserted x > 200
        assert solver.is_sat() == True
        assert solver.is_formula_sat(formula_x_eq_350) == True
        assert solver.is_formula_sat(formula_x_eq_250) == True
        assert solver.is_formula_sat(formula_x_eq_150) == False
        assert solver.is_formula_sat(formula_x_eq_50) == False

        solver.pop()

        # second frame, we asserted x > 100
        assert solver.is_sat() == True
        assert solver.is_formula_sat(formula_x_eq_350) == True
        assert solver.is_formula_sat(formula_x_eq_250) == True
        assert solver.is_formula_sat(formula_x_eq_150) == True
        assert solver.is_formula_sat(formula_x_eq_50) == False


resources_dir = os.path.join(os.path.dirname(__file__), os.path.basename(__file__).split('.')[0] + '_resources')
os.makedirs(resources_dir, exist_ok=True)
BIG_ASSERTION_X_EQUAL_123_PICKLE_FNAME = os.path.join(resources_dir, "big_assertion_x_equal_123.pickle")
SOLVER_X_EQUAL_123_PICKLE_FNAME = os.path.join(resources_dir, "solver_x_equal_123.pickle")
SOLVER_MULTIPLE_FRAMES_PICKLE_FNAME = os.path.join(resources_dir, "solver_multiple_frames.pickle")

def _store_big_value_equal_123():
    """
    Store a large pickled assertion.
    The assertion ensures that the symbol 'x' is equal to 123.
    We do this in a completely separate python invocation to ensure that no
    funny business is going on by sharing solver state between serialization and deserialization.
    """

    solver = Yices2()
    true_value = helper_get_true_value(solver)
    false_value = helper_get_false_value(solver)
    x = solver.BVS("x", 256)

    # Make a conjunction of a bunch of equalities
    statements = []

    statements.append(solver.Equal(x, solver.BVV(123, 256)))
    statements.append(solver.NotEqual(x, solver.BVV(124, 256)))
    statements.append(solver.Equal(x, solver.If(true_value, solver.BVV(123, 256), solver.BVV(124, 256))))
    statements.append(solver.Equal(x, solver.If(false_value, solver.BVV(124, 256), solver.BVV(123, 256))))
    statements.append(solver.Equal(x, solver.BV_Add(solver.BVV(100, 256), solver.BVV(23, 256))))
    statements.append(solver.Equal(x, solver.BV_Sub(solver.BVV(200, 256), solver.BVV(77, 256))))
    statements.append(solver.Equal(x, solver.BV_Xor(solver.BVV(123 ^ 0xff, 256), solver.BVV(0xff, 256))))

    empty_array = solver.Array('arr1', solver.BVSort(256), solver.BVSort(256))
    array_with_one_element = solver.Array_Store(empty_array, solver.BVV(0x55, 256), solver.BVV(123, 256))
    statements.append(solver.Equal(x, solver.Array_Select(array_with_one_element, solver.BVV(0x55, 256))))

    # extract
    shifted_val = 123 << 8
    extracted = solver.BV_Extract(
        8, # start
        15, # end (inclusive, 15-8+1 = 8 bits)
        solver.BVV(shifted_val, 256),
    )
    assert extracted.bitsize == 8
    expanded = solver.BV_Zero_Extend(extracted, 256-8)
    assert expanded.bitsize == 256
    statements.append(solver.Equal(x, expanded))

    # concat
    # note: 123 == 0b01111011
    # split into two nibbles: 0111 and 1011
    v1 = 123 & 0b1111
    v2 = (123 >> 4) & 0b1111
    v1_bvv = solver.BVV(v1, 4)
    v2_bvv = solver.BVV(v2, 4)
    v = solver.BV_Concat([v2_bvv, v1_bvv])
    assert v.bitsize == 8
    expanded = solver.BV_Zero_Extend(v, 256-8)
    assert expanded.bitsize == 256
    statements.append(solver.Equal(x, expanded))

    with open(BIG_ASSERTION_X_EQUAL_123_PICKLE_FNAME, "wb") as f:
        conjunction = solver.And(*statements)
        pickle.dump(conjunction, f)

def _store_solver_with_only_one_frame():
    """
    Store a whole Solver with only one frame.
    That frame contains a simple assertion that x is equal to 123.
    """

    solver = Yices2()
    x = solver.BVS("x", 256)
    solver.add_assertion(solver.Equal(x, solver.BVV(123, 256)))

    with open(SOLVER_X_EQUAL_123_PICKLE_FNAME, "wb") as f:
        pickle.dump(solver, f)

def _store_solver_with_two_frames():
    """
    Store a solver with two frames.
    The first frame asserts that x > 100.
    The second frame asserts that x > 200.
    """
    solver = Yices2()
    x = solver.BVS("x", 256)

    solver.add_assertion(solver.BV_UGT(x, solver.BVV(100, 256)))
    solver.push()
    solver.add_assertion(solver.BV_UGT(x, solver.BVV(200, 256)))

    with open(SOLVER_MULTIPLE_FRAMES_PICKLE_FNAME, "wb") as f:
        pickle.dump(solver, f)


if __name__ == "__main__":
    _store_big_value_equal_123()
    _store_solver_with_only_one_frame()
    _store_solver_with_two_frames()
