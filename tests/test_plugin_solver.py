from greed.state_plugins.solver import SimStateSolver
from greed.solver.shortcuts import BVV, BVS, BV_Zero_Extend, BV_Add, Equal

def test_symbols_referenced_at_with_YicesTermBVZeroExtend():
    solver = SimStateSolver()

    # Sanity check, add some constraints we know can be solved
    # y = 1
    # x + y = 2
    # => x = 1 (should be inferred)
    x = BVS("x", 32)
    y = BVS("y", 32)
    ONE = BVV(1, 32)
    TWO = BVV(2, 32)
    solver.add_path_constraint(
        Equal(
            BV_Add(x, y),
            TWO,
        )
    )
    solver.add_path_constraint(
        Equal(
            y, ONE
        )
    )

    assert solver.is_sat()

    # set Z to a one-byte value, we will then zero extend it to
    # 32 bytes and assert that it is equal to X (i.e., 1)
    z = BVS("z", 1) 
    extended_z = BV_Zero_Extend(
        z,
        31, # extend_by
    )
    solver.add_path_constraint(
        Equal(
            extended_z,
            x,
        )
    )


    assert solver.is_sat()
    # Get z
    z = solver.eval(z)
    assert z == 1

    # Ensure that we can get all symbols referenced, and that it exactly equals x, y, and z
    syms = solver.symbols_referenced_at()
    sym_names = {s.name for s in syms}
    assert sym_names == {"x", "y", "z"}
