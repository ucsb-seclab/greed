#!/usr/bin/env python3

import os

import IPython

from SEtaac import Project
from SEtaac.solver.shortcuts import *

if __package__:
    from . import common
else:
    import common


DEBUG = False


def run_test(target_dir, debug=False):
    p = Project(target_dir=target_dir)

    state = p.factory.entry_state(xid=1)

    # check initial conditions
    assert not state.solver.is_formula_true(Equal(state.memory[BVV(84, 256)], state.calldata[BVV(42, 256)]))
    assert not state.solver.is_formula_true(Equal(state.memory[BVV(0, 256)], state.calldata[BVV(43, 256)]))

    # test calldata offset < memory offset
    state.calldata[BVV(42, 256)] = BVV(42, 8)
    state.memory.memcopy(BVV(84, 256), state.calldata.copy(state), BVV(42, 256), BVV(1, 256))
    assert state.solver.is_formula_true(Equal(state.memory[BVV(84, 256)], state.calldata[BVV(42, 256)]))

    # test calldata offset > memory offset
    state.calldata[BVV(84, 256)] = BVV(43, 8)
    state.memory.memcopy(BVV(0, 256), state.calldata.copy(state), BVV(43, 256), BVV(1, 256))
    assert state.solver.is_formula_true(Equal(state.memory[BVV(0, 256)], state.calldata[BVV(43, 256)]))

    if debug:
        IPython.embed()


def test_lambda_memory_memcopy_offsets():
    run_test(target_dir=f"{os.path.dirname(__file__)}/test_lambda_memory",
             debug=DEBUG)


if __name__ == "__main__":
    common.setup_logging()
    args = common.parse_args()

    DEBUG = args.debug
    test_lambda_memory_memcopy_offsets()