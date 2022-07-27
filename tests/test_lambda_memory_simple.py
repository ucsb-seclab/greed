#!/usr/bin/env python3

import os

import IPython

from SEtaac import Project
from SEtaac.utils import gen_exec_id

if __package__:
    from . import common
else:
    import common


DEBUG = False


'''
CALLDATA generated with:

from eth_abi import encode_abi
encode_abi(['uint256', 'uint256', 'uint256', 'uint256', 'bytes32', 'bytes32[]'],[256, 224, 320, 0, b'\x45', [b'\xff',b'\xff',b'\xff',b'\xff',b'\xff',b'\xff',b'\xff',b'\xff',b'\xff',b'\xff']]).hex()

'''


# def print_constraints(state):
#     print("Number of constraints over memory is: {}".format(len(state.memory.constraints)))
#     print("Number of constraints over calldata is: {}".format(len(state.calldata.constraints)))
#     print("Number of constraints over storage is: {}".format(len(state.storage.constraints)))
#     import ipdb; ipdb.set_trace()


def run_test(target_dir, debug=False):
    p = Project(target_dir=target_dir)

    # data with 10 integers in the array
    data = '0000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000' \
           '00000000000000000000000e0000000000000000000000000000000000000000000000000000000000000014000000000000000' \
           '0000000000000000000000000000000000000000000000000045000000000000000000000000000000000000000000000000000' \
           '0000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000' \
           '00000000000000000000000000000000000aff00000000000000000000000000000000000000000000000000000000000000ff0' \
           '0000000000000000000000000000000000000000000000000000000000000ff0000000000000000000000000000000000000000' \
           '0000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000ff000000000000000' \
           '00000000000000000000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000' \
           '00000000ff00000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000' \
           '000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000ff0000' \
           '0000000000000000000000000000000000000000000000000000000000'
    # data with only 2 integers in the array
    # data = '0000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000' \
    #        '00000000000000000000000e0000000000000000000000000000000000000000000000000000000000000004000000000000000' \
    #        '0000000000000000000000000000000000000000000000000045000000000000000000000000000000000000000000000000000' \
    #        '0000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000' \
    #        '000000000000000000000000000000000002ff00000000000000000000000000000000000000000000000000000000000000ff0' \
    #        '0000000000000000000000000000000000000000000000000000000000000'

    xid = gen_exec_id()
    init_ctx = {"CALLDATA": "0x28a3ceac" + data}
    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx, max_calldatasize=600)
    simgr = p.factory.simgr(entry_state=entry_state)

    outcome = testname = None
    while len(simgr.active) > 0:
        simgr.run(find=lambda s: s.curr_stmt.__internal_name__ == "LOG1")
        for s in simgr.found:
            outcome, testname = common.parse_log(s)

        simgr.move(from_stash="found", to_stash="active")

    assert not any([s.error for s in simgr.states]), f"Simulation Manager has errored states: {simgr}"
    assert outcome == "success" and testname == "", f"Simulation Manager did not reach final success state: {simgr}"

    if debug:
        IPython.embed()


def test_lambda_memory_simple():
    run_test(target_dir=f"{os.path.dirname(__file__)}/test_lambda_memory_simple",
             debug=DEBUG)


if __name__ == "__main__":
    common.setup_logging()
    args = common.parse_args()

    DEBUG = args.debug
    test_lambda_memory_simple()