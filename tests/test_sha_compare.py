#!/usr/bin/env python3

import os
import pytest

import IPython

from greed import Project
from greed.utils.extra import gen_exec_id

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


    xid = gen_exec_id()
    init_ctx = {"CALLDATA": "0x663bc990"}
    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx, max_calldatasize=20)
    simgr = p.factory.simgr(entry_state=entry_state)

    common.run_test_simgr(simgr, debug=debug)


@pytest.mark.skip
def test_lambda_memory_simple():
    run_test(target_dir=f"{os.path.dirname(__file__)}/test_sha_compare",
             debug=DEBUG)


if __name__ == "__main__":
    common.setup_logging()
    args = common.parse_args()

    DEBUG = args.debug
    test_lambda_memory_simple()