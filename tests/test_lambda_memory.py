import argparse
import logging

import IPython

from SEtaac import Project, utils
from SEtaac.utils import gen_exec_id
from SEtaac.utils.solver.bitwuzla import Bitwuzla
from SEtaac.utils.solver.shortcuts import *


def setup_logging():
    LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
    logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug output")
    args = parser.parse_args()

    # setup logging
    if args.debug:
        logging.getLogger("SEtaac").setLevel("DEBUG")
    else:
        logging.getLogger("SEtaac").setLevel("INFO")

    return args


def parse_log(state):
    log_stmt = state.curr_stmt

    # manually set arg_vals, since we didn't handle this statement yet
    log_stmt.set_arg_val(state)

    if not (bv_unsigned_value(log_stmt.offset_val) == 0 and bv_unsigned_value(log_stmt.size_val) == 0):
        return

    # length_ptr = log_stmt.topic_val
    # length = utils.bytes_to_int(state.memory.read(length_ptr, 32))
    #
    # value_ptr = log_stmt.topic_val + 32
    # value = bytes(state.memory.read(value_ptr, length)).decode()

    value = utils.int_to_big_endian(bv_unsigned_value(log_stmt.topic_val)).decode().split('\x00')[0]

    print(f"---> {value}")
    outcome, testname = value.split(":")
    assert outcome == "success", f"{testname} failed"


'''
CALLDATA generated with:

from eth_abi import encode_abi
encode_abi(['uint256', 'uint256', 'uint256', 'uint256', 'bytes32', 'bytes32[]'],[256, 224, 64, 0, b'\x45', [b'\xff', b'\xff']]).hex()

'''
def run_test(debug=False):
    set_solver(Bitwuzla)
    p = Project(target_dir='./test_lambda_memory')
    
    xid = gen_exec_id()
        
    # SHA("test_1(uint256,uint256,uint256,uint256,bytes32,bytes32[])")
    data = '000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000450000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000002ff00000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000'
    init_ctx = {"CALLDATA": "0x28a3ceac" + data}
    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx, max_calldatasize=512)
    simgr = p.factory.simgr(entry_state=entry_state)

    while len(simgr.active) > 0:
        simgr.run(find=lambda s: s.curr_stmt.__internal_name__ == "LOG1")
        for s in simgr.found:
            parse_log(s)

        simgr.move(from_stash="found", to_stash="active")

    assert not any([s.error for s in simgr.states]), f"Simulation Manager has errored states: {simgr}"

    if debug:
        IPython.embed()

if __name__ == "__main__":
    run_test()