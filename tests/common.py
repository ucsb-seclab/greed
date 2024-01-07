import argparse
import logging

import IPython

from greed import Project
from greed.solver.shortcuts import *
from greed.utils.extra import gen_exec_id
from greed.exploration_techniques import HeartBeat

def setup_logging():
    LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
    logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug output")
    args = parser.parse_args()

    # setup logging
    if args.debug:
        logging.getLogger("greed").setLevel("DEBUG")
    else:
        logging.getLogger("greed").setLevel("INFO")

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

    value_int = bv_unsigned_value(log_stmt.topic_val)
    value = value_int.to_bytes(length=(value_int.bit_length() + 7) // 8, byteorder='big').decode().split('\x00')[0]

    print(f"---> {value}")
    outcome, testname = value.split(":")
    assert outcome == "success", f"{testname} failed"
    return outcome, testname


def run_test(target_dir, debug=False):
    p = Project(target_dir=target_dir)

    xid = gen_exec_id()
    entry_state = p.factory.entry_state(xid=xid)
    simgr = p.factory.simgr(entry_state=entry_state)
    # heartbeat = HeartBeat(beat_interval=1, show_op=True)
    # simgr.use_technique(heartbeat)

    run_test_simgr(simgr, debug=debug)


def run_test_simgr(simgr, debug=False):
    outcome = testname = None
    while len(simgr.active) > 0:
        simgr.run(find=lambda s: s.curr_stmt.__internal_name__ == "LOG1")
        for s in simgr.found:
            if len(s.sha_observed) > 0:
                if s.sha_resolver.fix_shas():
                    outcome, testname = parse_log(s)
                else:
                    # Prune this state, shas are unsat.
                    simgr.stashes["found"].remove(s)
                    simgr.stashes["pruned"].append(s)
            else:
                outcome, testname = parse_log(s)
            
        simgr.move(from_stash="found", to_stash="active")

    assert not any([s.error for s in simgr.states]), f"Simulation Manager has errored states: {simgr}"
    
    assert outcome == "success" and testname == "", f"Simulation Manager did not reach final success state: {simgr}"

    if debug:
        IPython.embed()
