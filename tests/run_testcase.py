#!/usr/bin/env python3

import argparse
import logging

from SEtaac import Project, utils
from SEtaac.utils import gen_exec_id

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("SEtaac")


def parse_log(state):
    log_stmt = state.curr_stmt

    # manually set arg_vals, since we didn't handle this statement yet
    log_stmt.set_arg_val(state)

    if not (log_stmt.offset_val == 0 and log_stmt.size_val == 0):
        return

    length_ptr = log_stmt.topic_val
    length = utils.bytes_to_int(state.memory.read(length_ptr, 32))

    value_ptr = log_stmt.topic_val + 32
    value = bytes(state.memory.read(value_ptr, length)).decode()

    print(f"---> {value}")


def main(args):
    p = Project(target_dir=args.target)

    xid = gen_exec_id()
    entry_state = p.factory.entry_state(xid=xid)
    simgr = p.factory.simgr(entry_state=entry_state)

    while len(simgr.active) > 0:
        simgr.run(find=lambda s: s.curr_stmt.__internal_name__ == "LOG1")
        for s in simgr.found:
            parse_log(s)

        simgr.move(from_stash="found", to_stash="active")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("--target", type=str, action="store", help="Path to Gigahorse output folder", required=True)
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug output")

    args = parser.parse_args()

    # setup logging
    if args.debug:
        log.setLevel("DEBUG")
    else:
        log.setLevel("INFO")

    main(args)
