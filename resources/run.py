#!/usr/bin/env python3
import argparse
import logging

import IPython

from greed import Project
from greed.utils import gen_exec_id

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("greed")


def main(args):
    p = Project(target_dir=args.target)
    xid = gen_exec_id()

    entry_state = p.factory.entry_state(xid=xid)
    simgr = p.factory.simgr(entry_state=entry_state)

    ####################################################################################################################
    # SETUP PRIORITIZATION
    if args.find is not None:
        target_stmt = None
        target_stmt_id = None

        if args.find in p.statement_at:
            target_stmt_id = args.find
            target_stmt = p.factory.statement(target_stmt_id)
        else:
            print('Please specify a valid target statement.')
            exit(1)

        directed_search = DirectedSearch(target_stmt)
        simgr.use_technique(directed_search)

        prioritizer = Prioritizer(scoring_function=lambda s: -s.globals['directed_search_distance'])
        simgr.use_technique(prioritizer)

        simgr.run(find=lambda s: s.curr_stmt.id == target_stmt_id)

        if not simgr.found:
            log.fatal('No paths found')
            exit()

        found = simgr.found.pop()

        log.info(f'Found {found}')
        calldata_size = found.MAX_CALLDATA_SIZE
        calldata = found.solver.eval_memory(found.calldata, BVV(calldata_size, 256))\
            .to_bytes(calldata_size, 'big')\
            .hex()
        log.info(f'CALLDATA: {calldata}')
    ####################################################################################################################
    else:
        simgr.run()

    if args.debug:
        IPython.embed()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("target", type=str, action="store", help="Path to Gigahorse output folder")
    parser.add_argument("--find", type=str, action="store", help="Target address")
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug output")

    args = parser.parse_args()

    # setup logging
    if args.debug:
        log.setLevel("DEBUG")
    else:
        log.setLevel("INFO")

    try:
        main(args)
    except KeyboardInterrupt:
        pass
