#!/usr/bin/env python3
import argparse
import logging

from greed import Project
from greed import options
from greed.exploration_techniques import Prioritizer, DirectedSearch, HeartBeat
from greed.solver.shortcuts import *
from greed.utils import gen_exec_id

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("greed")


def main(args):
    p = Project(target_dir=args.target)

    target_stmt = None
    target_stmt_id = None

    if args.addr in p.statement_at:
        target_stmt_id = args.addr
        target_stmt = p.factory.statement(target_stmt_id)
    elif args.addr in p.block_at:
        target_block_id = args.addr
        target_block = p.factory.block(target_block_id)
        target_stmt = target_block.first_ins
        target_stmt_id = target_stmt.id
    else:
        print('Please specify a target address.')
        exit(1)

    init_ctx = {}  # "CALLDATA": "b88d4fde"}
    xid = gen_exec_id()
    entry_state = p.factory.entry_state(xid=xid, max_calldatasize=1024)
    entry_state.set_init_ctx(init_ctx=init_ctx)

    simgr = p.factory.simgr(entry_state=entry_state)

    options.LAZY_SOLVES = args.lazy

    directed_search = DirectedSearch(target_stmt)
    simgr.use_technique(directed_search)

    prioritizer = Prioritizer(scoring_function=lambda s: -s.globals['directed_search_distance'])
    simgr.use_technique(prioritizer)

    # dfs = DFS()
    # simgr.use_technique(dfs)

    heartbeat = HeartBeat()
    simgr.use_technique(heartbeat)

    try:
        simgr.run(find=lambda s: s.curr_stmt.id == target_stmt_id)
    except KeyboardInterrupt:
        pass

    # import IPython; IPython.embed(); exit()

    if not simgr.found:
        log.fatal('No paths found')
        exit()

    found = simgr.found.pop()

    log.info(f'Found {found}')
    calldata_size = found.MAX_CALLDATA_SIZE
    calldata = found.solver.eval_memory(found.calldata, BVV(calldata_size, 256)).to_bytes(calldata_size, 'big').hex()
    log.info(f'CALLDATA: {calldata}')


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("target", type=str, action="store", help="Path to Gigahorse output folder")
    parser.add_argument("--addr", type=str, action="store", help="Target address", required=True)
    parser.add_argument("--lazy", action="store_true", help="Enable lazy solves")
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug output")

    args = parser.parse_args()

    # setup logging
    if args.debug:
        log.setLevel("DEBUG")
    else:
        log.setLevel("INFO")

    main(args)
