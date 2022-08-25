#!/usr/bin/env python3
import argparse
import logging

from SEtaac import Project
from SEtaac import options
from SEtaac.exploration_techniques import DFS, DirectedSearch, HeartBeat
from SEtaac.solver.shortcuts import *
from SEtaac.utils import gen_exec_id

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("SEtaac")


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

    init_ctx = {}  # "CALLDATA": "6ecd23060"}
    xid = gen_exec_id()
    entry_state = p.factory.entry_state(xid=xid)
    entry_state.set_init_ctx(init_ctx=init_ctx)

    simgr = p.factory.simgr(entry_state=entry_state)

    options.LAZY_SOLVES = True

    directed_search = DirectedSearch(target_stmt)
    simgr.use_technique(directed_search)

    dfs = DFS()
    simgr.use_technique(dfs)

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
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug output")

    args = parser.parse_args()

    # setup logging
    if args.debug:
        log.setLevel("DEBUG")
    else:
        log.setLevel("INFO")

    main(args)
