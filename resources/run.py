#!/usr/bin/env python3
import argparse
import logging

import IPython

from web3 import Web3

from greed import Project
from greed import options
from greed.exploration_techniques import DirectedSearch, Prioritizer
from greed.solver.shortcuts import *
from greed.utils.extra import gen_exec_id

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("greed")


def main(args):
    p = Project(target_dir=args.target)
    xid = gen_exec_id()

    options.SOLVER_TIMEOUT = 60
    options.MAX_CALLDATA_SIZE = 1024
    options.GREEDY_SHA = True
    options.MAX_SHA_SIZE = 512
    options.OPTIMISTIC_CALL_RESULTS = True
    options.DEFAULT_EXTCODESIZE = True
    # options.STATE_INSPECT = True

    init_ctx = {
        "CALLDATASIZE": options.MAX_CALLDATA_SIZE,
        "CALLER": "0xaaA4a5495988E18c036436953AC87aadEa074550",
        "ORIGIN": "0xaaA4a5495988E18c036436953AC87aadEa074550",
        "ADDRESS": args.address or "0x42"
    }

    w3 = Web3(Web3.HTTPProvider(options.WEB3_PROVIDER))
    if w3.is_connected():
        block_number = w3.eth.block_number
        block_info = w3.eth.get_block(block_number)
        init_ctx["NUMBER"] = block_number
        init_ctx["DIFFICULTY"] = block_info["totalDifficulty"]
        init_ctx["TIMESTAMP"] = block_info["timestamp"]

    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx, partial_concrete_storage=args.partial_concrete_storage)
    simgr = p.factory.simgr(entry_state=entry_state)

    ####################################################################################################################
    # from greed.exploration_techniques.other import MstoreConcretizer
    # concretizer = MstoreConcretizer()
    # concretizer.setup(simgr)
    # simgr.use_technique(concretizer)

    # def print_calldata(simgr, state):
    #     calldata_size = state.MAX_CALLDATA_SIZE
    #     calldata = state.solver.eval_memory(state.calldata, BVV(calldata_size, 256))
    #     log.info(f'CALLDATA: {calldata}')

    # simgr.one_active.inspect.stop_at_stmt("STATICCALL", func=print_calldata)

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
        calldata = found.solver.eval_memory(found.calldata, BVV(calldata_size, 256))
        log.info(f'CALLDATA: {calldata}')
    ####################################################################################################################
    else:
        simgr.run()

    if args.debug:
        IPython.embed()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("target", type=str, action="store", help="Path to Gigahorse output folder")
    parser.add_argument("--address", type=str, action="store", help="Address of the contract")
    parser.add_argument("--find", type=str, action="store", help="Target code address")
    parser.add_argument("--partial-concrete-storage", dest="partial_concrete_storage", action="store_true", help="Enable partial concrete storage")
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
