#!/usr/bin/env python3
import argparse
import itertools
import logging
from collections import defaultdict
from SEtaac.utils.solver.shortcuts import *

import networkx as nx

from SEtaac import Project
from SEtaac import options
from SEtaac.utils import gen_exec_id
from SEtaac.utils.solver.bitwuzla import Bitwuzla
from SEtaac.utils.solver.shortcuts import *
from eth_abi import encode_abi

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("SEtaac")


def main(args):
    set_solver(Bitwuzla)
    p = Project(target_dir=args.target)

    # pick a function
    for f in list(p.function_at.values()):
        # skip if no signature
        if f.signature is None:
            continue

        print(f"Analysing signature: {f.signature}")

        # find out minimun possible calldatasize
        options.LAZY_SOLVES = False
        init_ctx = {"CALLDATA": f.signature}
        entry_state = p.factory.entry_state(xid=gen_exec_id(), init_ctx=init_ctx, max_calldatasize=256)
        simgr = p.factory.simgr(entry_state=entry_state)
        simgr.run()

        get_num_calldataload = lambda s: len([stmt for stmt in s.trace if stmt.__internal_name__ == "CALLDATALOAD"])
        for state in sorted(simgr.states, key=get_num_calldataload, reverse=True):
            with new_solver_context(state) as solver:
                if solver.is_sat():
                    successful_state = state
                    break
        else:
            raise Exception("Could not find any successful state (calldatasize range searched: 0-256)")

        print(get_num_calldataload(successful_state))

        with new_solver_context(successful_state) as solver:
            for i in range(256):
                if solver.is_formula_sat(Equal(successful_state.calldatasize, BVV(i, 256))):
                    mininum_calldatasize = i
                    break
            else:
                raise Exception("Could not find minimum calldatasize (calldatasize range searched: 0-256)")

        print(f"minimum calldatasize: {mininum_calldatasize}")

        if mininum_calldatasize == 4:
            print(f"function {f.signature} takes no arguments")
            continue

        # find out what offsets contain basic types (can be zero)
        with new_solver_context(successful_state) as solver:
            for i in range((mininum_calldatasize-4)//32):
                print(i)
                # bytes_i_is_zero = Equal(Array_Select(successful_state.calldata, BVV(i, 256)), BVV(0, 8))
                # print(i, solver.is_formula_sat(bytes_i_is_zero))

        # now generate ABIs that add up to (mininum_calldatasize - 4) bytes

        # import IPython; IPython.embed()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("target", type=str, action="store", help="Path to Gigahorse output folder")
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug output")

    args = parser.parse_args()

    # setup logging
    if args.debug:
        log.setLevel("DEBUG")
    else:
        log.setLevel("INFO")

    main(args)
