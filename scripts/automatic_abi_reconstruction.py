#!/usr/bin/env python3
import argparse
import logging

from SEtaac import Project
from SEtaac import options
from SEtaac.utils import gen_exec_id
from SEtaac.utils.solver.bitwuzla import Bitwuzla
from SEtaac.utils.solver.shortcuts import *

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

        log.info(f"Analysing signature: {f.signature}")

        # find out minimun possible calldatasize
        options.LAZY_SOLVES = False
        init_ctx = {"CALLDATA": f.signature}
        entry_state = p.factory.entry_state(xid=gen_exec_id(), init_ctx=init_ctx, max_calldatasize=256)
        simgr = p.factory.simgr(entry_state=entry_state)
        simgr.run()

        get_num_calldataload = lambda s: len([stmt for stmt in s.trace if stmt.__internal_name__ == "CALLDATALOAD"])
        for state in sorted(simgr.states, key=get_num_calldataload, reverse=True):
            if state.curr_stmt.__internal_name__ != "STOP":
                continue
            with new_solver_context(state) as solver:
                if solver.is_sat():
                    successful_state = state
                    break
        else:
            log.info("Could not find any successful state (calldatasize range searched: 0-256)")
            continue
            # raise Exception("Could not find any successful state (calldatasize range searched: 0-256)")

        with new_solver_context(successful_state) as solver:
            for i in range(256):
                if solver.is_formula_sat(Equal(successful_state.calldatasize, BVV(i, 256))):
                    mininum_calldatasize = i
                    break
            else:
                raise Exception("Could not find minimum calldatasize (calldatasize range searched: 0-256)")

        log.info(f"minimum calldatasize: {mininum_calldatasize}")

        if mininum_calldatasize == 4:
            log.info(f"function {f.signature} takes no arguments")
            continue

        # find out what offsets contain basic types (can be zero)
        current_offset = 4
        known_types = {0: ('func_signature', 4)}
        with new_solver_context(successful_state) as solver:
            while current_offset + 32 <= mininum_calldatasize:
                # length is parsed ahead of time (when we see an "offset"), so skip this offset if already known
                if current_offset in known_types:
                    current_offset += known_types[current_offset][1]

                bv_current_offset = successful_state.calldata.readn(BVV(current_offset, 256), 32)

                # 1) check if the current offset is a basic element
                current_offset_is_basic = solver.is_formula_sat(
                    Equal(bv_current_offset, BVV(0, 256)))

                if current_offset_is_basic:
                    known_types[current_offset] = ('basic', 32)
                    current_offset += 32
                    continue

                # 2) else, the current offset has to be of "offset" type
                known_types[current_offset] = ('offset', 32)
                for offset in range(current_offset+32, mininum_calldatasize-32+1, 32):
                    if solver.is_formula_sat(Equal(bv_current_offset, BVV(offset, 256))):
                        # 3) find corresponding object (length)
                        known_types[offset] = ('length', 32)
                        break
                else:
                    raise Exception(f"Could not find element pointed by offset at {current_offset}")
                current_offset += 32

            calldata = bytes(solver.eval_one_array(successful_state.calldata.base,
                                                   mininum_calldatasize)).hex()
            log.info(f'CALLDATA: {calldata}')
            log.info(f"{known_types}")

            log.info('-'*20)
            for offset, (name, length) in known_types.items():
                log.info(f"{name} {bytearray.fromhex(calldata)[offset:offset+length].hex()}")


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
