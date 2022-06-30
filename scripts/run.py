#!/usr/bin/env python3
import IPython
import argparse
import logging

from SEtaac import Project
from SEtaac.utils import gen_exec_id
from SEtaac.utils.solver.shortcuts import *

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("SEtaac")


def main(args):
    p = Project(target_dir=args.target)

    xid = gen_exec_id()
    entry_state = p.factory.entry_state(xid=xid)

    # use concrete calldata if possible
    if args.calldata is not None:
        log.info(f"Setting CALLDATA to a concrete value: {args.calldata}")
        calldata_int = int(args.calldata, 16)
        calldata_bytes = calldata_int.to_bytes(length=(calldata_int.bit_length() + 7) // 8, byteorder='big')
        entry_state.calldata = [BVV(b, 256) for b in calldata_bytes]
        entry_state.calldatasize = BVV(len(calldata_bytes), 256)
        if len(calldata_bytes) > 256:
            log.error("CALLDATA longer than the current max length (256 bytes)")
            exit(1)
    elif args.function is not None:
        log.info(f"Adding constraints for function id: {args.function}")
        function_id_int = int(args.function, 16)
        function_id_bytes = function_id_int.to_bytes(length=(function_id_int.bit_length() + 7) // 8, byteorder='big')
        for i, b in enumerate(function_id_bytes):
            entry_state.constraints.append(entry_state.calldata[i] == b)

    simgr = p.factory.simgr(entry_state=entry_state)

    try:
        simgr.run()
    except KeyboardInterrupt:
        pass

    if args.debug:
        IPython.embed()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("target", type=str, action="store", help="Path to Gigahorse output folder")
    parser.add_argument("--calldata", type=str, action="store", help="Concrete CALLDATA (in hex)")
    parser.add_argument("--function", type=str, action="store", help="Concrete function identifier (in hex)")
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug output")

    args = parser.parse_args()

    # setup logging
    if args.debug:
        log.setLevel("DEBUG")
    else:
        log.setLevel("INFO")

    main(args)
