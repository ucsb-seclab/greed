#!/usr/bin/env python3
import argparse
import logging

import IPython

from SEtaac import Project
from SEtaac.utils import gen_exec_id

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("SEtaac")


def main(args):
    p = Project(target_dir=args.target)
    xid = gen_exec_id()

    # use concrete calldata if possible
    if args.calldata is not None:
        if len(args.calldata.replace('0x', '')) > 256:
            log.error("CALLDATA longer than the current max length (256 bytes)")
            exit(1)
        log.info(f"Setting CALLDATA to a concrete value: {args.calldata}")
        init_ctx = {"CALLDATA": args.calldata, "CALLDATASIZE": len(args.calldata.replace('0x', ''))}
    elif args.function is not None:
        log.info(f"Adding constraints for function id: {args.function}")
        init_ctx = {"CALLDATA": args.function}
    else:
        init_ctx = None

    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx)
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
