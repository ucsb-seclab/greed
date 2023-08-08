#!/usr/bin/env python

import argparse
import logging

from web3 import Web3

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("geth2postgres")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--address", type=str, action="store", help="Target address")
    parser.add_argument("--out", type=str, action="store", help="Target file", default="contract.hex")
    parser.add_argument("--w3", type=str, default="http://127.0.0.1:8545")
    parser.add_argument("--peek", action="store_true", help="Just print code to stdout")
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug output")

    args = parser.parse_args()

    # setup logging
    if args.debug:
        log.setLevel("DEBUG")
    else:
        log.setLevel("INFO")

    # connect to web3
    w3 = Web3(Web3.HTTPProvider(args.w3))
    assert w3.is_connected()

    code = w3.eth.get_code(args.address).hex()[2:]

    if args.peek:
        print(code, end='')
    else:
        with open(args.out, "w") as contract_file:
            contract_file.write(code)
