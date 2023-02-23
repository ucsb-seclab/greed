#!/usr/bin/env python3
import argparse
import logging

if __package__:
    from . import common
else:
    import common


if __name__ == "__main__":
    common.setup_logging()

    parser = argparse.ArgumentParser()
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug output")
    parser.add_argument("target", type=str, action="store", help="Path to Gigahorse output folder")
    args = parser.parse_args()

    # setup logging
    if args.debug:
        logging.getLogger("greed").setLevel("DEBUG")
    else:
        logging.getLogger("greed").setLevel("INFO")

    if args.target is None:
        print("Usage: <bin> --target TARGET_DIR")
        exit(1)

    common.run_test(args.target, debug=args.debug)
