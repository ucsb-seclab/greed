#!/usr/bin/env python3

if __package__:
    from . import common
else:
    import common


if __name__ == "__main__":
    common.setup_logging()
    args = common.parse_args()

    if args.target is None:
        print("Usage: <bin> --target TARGET_DIR")
        exit(1)

    common.run_test(args.target, debug=args.debug)
