#!/usr/bin/env python3
import os

if __package__:
    from . import common
else:
    import common


DEBUG = False


def test_sha():
    common.run_test(target_dir=f"{os.path.dirname(__file__)}/test_sha_overlapping",
                    debug=DEBUG)


if __name__ == "__main__":
    common.setup_logging()
    args = common.parse_args()

    DEBUG = args.debug
    test_sha()
