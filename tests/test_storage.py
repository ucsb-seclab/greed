#!/usr/bin/env python3
import os

if __package__:
    from . import common
else:
    import common


DEBUG = False


def test_storage():
    common.run_test(target_dir=f"{os.path.dirname(__file__)}/test_storage",
                    debug=DEBUG)


if __name__ == "__main__":
    common.setup_logging()
    args = common.parse_args()

    DEBUG = args.debug
    test_storage()
