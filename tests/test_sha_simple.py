#!/usr/bin/env python3
import os

if __package__:
    from . import common
else:
    import common


def test_sha():
    common.run_test(f"{os.path.dirname(__file__)}/test_sha_simple")


if __name__ == "__main__":
    common.setup_logging()
    args = common.parse_args()

    test_sha()
