#!/usr/bin/env python3

import os
import sys

# IT: Ugly hack; this can be avoided if we pull the script at the top level
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))
from clientlib.facts_to_cfg import Statement, Block, Function, construct_cfg, load_csv_map  # type: ignore
from opcodes import *
from greed import Project

PRINT_UNRESOLVED_OPS = True
PRINT_UNRESOLVED_OPS_UNREACHABLE = False


def main():
    p = Project(target_dir='.')

    unresolved_ops = list()
    unresolved_ops_unreachable = list()
    for block in p.block_at.values():
        for statement in block.statements:
            # function inlining translates CALLPRIVATE to JUMP with multiple arguments (which is not a bad opcode)
            opcode = statement.__internal_name__
            if opcode in set(OPCODES.keys()) - {"JUMP"}:
                expected_args = OPCODES[opcode].pop
                actual_args = len(statement.arg_vars)
                if actual_args != expected_args and block.function in p.callgraph.nodes:
                    # reachable
                    unresolved_ops.append((statement.id, opcode, actual_args, expected_args))
                elif actual_args != expected_args:
                    # not reachable
                    unresolved_ops_unreachable.append((statement.id, opcode, actual_args, expected_args))

    if len(unresolved_ops+unresolved_ops_unreachable) == 0:
        print("No bad opcodes detected")
        exit(0)

    if len(unresolved_ops_unreachable) != 0:
        print(f"There are {len(unresolved_ops_unreachable)} UNREACHABLE unresolved ops")
        if PRINT_UNRESOLVED_OPS_UNREACHABLE:
            for x in unresolved_ops_unreachable:
                print(x)
        exit(0)

    if len(unresolved_ops) != 0:
        print(f"[!!!] WARNING | There are {len(unresolved_ops)} REACHABLE unresolved ops")
        if PRINT_UNRESOLVED_OPS:
            for x in unresolved_ops:
                print(x)
        exit(1)


if __name__ == "__main__":
    main()
