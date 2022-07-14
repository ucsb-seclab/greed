#!/usr/bin/env python3
from typing import Mapping, Set, TextIO

import json
import os
import sys
import networkx

# IT: Ugly hack; this can be avoided if we pull the script at the top level
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))
from clientlib.facts_to_cfg import Statement, Block, Function, construct_cfg, load_csv_map # type: ignore
from opcodes import *

PRINT_UNRESOLVED_OPERATORS = True 
UNRESOLVED_OPS = []

def check_statement(stmt: Statement):
    if stmt.op in OPCODES.keys():
        if len(stmt.operands) != OPCODES[stmt.op].pop:
            UNRESOLVED_OPS.append((stmt.ident, stmt.op, len(stmt.operands), OPCODES[stmt.op].pop))

def check(blocks, functions):
    for block_id, block in blocks.items():
        for statement in block.statements:
            check_statement(statement)

def main():    
    blocks, functions = construct_cfg()
    check(blocks, functions)
    if len(UNRESOLVED_OPS) != 0:
        print("[!!!] WARNING | There are {} unresolved ops".format(len(UNRESOLVED_OPS)))
        if PRINT_UNRESOLVED_OPERATORS:
            for x in UNRESOLVED_OPS:
                print(x)
    else:
        print("No bad opcodes detected")


if __name__ == "__main__":
    main()
