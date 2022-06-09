#!/usr/bin/env python3
from typing import Mapping, Set, TextIO

import os
import sys

import dill 

# IT: Ugly hack; this can be avoided if we pull the script at the top level
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))
from clientlib.facts_to_cfg import Statement, Block, Function, construct_cfg, load_csv_map # type: ignore

# TACBlock_ident to list(TACStatement)
IR_DICT = {}
IR_DICT_EXPORT_FILENAME = "IR_DICT.dill"

class TAC_Statement:
    def __init__(self, TACblock_ident, ident, opcode, operands=None, defs=None, values=None):
        self.tac_block_id = TACblock_ident
        self.ident = ident
        self.opcode = opcode
        self.operands = operands if operands else list()
        self.defs = defs if defs else list()
        self.values = values if values else dict()
    
    def __str__(self):
        return "TAC_Statement[blockid:{}|stmtid:{}] | opcode: {} | operands:{} | defs:{} | values:{}".format(self.tac_block_id, 
                                                                                                             self.ident,
                                                                                                             self.opcode, 
                                                                                                             self.operands,
                                                                                                             self.defs,
                                                                                                             self.values)
def create_tac_statement(tac_statement, stmt):

    # Associate values with variables using Gigahorse intermediate files
    def parse_val(var: str):
        if var in tac_variable_value:
            tac_statement.values['v' + var.replace('0x', '')] = tac_variable_value[var]
    
    for d in stmt.defs:
        parse_val(d) 
    for o in stmt.operands:
        parse_val(o)

    if stmt.operands:
        tac_statement.operands = ['v' + var.replace('0x', '') for var in stmt.operands] 
    
    if stmt.defs:
        tac_statement.defs = ['v' + var.replace('0x', '') for var in stmt.defs]

    return tac_statement


def process_tac_blocks(block: Block, visited: Set[str]):
    #emit(f"Begin block {block.ident}", out, 1)

    IR_DICT[block.ident] = []

    for stmt in block.statements:
        tac_statement = TAC_Statement(block.ident, stmt.ident, stmt.op)
        full_tac_statement = create_tac_statement(tac_statement, stmt)
        IR_DICT[block.ident].append(full_tac_statement)
    
    for block in block.successors:
        if block.ident not in visited:
            visited.add(block.ident)
            process_tac_blocks(block, visited)

def process_tac_funcs(functions: Mapping[str, Function]):
    for function in sorted(functions.values(), key=lambda x: x.ident):
        process_tac_blocks(function.head_block, set())

def main():
    global tac_variable_value
    tac_variable_value = load_csv_map('TAC_Variable_Value.csv')

    _, functions,  = construct_cfg()

    process_tac_funcs(functions)
    
    print("Dumping IR at {}".format(IR_DICT_EXPORT_FILENAME))

    with open("./{}".format(IR_DICT_EXPORT_FILENAME), "wb") as tac_ir_file:
        dill.dump(IR_DICT, tac_ir_file)

if __name__ == "__main__":
    main()
