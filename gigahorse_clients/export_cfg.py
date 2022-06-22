#!/usr/bin/env python3
from typing import Mapping, Set, TextIO

import json
import os
import sys
import networkx
import dill 

# IT: Ugly hack; this can be avoided if we pull the script at the top level
sys.path.append(os.path.join(os.path.dirname(__file__), '..'))
from clientlib.facts_to_cfg import Statement, Block, Function, construct_cfg, load_csv, load_csv_map # type: ignore

from opcodes import *

DUMP_CFG_DOT_FILE = True
DUMP_STATEMENTS = True
DROP_ORPHANS = True
CHECK_UNRESOLVED_OPERATORS = True
PRINT_UNRESOLVED_OPERATORS = False 

UNRESOLVED_OPS = []


TAC_CFG_EXPORT_FILENAME = "TAC_CFG.dill"

def emit_stmt(stmt: Statement):
    def render_var(var: str):
        if var in tac_variable_value:
            return f"v{var.replace('0x', '')}({tac_variable_value[var]})"
        else:
            return f"v{var.replace('0x', '')}"
    
    defs = [render_var(v) for v in stmt.defs]
    uses = [render_var(v) for v in stmt.operands]

    if CHECK_UNRESOLVED_OPERATORS:
        if stmt.op in OPCODES.keys():
            if len(uses) != OPCODES[stmt.op].pop:
                UNRESOLVED_OPS.append((stmt.ident, stmt.op, len(uses), OPCODES[stmt.op].pop))
    if defs:
        return f"{stmt.ident}: {', '.join(defs)} = {stmt.op} {', '.join(uses)}"
    else:
        return f"{stmt.ident}: {stmt.op} {', '.join(uses)}"


def is_orphan(node, cfg_data):
    for src, succs in cfg_data['jump_data'].items():
        if node == src and len(succs) != 0:
            return False
        if node in succs:
            return False
    return True


def to_dot(cfg_data, blocks, functions):
    s = 'digraph g {\n'
    s += '\tsplines=ortho;\n'
    s += '\tnode[fontname="courier"];\n'
    for node in cfg_data['nodes']:

        if DROP_ORPHANS and is_orphan(node,cfg_data):
            #print("[!] Discarding orphan node {} (no succs)".format(node))
            continue

        color = 'black' if node not in functions.keys() else 'blue'
        label = []

        if node in functions.keys():
            func_obj = functions[node]
            if func_obj.is_public:
                visibility = 'public'
            else:
                visibility = 'private'
                color = 'red'

            label.append("{}_func_name={}".format(visibility, func_obj.name))

        label.append("block_addr: {}".format(node))

        if DUMP_STATEMENTS:
            for statement in blocks[node].statements:
                label.append(emit_stmt(statement))

        s += '\t\"{}\" [shape=box, color={}, label="{}"];\n'.format(node, color, '\n'.join(label))

    s += '\n'

    for src, succs in cfg_data['jump_data'].items():
        for succ in succs:
            s += '\t\"%s\" -> \"%s\";\n' % (src, succ)

    s += '}'

    with open("./gigahorse_cfg.dot", "w") as cfg_dot:
        cfg_dot.write(s)


def main():
    global tac_variable_value
    tac_variable_value = load_csv_map('TAC_Variable_Value.csv')
    tac_functions_blocks = load_csv('InFunction.csv')
    tac_fallthrough_edge = load_csv_map('IRFallthroughEdge.csv')

    blocks, functions = construct_cfg()

    cfg_data = {}
    cfg_data['nodes'] = []
    cfg_data['jump_data'] = {}
    cfg_data['fallthrough_edge'] = {}
    cfg_data['functions'] = {}
    
    for bb_key, bb in blocks.items():
        cfg_data['nodes'].append(bb_key)
        cfg_data['jump_data'][bb_key] = []

    for bb_key, bb in blocks.items():
        for bb_succ in bb.successors:
            cfg_data['jump_data'][bb_key].append(bb_succ.ident)

        if len(bb.successors) == 0:
            cfg_data['fallthrough_edge'][bb_key] = None
        elif len(bb.successors) == 1:
            cfg_data['fallthrough_edge'][bb_key] = bb.successors[0].ident
        elif bb_key not in tac_fallthrough_edge:
            # this should only happen for callprivate
            cfg_data['fallthrough_edge'][bb_key] = None
        else:
            cfg_data['fallthrough_edge'][bb_key] = tac_fallthrough_edge[bb_key]

    for f_addr, f_data in functions.items():
        # WARNING the ident for the function is in the TAC representation, might not correspond to the block addr in the 
        #         stack based representation
        func_blocks = []
        
        for block_id, f_id in tac_functions_blocks:
            if f_id == f_data.head_block.ident:
                func_blocks.append(block_id)
        
        cfg_data['functions'][f_addr] = dict({
                                              'addr': f_data.head_block.ident, 
                                              'is_public': f_data.is_public, 
                                              'name': f_data.name,
                                              'arguments': f_data.formals,
                                              'blocks': func_blocks
                                             })
    
    if DUMP_CFG_DOT_FILE:
        to_dot(cfg_data, blocks, functions)
    
    if CHECK_UNRESOLVED_OPERATORS and len(UNRESOLVED_OPS) != 0:
        print("[!!!] WARNING | There are {} unresolved ops".format(len(UNRESOLVED_OPS)))
        if PRINT_UNRESOLVED_OPERATORS:
            for x in UNRESOLVED_OPS:
                print(x)

    print("Dumping cfg data at {}".format(TAC_CFG_EXPORT_FILENAME))

    with open("./{}".format(TAC_CFG_EXPORT_FILENAME), "wb") as tac_cfg_file:
        dill.dump(cfg_data, tac_cfg_file)

if __name__ == "__main__":
    main()
