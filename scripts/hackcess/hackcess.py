import sys 

from SEtaac import Project
from SEtaac import options
from SEtaac.utils import gen_exec_id
from SEtaac.utils.solver.shortcuts import *
from SEtaac.exploration_techniques import DFS, DirectedSearch, HeartBeat

from taint_analysis import CalldataTaintAnalysis

import networkx as nx 
import random


from SEtaac.utils.solver.yices2 import * 

seen = set()
seen_names = set()
interesting_terms2 = []


def parse_constraints(to_parse):
    if isinstance(to_parse, str) or isinstance(to_parse, int):
        return
    if hasattr(to_parse, "name"):
        if to_parse.name != None:
            print(to_parse.name)
    if hasattr(to_parse, "children"):
        for c in to_parse.children:
            if hasattr(c, "id"):
                parse_constraints(c)

constraints_graph = nx.DiGraph()
seen = set()

def viz_constraints(to_parse):
    global constraints_graph
    global seen
    if hasattr(to_parse, "children"):
        if to_parse not in seen:
            constraints_graph.add_node(to_parse)
            seen.add(to_parse)
            for child in to_parse.children:
                if hasattr(child, "children"):
                    if child not in seen:
                        constraints_graph.add_node(child)
                        seen.add(child)
                    constraints_graph.add_edge(to_parse, child)
                    viz_constraints(child)
            

def find_calldata_deps(to_parse, seen=set()):
    if hasattr(to_parse, "name"):
        if to_parse.name != None:
            print(to_parse.name)
    if isinstance(to_parse, str) or isinstance(to_parse, int):
        return
    if hasattr(to_parse, "name"):
        if to_parse.name != None:
            if "CALLDATALOAD" in to_parse.name:
                print(to_parse) 
    if hasattr(to_parse, "children"):
        for c in to_parse.children:
            if hasattr(c, "id"):
                if c.id not in seen:
                    seen.add(c.id)
                    find_calldata_deps(c, seen)
            else:
                print(to_parse)
    else:
        print(to_parse)


if __name__ == "__main__":
    p = Project(target_dir=sys.argv[1])
    xid = gen_exec_id()
    
    init_ctx = {"CALLDATA": "0x7da1083a0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000a2211111111111111222200000000000000000000000000"}
    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx, max_calldatasize=100)

    #entry_state.add_breakpoint("0x4460x2060x2530x3b")
    
    simgr = p.factory.simgr(entry_state=entry_state)
    
    #options.LAZY_SOLVES = True
    
    dfs = DFS()
    simgr.use_technique(dfs)
    
    directed_search = DirectedSearch(p.factory.statement("0xc10x45"))
    simgr.use_technique(directed_search)

    heartbeat = HeartBeat()
    simgr.use_technique(heartbeat)

    simgr.run(find=lambda s: s.curr_stmt.id == "0xc10x45")

    found = simgr.one_found

    #cta = CalldataTaintAnalysis(found, 0x4, 0x100)
    #cta.is_mem_read_tainted(0x0)

    #data = found.memory.readn(BVV(386,256), BVV(32,256))

    #viz_constraints(found.sha_observed[0].memory.readn(BVV(223,256), BVV(30,256)))

    # Dump the constraints at the memory just copied from CALLDATACOPY
    import ipdb; ipdb.set_trace()
    #viz_constraints(found.memory.readn(BVV(386,256), BVV(32,256)))

    
