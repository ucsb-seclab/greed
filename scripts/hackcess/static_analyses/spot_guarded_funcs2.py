import sys 
import logging 
import networkx as nx
import itertools 

from SEtaac import Project
from SEtaac.TAC.base import TAC_Statement
from SEtaac import options


import random

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
l = logging.getLogger("SpotGuardedFuncs")
l.setLevel(logging.INFO)


class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'
    # Background colors:
    GREYBG = '\033[100m'
    REDBG = '\033[101m'
    GREENBG = '\033[102m'
    YELLOWBG = '\033[103m'
    BLUEBG = '\033[104m'
    PINKBG = '\033[105m'
    CYANBG = '\033[106m'



def check_for_sink(project, func, caller_stmt):
    # Grab all the EQ statements in the target function 
    func_stmts = [s for b in func.blocks for s in b.statements]
    eq_stmts = [s for s in func_stmts if s.__internal_name__ == "EQ"]
    # Check if there exist a path in the usedef graph between the CALLER and the EQ
    for eq_stmt in eq_stmts:
        if nx.has_path(func.usedef_graph, caller_stmt.id, eq_stmt.id):
            l.info(f"   {bcolors.OKGREEN}Found a path from CALLER@{caller_stmt.id} to EQ@{eq_stmt.id} in function {f.name}{bcolors.ENDC}")
            # Let's check where is the EQ coming from
            # First let's exclude the path that goes through CALLER
            # Let's get the path 
            path = nx.shortest_path(func.usedef_graph, caller_stmt.id, eq_stmt.id)[:-1]

            # The last element if the node right before the EQ that defines the EQ arg,
            # we don't need to explore that branch because it's going to the CALLER.
            node_before_eq_to_caller = path[-1]

            # We take the edges of the eq_stmt and get the other path 
            found = False
            for src,dst in func.usedef_graph.in_edges(eq_stmt.id):
                if dst == eq_stmt.id and src != node_before_eq_to_caller:
                    found = True
                    break
            
            # We MUST have it, otherwise something is fucked...
            if not found: assert(False)
            
            # Here src is the last node that defines the arg to EQ, dst is the EQ
            reversed_subtree = nx.dfs_tree(func.usedef_graph.reverse(), source=src)
            
            for idx, pred in enumerate(reversed_subtree.nodes()):
                #print(f"{idx} {pred}")
                node_attr = func.usedef_graph.nodes[pred]
                if node_attr["type"] == "stmt" and node_attr["stmt_name"] == "SLOAD":
                    l.info(f"    {bcolors.WARNING}EQ@{eq_stmt.id} argument is coming from SLOAD!{bcolors.ENDC}")
                elif node_attr["type"] == "var" and node_attr["value"] != '':
                    const = node_attr["value"]
                    l.info(f"    {bcolors.WARNING}EQ@{eq_stmt.id} argument is coming from this constant {const}!{bcolors.ENDC}")
                    
if __name__ == "__main__":
    p = Project(target_dir=sys.argv[1])
    
    import ipdb; ipdb.set_trace()
    
    # Iterate over all the functions in the project
    for f in p.function_at.values():
        l.info(f"<<<Analyzing function {f.name} [signature: {f.signature}] [tac_id: {f.id}]>>>")
        if f.public and f.id != '0x0':
            # Iterate over all the basic blocks in the function
            for bb in f.blocks:
                # Iterate over all the statements in the basic block
                for stmt in bb.statements:
                    # Check if the statement is a call
                    if isinstance(stmt, TAC_Statement) and stmt.__internal_name__ == 'CALLER':
                        l.info(" Spotted CALLER at %s in %s", stmt.id, f.name)
                        # Check if CALLER result flows into any EQ
                        check_for_sink(p, f, stmt)
