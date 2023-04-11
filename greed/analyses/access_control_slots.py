# This analysis extracts the storage slots that are possibly containing 
# variables related to the administration of the contracts (_owner, _guardian, etc...)
#
# As for now, it is a simpler implementation of the Achecker paper 
# https://www.asemghaleb.com/assets/pdf/AChecker_paper-preprint.pdf that map-based 
# permissions.
# 
# In terms of true positives, the results are comparable to the guard analysis performed by
# Gigahorse, however, as Gigahorse tries to recover map-based permissions, our analysis here 
# is afflicted by less false positives.
#
# E.g., Gigahorse would mark as guard the variable _debt when the contract contains code like
# this:
# 
# require(varg0 <= _debt[v2], Error('SafeMath: subtraction overflow'));
#


import web3
import os
import sys 
import datetime
import json
import logging
import time
import shutil
import networkx as nx 

from greed import Project
from greed import options

log = logging.getLogger(__name__)

# This represents a state instantiated at a specific node of the use-def graph
# Every state contains the list of stmt and vars collected until now following a specific
# path in the use-def graph.
class ReverseExplorerState:
    def __init__(self, project, func, target:str, caller=None, slices_stmts=None, slices_vars=None):
        self.project = project
        # Target is simply an ID in the usedef graph
        self.target = target
        self.stmt = None if not self.is_stmt() else self.project.statement_at[self.target]
        self.func = func
        reversed_usedef = self.func.usedef_graph.reverse()
        self.reversed_subgraph = nx.subgraph(reversed_usedef, nx.descendants(reversed_usedef, self.target) | {self.target})

        self.caller = None if caller is None else caller
        self.slices_stmts = set() if slices_stmts is None else slices_stmts
        self.slices_vars = {target,} if slices_vars is None else slices_vars|{target,}

    def step(self):
        return [ReverseExplorerState(self.project, self.func, n, self.caller, self.slices_stmts, self.slices_vars) 
                                for n in self.reversed_subgraph.neighbors(self.target)]
    
    def is_stmt(self):
        return "0x" in self.target
    
    def __repr__(self):
        return str(self.slices_stmts)

# Orchestrates the backward exploration of the use-def graph to collect
# all the nodes involved in defining a specific var target.
class ReverseExplorer:
    def __init__(self, project, first_state):
        self.project = project
        self.stashes = [first_state]
        self.slices = set()

        self.seen_targets = set()
        
    def run(self):
        while len(self.stashes) > 0:
            log.debug(f'len of stash: {len(self.stashes)}')
            curr_state = self.stashes.pop()
            log.debug(f"curr_state is at {curr_state.target}")
            next_states = curr_state.step()
            
            if len(next_states) == 0:
                log.debug(f'Deadended: {curr_state.slices_stmts}')
                self.slices.add(curr_state)
                
            log.debug(f'next_states are {[x.target for x in next_states]}')

            for next_state in next_states:
                if next_state.target in self.seen_targets:
                    # Stop this branch. Don't discard, we might have reached this target 
                    # from another branch of the usedef graph and we must keep the trace.
                    log.debug(f'Deadended: {curr_state.slices_stmts}')
                    self.slices.add(curr_state)
                    continue
                else:
                    self.seen_targets.add(next_state.target)
                #log.debug(next_state.target, next_state.slices_vars, next_state.slices_stmts )
                if next_state.is_stmt():
                    if next_state.stmt.__internal_name__ == "CALL" or next_state.stmt.__internal_name__ == "CALLCODE" or next_state.stmt.__internal_name__ == "DELEGATECALL" or next_state.stmt.__internal_name__ == "STATICCALL":
                        log.debug(f'Found {next_state.stmt}')
                        # We'll see later if we want to consider external checks. As of now we kinda want 
                        # only the storage slots with "critical" ownership data.
                        pass
                    elif next_state.stmt.__internal_name__ == "CALLPRIVATE":
                        log.debug(f'Found {next_state.stmt}')
                        # Trying to extract the destination of the CALLPRIVATE, if we can't, as for now we give up.
                        try:
                            func_target = self.project.function_at[hex(next_state.stmt.arg_vals[next_state.stmt.arg1_var].value)]
                        except Exception as e:
                            log.debug(f"Could not extract function target for {next_state}")
                            # Consider to extract this dynamically maybe? TODO
                            continue

                        # Grab all the returnprivates of the target function
                        return_privates = [s for b in func_target.blocks for s in b.statements if s.__internal_name__ == "RETURNPRIVATE"]
                            
                        # How many res_var of the CALLPRIVATE are in the use-def chain of the target var?
                        res_vars_deps = [res_var for res_var in next_state.stmt.res_vars if res_var in next_state.slices_vars]

                        # Grab their indexes in the res_vars list (these are gonna be used to understand which RETURNPRIVATE var to consider)
                        res_vars_deps_idx = [next_state.stmt.res_vars.index(res_var_dep) for res_var_dep in res_vars_deps]

                        for rp in return_privates:
                            if len(rp.arg_vars) != len(next_state.stmt.arg_vars):
                                log.debug(f"Wrong mapping between CALLPRIVATE and RETURNPRIVATE (expected at least {max(res_vars_deps_idx)} args, got {len(rp.arg_vars)})")
                                continue
                            log.debug(f"Investigating return from {func_target.id}")
                            for res_var_dep_idx in res_vars_deps_idx:
                                # The argument in position 1 is the one mapped to the res_var if the CALLPRIVATE had only 1 arg
                                # We are doing res_var_dep_idx+1 because the var at 0 is the return PC
                                log.debug(f"Resuming slice from {rp.arg_vars[res_var_dep_idx+1]}")
                                new_slices_vars = next_state.slices_vars.copy()
                                new_slices_vars.add(rp.arg_vars[res_var_dep_idx+1])
                                self.stashes.append(ReverseExplorerState(self.project,
                                                                         func_target, 
                                                                         rp.arg_vars[res_var_dep_idx+1],
                                                                         caller=next_state.stmt,
                                                                         slices_stmts=next_state.slices_stmts.copy(), 
                                                                         slices_vars=new_slices_vars.copy()))
                    else:
                        log.debug(f"Adding stmt {next_state.target}")
                        new_slices_stmts = next_state.slices_stmts.copy()
                        new_slices_stmts.add(next_state.target)
                        self.stashes.append(ReverseExplorerState(self.project,
                                                                 next_state.func,
                                                                 next_state.target, 
                                                                 next_state.caller, 
                                                                 slices_stmts=new_slices_stmts.copy(), 
                                                                 slices_vars=next_state.slices_vars.copy()))
                else:
                    # We are in a var
                    if "arg" in next_state.target:
                        log.debug("Return value depends on the argument of CALLPRIVATE!")
                        #log.debug(f'Deadended: {curr_state.slices_stmts}')
                        #self.slices.add(curr_state) # As of now we stop.
                        if next_state.caller is None:
                            # HACK: as of now, if there is no caller, we avoid to xref the current function.
                            log.debug(f'No caller, stopping here')
                            log.debug(f'Deadended: {curr_state.slices_stmts}')
                            self.slices.add(curr_state)
                        else:
                            # Let's map the argument to this CALLPRIVATE to the corresponding argument of the caller
                            index_of_arg = int(next_state.target.split("arg")[1],10)
                            callprivate_arg_target = next_state.caller.arg_vars[index_of_arg+1]
                            log.debug("Adding a var")
                            # Simply add the var
                            new_slices_vars = next_state.slices_vars.copy()
                            new_slices_vars.add(callprivate_arg_target)
                            self.stashes.append(ReverseExplorerState(self.project,
                                                                    next_state.func,
                                                                    next_state.target, 
                                                                    next_state.caller, 
                                                                    slices_stmts=next_state.slices_stmts.copy(), 
                                                                    slices_vars=new_slices_vars.copy()))                            
                    else:
                        log.debug("Adding a var")
                        # Simply add the var
                        new_slices_vars = next_state.slices_vars.copy()
                        new_slices_vars.add(next_state.target)
                        self.stashes.append(ReverseExplorerState(self.project,
                                                                 next_state.func,
                                                                 next_state.target, 
                                                                 next_state.caller, 
                                                                 slices_stmts=next_state.slices_stmts.copy(), 
                                                                 slices_vars=new_slices_vars.copy()))

# Just an utility to dump the use-def graph and change color
# to the stmt nodes involved in the collected slice.
def dump_slice(full_slice, func, filename):
    log.info(f"Dumping usedef .dot output to file {filename}")

    dot = "digraph g {\n"
    dot += "splines=ortho;\n"
    dot += "node[fontname=\"courier\"];\n"

    # Iterate though the nodes in the graph
    for node in func.usedef_graph.nodes:
        label = []
        # Get the node attributes
        node_attr = func.usedef_graph.nodes[node]

        if node_attr["type"] == "stmt":
            label.append(f"id: {node}")
            label.append(f"stmt_name: {node_attr['stmt_name']}")
            label.append(f"block_id: {node_attr['block_id']}")
            label = "\n".join(label)
        else:
            label.append(f"var: {node}")
            label.append(f"value: {node_attr['value']}")
            label = "\n".join(label)

        if node in full_slice:
            dot += f"\"{node}\" [shape=box, color=red, \nlabel=\"{label}\"];\n\n"
        else:
            dot += f"\"{node}\" [shape=box, color=black, \nlabel=\"{label}\"];\n\n"
    dot += "\n"

    for a, b in func.usedef_graph.edges:
        elabel = []
        # Get the edge attributes
        edge_attr = func.usedef_graph.edges[a, b]
        if edge_attr["type"] == "use":
            elabel.append(f'used_{edge_attr.get("index")}')
            elabel = "\n".join(elabel)
            dot += f"\"{a}\" -> \"{b}\" [color=blue, \nlabel=\"{elabel}\"];\n"
        else:
            elabel.append(f'def_{edge_attr.get("index")}')
            elabel = "\n".join(elabel)
            dot += f"\"{a}\" -> \"{b}\" [color=green, \nlabel=\"{elabel}\"];\n"

    dot += "}"

    with open(filename, "w") as dump_file:
        dump_file.write(dot)

# Entry point for the analysis
def get_access_control_slots(project):
        
    # Grab all the JUMPIs in the project 
    jumpis = [ins for ins in project.statement_at.values() if ins.__internal_name__ == "JUMPI" ]
    log.debug(f'Found {len(jumpis)} JUMPIs in the project')
    
    '''
    jumpi_that_reverts = []
    for jumpi in jumpis:
        stmts = []
        jumpi_block = project.block_at[jumpi.block_id]
        
        successors_blocks = jumpi_block.succ
        for succ_block in successors_blocks:
            stmts.extend([x.__internal_name__ for x in succ_block.statements])

        if "REVERT" in stmts:
            jumpi_that_reverts.append(jumpi)

    jumpis = jumpi_that_reverts
    log.debug(f'Found {len(jumpis)} JUMPIs that reverts')
    '''
    
    critical_slots = set()

    # Let's analyze the JUMPIs that revert    
    for jumpi in jumpis:
        block = project.block_at[jumpi.block_id]
        func =  block.function
        
        # Get the variable that holds the condition of the JUMPI
        condition = jumpi.arg2_var
        trace = []
        #log.info(f'Initial JUMPI condition at {condition} in function {func.id}')
        rev_explorer = ReverseExplorer(project, ReverseExplorerState(project, func, condition))
        rev_explorer.run()
        full_slice = set()

        for myslice in rev_explorer.slices:
            # Union of all the stmts here.
            for stmt in myslice.slices_stmts:
                full_slice.add(stmt)
        
        stmts_mnemonic_in_slice = [project.statement_at[x].__internal_name__ for x in full_slice]
        stmts_in_slice = [project.statement_at[x] for x in full_slice]
        log.debug(stmts_in_slice)
        
        if "CALLER" in stmts_mnemonic_in_slice and "EQ" in stmts_mnemonic_in_slice and "SLOAD" not in stmts_mnemonic_in_slice:
            log.debug(stmts_mnemonic_in_slice)
            log.debug(f'JUMPI at {jumpi.id} in function {func.name}:{func.signature} is a access control check! (CALLER+EQ)')
        
        elif "CALLER" in stmts_mnemonic_in_slice and "SLOAD" in stmts_mnemonic_in_slice and "SHA3" in stmts_mnemonic_in_slice:
            log.debug(stmts_mnemonic_in_slice)
            log.debug(f'JUMPI at {jumpi.id} in function {func.name}:{func.signature} is a access control check! (CALLER+SLOAD+SHA3)')

        elif "CALLER" in stmts_mnemonic_in_slice and "SLOAD" in stmts_mnemonic_in_slice and "SHA3" not in stmts_mnemonic_in_slice:
            log.debug(f'JUMPI at {jumpi.id} in function {func.name}:{func.signature} is a access control check! (CALLER+SLOAD)')
            for stmt in stmts_in_slice:
                if stmt.__internal_name__ == "SLOAD":
                    try:
                        slot = stmt.arg1_val.value
                        critical_slots.add(slot)
                        log.debug(f'  Possible slot of owner: {hex(slot)}')
                    except Exception as e:
                        pass         
        else:
            pass
    
    return critical_slots