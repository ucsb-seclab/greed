import sys 
import logging 
import networkx as nx
import sha3 

from SEtaac import Project
from SEtaac.TAC.base import TAC_Statement
from SEtaac import options
from SEtaac.utils import gen_exec_id
from SEtaac.utils.solver.shortcuts import *
from SEtaac.exploration_techniques import DFS, DirectedSearch, HeartBeat, SimgrViz

import networkx as nx 
import random


log = logging.getLogger("ShaResolver")
log.setLevel(logging.INFO)

# This function tries to spot 
# dependencies between SHA operations.
# e.g., SHA of SHA.
# Returns a graph representing the dependencies.
# TODO, maybe this is too expensive and we want to look into
#       alternative solutions like peeking into the constraints?
def detect_sha_dependencies(state):
    sha_deps = nx.DiGraph()
    
    if len(state.sha_observed) == 1:
        # Well, we are done.
        sha_deps.add_node(state.sha_observed[0])
        return sha_deps

    log.info("Checking SHA dependecies")

    for curr_sha in state.sha_observed:
        log.info(f"Checking dependencies for {curr_sha.symbol.name}")
        sha_deps.add_node(curr_sha)

        # Get a model for our SHA
        sha_model = get_fixed_sha_model(state, curr_sha)

        # Now, let's see what happened to the other SHAs
        for other_sha in state.sha_observed:
            if other_sha.symbol.name == curr_sha.symbol.name:
                # Skip the current SHA under analysis
                continue
            if sha_deps.has_edge(other_sha, curr_sha):
                # OPTIMIZATION: if sha1 depends from sha2, sha2 CANNOT depend from sha1, so skip that.
                continue

            # Can this other SHA still be concretized to 0? If yes, constraining the 
            # input buffer of 'sha_observed' didn't influence this SHA, hence, there 
            # is no dependency between these two SHAs.
            sha_model.add(Equal(other_sha.symbol, BVV(0,256)))
            if state.solver.are_formulas_sat(list(sha_model)):
                continue
            else:
                # Register the dependency
                log.info(f"{curr_sha.symbol.name} depends from {other_sha.symbol.name}")
                sha_deps.add_node(other_sha)
                sha_deps.add_edge(curr_sha, other_sha)
    
    # We return the transitive reduction :)
    return nx.transitive_reduction(sha_deps)


def get_keccak256(input_buffer, sha_size):
    keccak256 = sha3.keccak_256()
    input_buffer = bv_unsigned_value(input_buffer).to_bytes(bv_unsigned_value(sha_size), 'big')
    keccak256.update(input_buffer)
    res = keccak256.hexdigest()
    return res


def get_fixed_sha_model(state, sha_observed, input_buffer_blocked_sols=None):
    
    sha_model = {}

    sha_model['extras'] = set()

    sha_model['argOffset'] = set()
    sha_model['argSize'] = set()

    sha_model['blocked_argOffset'] = set()
    sha_model['blocked_argSize'] = set()
    sha_model['blocked_inputBuffer'] = set()

    # Null size doesn't make any sense for SHA, let's rule this out
    sha_model['extras'].add(NotEqual(sha_observed.size, BVV(0,256)))

    # Get some solutions 
    log.info(f"  [{sha_observed.symbol.name}] getting solution for argOffset")
    sha_arg_offset = state.solver.eval(sha_observed.start, raw=True)
    log.info(f"  [{sha_observed.symbol.name}] offsetArg at {hex(bv_unsigned_value(sha_arg_offset))}")
    log.info(f"  [{sha_observed.symbol.name}] getting solution for argSize")
    sha_size = state.solver.eval(sha_observed.size, raw=True)
    log.info(f"  [{sha_observed.symbol.name}] argSize at {hex(bv_unsigned_value(sha_size))}")
    log.info(f"  [{sha_observed.symbol.name}] getting solution for inputBuffer")

    sha_model['argOffset'].add(Equal(sha_observed.start, sha_arg_offset))
    sha_model['argSize'].add(Equal(sha_observed.size, sha_size))

    if input_buffer_blocked_sols:
        # MAKE SURE blocked_sols are of type raw.
        for blocked_sol in input_buffer_blocked_sols:
            state.solver.add_constraint(NotEqual(sha_observed.readn(BVV(0,256), sha_size), blocked_sol))
    
    sha_input_buffer = state.solver.eval_memory_at(sha_observed, BVV(0,256), sha_size, raw=True)

    log.info(f"Buffer for {sha_observed.symbol.name} set at {hex(bv_unsigned_value(sha_input_buffer))}")
    log.info(f"  [{sha_observed.symbol.name}] calculating concrete SHA")
    sha_result = get_keccak256(sha_input_buffer, sha_size)
    log.info(f"    [{sha_observed.symbol.name}] concrete SHA is {sha_result}")

    # Set constraints accordingly


    for x,b in zip(range(0, bv_unsigned_value(sha_size)), 
                            bv_unsigned_value(sha_input_buffer).to_bytes(bv_unsigned_value(sha_size), 'big')):
        sha_model.add(Equal(sha_observed[BVV(x,256)], BVV(b,8)))

    # Finally set the SHA result
    sha_model.add(Equal(sha_observed.symbol, BVV(int(sha_result,16),256)))

    return sha_model