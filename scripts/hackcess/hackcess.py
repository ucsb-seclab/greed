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

log = logging.getLogger("Hackcess")
log.setLevel(logging.INFO)

class CallInfo():
    def __init__(self, call_stmt):

        self.call_stmt = call_stmt

        # Classification TTT,UTT,UUU,...
        self.taintedContractAddress = True
        self.taintedFunction = True
        self.taintedArguments = True

        # list of destination contracts that can be called
        self.contractAddresses = list()
        # list of destination functions that can be called
        self.functionAddresses = list()
        # list of arguments that can be provided to the call
        self.argumentsValuse = list()

        # Stores here the values of the possible argsOffsets
        self.argsOffsets = list()
        # Stores here the values of the possible argsSizes
        self.argsSizes = list()
    
    @property
    def call_type(self):
        type_str = ""
        if self.taintedContractAddress:
            type_str += "T"
        else:
            type_str += "U"
        if self.taintedFunction:
            type_str += "T"
        else:
            type_str += "U"
        if self.taintedArguments:
            type_str += "T"
        else:
            type_str += "U"
        return type_str
        
    def __str__(self):
        return f"Call at {self.call_stmt.id} | call_type: {self.call_type}"


def get_keccak256(input_buffer, sha_size):
    keccak256 = sha3.keccak_256()
    input_buffer = bv_unsigned_value(input_buffer).to_bytes(bv_unsigned_value(sha_size), 'big')
    keccak256.update(input_buffer)
    res = keccak256.hexdigest()
    return res


# This function tries to spot 
# dependencies between SHA operations.
# e.g., SHA of SHA.
# Returns a graph representing the dependencies.
# TODO, maybe this is too expensive and we want to look into
#       alternative solutions like peeking into the constraints?
def detect_sha_dependencies(base_state):
    log.info("Checking SHA dependecies")
    sha_deps = nx.DiGraph()
    
    # WARNING: this might not be right, however, copy the state for EVERY
    # observed SHA is too expensive because we lose Yices incremental solving.
    # Maybe we can do something importing the Context? TODO 
    state = base_state.copy()

    for sha_observed in state.sha_observed:
        log.info(f"Checking dependencies for {sha_observed.symbol.name}")
        sha_deps.add_node(sha_observed)

        log.info(f" [{sha_observed.symbol.name}] checking if unconstrained")

        # NOTE: if the SHA has already been fixed by the symbolic-executor, 
        # we are going to be faster at fixing the next solutions, but afaik 
        # it should be safe to re-add constraints.

        fix_sha(state, sha_observed)
        
        # Now, let's see what happened to the other SHAs
        for other_sha in state.sha_observed:
            if other_sha.symbol.name == sha_observed.symbol.name:
                # Skip the current SHA under analysis
                continue
            # Can this other SHA still be concretized to 0? If yes, constraining the 
            # input buffer of 'sha_observed' didn't influence this SHA, hence, there 
            # is no dependency between this two SHAs.
            if state.solver.is_formula_sat(Equal(other_sha.symbol, BVV(0,256))):
                continue
            else:
                # Register the dependency
                log.info(f"{sha_observed.symbol.name} depends from {other_sha.symbol.name}")
                sha_deps.add_node(other_sha)
                sha_deps.add_edge(sha_observed, other_sha)
    
    # We return the transitive reduction :)
    return nx.transitive_reduction(sha_deps)


def fix_sha(state, sha_observed):

    # Null size doesn't make any sense for SHA, let's rule this out
    state.add_constraint(NotEqual(sha_observed.size, BVV(0,256)))
    # Get some solutions 
    log.info(f"  [{sha_observed.symbol.name}] getting solution for argOffset")
    sha_arg_offset = state.solver.eval_one(sha_observed.start, raw=True)
    log.info(f"  [{sha_observed.symbol.name}] getting solution for argSize")
    sha_size = state.solver.eval_one(sha_observed.size, raw=True)
    log.info(f"  [{sha_observed.symbol.name}] getting solution for inputBuffer")
    sha_input_buffer = state.solver.eval_one_array_at(sha_observed.memory, sha_arg_offset, sha_size, raw=True)
    log.info(f"  [{sha_observed.symbol.name}] calculating concrete SHA")
    sha_result = get_keccak256(sha_input_buffer, sha_size)
    log.info(f"    [{sha_observed.symbol.name}] concrete SHA is {sha_result}")

    # Set constraints accordingly
    state.add_constraint(Equal(sha_observed.start, sha_arg_offset))
    state.add_constraint(Equal(sha_observed.size, sha_size))
    for x,b in zip(range(0, bv_unsigned_value(sha_size)), 
                            bv_unsigned_value(sha_input_buffer).to_bytes(bv_unsigned_value(sha_size), 'big')):
        state.add_constraint(Equal(sha_observed.memory[BVV(bv_unsigned_value(sha_arg_offset)+x,256)], BVV(b,8)))
    
    # Finally set the SHA result
    state.add_constraint(Equal(sha_observed.symbol, BVV(int(sha_result,16),256)))


# WARNING: this function modifies the state!
def resolve_sha_ops(state):
    # This will contain the set of constraints that need to 
    # be added to the state 
    sha_models = set()

    # Let's detect first any dependencies among the SHAs.
    sha_deps = detect_sha_dependencies(state)

    # Now that we have the dependecies between SHAs, we want 
    # to resolve them starting from the leaves, up to the root SHAs.
    # NOTE: keep in mind that the graph possibly contains disjunted nodes.
    last_shas = [sha for sha in sha_deps.nodes() if sha_deps.out_degree(sha) == 0]
    
    log.info("Fixating all the SHAs")
    for sha_observed in last_shas:
        log.info(f" Fixing {sha_observed.symbol.name}")
        fix_sha(state, sha_observed)
        for pred_sha in nx.ancestors(sha_deps, sha_observed):
            log.info(f" Fixing {pred_sha.symbol.name}")
            fix_sha(state, pred_sha)
    
    return



def analyze_state_at_call(state, target_call_info):
    # Here we want to grab more information regarding
    # the call.

    # First thing, if any SHA3 happens, we need to fixate
    # them.
    resolve_sha_ops(state)
    
    if len(target_call_info.contractAddresses) == 0:
        # This means we did not extract the targetContract statically, hence, we need
        # to know how many solutions we have for this.
        targetContract = state.solver.eval_one(state.registers[state.curr_stmt.arg1_var])
        # TODO TODO TODO
        assert(False)
    
    import ipdb; ipdb.set_trace()

    mem_offset_call = state.solver.eval_one(state.registers[state.curr_stmt.arg4_var], raw=True)
    print(f"mem_offset_call at {bv_unsigned_value(mem_offset_call)}")
    args_size_call = state.solver.eval_one(state.registers[state.curr_stmt.arg5_var], raw=True)
    print(f"args_size_call at {bv_unsigned_value(args_size_call)}")

    memory_at_call = hex(state.solver.eval_one_array_at(state.memory, mem_offset_call, args_size_call))
    print(f"CALLDATA {calldata_value} - MEMORY AT CALL {memory_at_call}")

    return

def get_init_ctx_for(func):
    # This function will use the prototype recovery to 
    # return an appropiate init_ctx.
    # TODO TODO TODO TODO
    assert(func.public and func.name)
    
    data = ""
    return {"CALLDATA": func.name + data}, 100

def analyze_call_from_ep(entry_point, target_call_info):

    init_ctx, max_calldatasize = get_init_ctx_for(entry_point)
    
    # HACK 
    init_ctx = {"CALLDATA": "0x7da1083a0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000aSSSSSSSSSSSSSSSSSSSS00000000000000000000000000"}
    max_calldatasize = 100 

    # Some state options
    options.GREEDY_SHA = False
    #options.LAZY_SOLVES = True

    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx, max_calldatasize=max_calldatasize)
    simgr = p.factory.simgr(entry_state=entry_state)
    
    #simgrviz = SimgrViz()
    #simgr.use_technique(simgrviz)
    
    dfs = DFS()
    simgr.use_technique(dfs)

    directed_search = DirectedSearch(p.factory.statement(target_call_info.call_stmt.id))
    simgr.use_technique(directed_search)

    heartbeat = HeartBeat()
    simgr.use_technique(heartbeat)

    log.info(f"Symbolically executing from {entry_point.id} to CALL at {target_call_info.call_stmt.id}")
    simgr.run(find=lambda s: s.curr_stmt.id == target_call_info.call_stmt.id)
    log.info(f"✅ Found state for CALL at {target_call_info.call_stmt.id}!")

    for state in simgr.found:
        analyze_state_at_call(state, target_call_info)


# Here we want to understand from which function
# it is possible to reach this specific CALL statement. 
# Returns a list of entry-points that can reach the CALL.
def how_to_reach(p: Project, target_call:TAC_Statement):
    
    # TODO: if function is guarded, we should abort it, or, find 
    # if there is another contract that owns this specific contract.
    # basically reversing the chain even more.

    target_function = p.factory.block(target_call.block_id).function
    # If the function containing the CALL is public we are done.
    if target_function.public:
        return [target_function]

    # Otherwise, we need to find the entry points that lead to this CALL
    # using the callgraph.
    # To do that, we start from all the public functions, and see if they 
    # can reach the function.id of the CALL under analysis.
    possible_entry_points = [f for f in p.function_at.values() if f.public]
    entry_points = set()
    for ep in possible_entry_points:
        if nx.has_path(ep, target_function):
            entry_points.add(ep)
    
    return entry_points

CallInfos = dict()

if __name__ == "__main__":
    p = Project(target_dir=sys.argv[1])
    xid = gen_exec_id()


    # First of all, let's find all the CALL statements
    CallInfos = {s.id:CallInfo(s) for s in p.statement_at.values() if s.__internal_name__ == "CALL"}

    # Collect static information that can be useful for symbolic execution 
    # and for the classification of the CALL.
    for c_id, call in CallInfos.items():
        # [1] 
        # In the simplest case, the contract address should have been already 
        # propagated by Gigahorse, if this is statically known, in these cases
        # just grab it.
        contractAddress = None
        if call.call_stmt.arg2_val:
            contractAddress = call.call_stmt.arg2_val.value
        if contractAddress:
            log.info(f"CALL at {c_id} calls into contract address at {hex(contractAddress)}")
            CallInfos[c_id].taintedContractAddress = False
            CallInfos[c_id].contractAddresses.append(contractAddress)

        # [2]
        # Let's see if the CALL is reading its parameters from a statically known offset,
        # this can be helpful later to pre-constraint some symbolic variables.
        argOffset = None
        if call.call_stmt.arg4_val:
            argOffset = call.call_stmt.arg4_val.value
        if argOffset:
            log.info(f"CALL at {c_id} expect argOffset at {hex(argOffset)}")
            CallInfos[c_id].argsOffsets.append(argOffset)

        # [3]
        # Finally, let's check for known argsSize
        argSize = None
        if call.call_stmt.arg5_val:
            argSize = call.call_stmt.arg5_val.value
        if argSize:
            log.info(f"CALL at {c_id} expect argSize {hex(argSize)}")
            CallInfos[c_id].argsSizes.append(argSize)

        # [4] 
        # Entry points in the contract to reach this CALL
        entry_points = how_to_reach(p, call.call_stmt)

        if not len(entry_points):
            log.warning(f"Cannot find an entry point for CALL {call}. Skipping it.")
            continue
        
        for ep in entry_points:
            analyze_call_from_ep(ep, call)
        
        import ipdb; ipdb.set_trace()

    log.info("CALLS SUMMARY")
    for call in CallInfos.values():
        log.info(" 📞 "+str(call))


    import ipdb; ipdb.set_trace()

    