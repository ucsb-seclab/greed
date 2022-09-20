import logging
import sys

import networkx as nx
from sha_resolver import detect_sha_dependencies, get_fixed_sha_model

from SEtaac import Project
from SEtaac import options
from SEtaac.TAC.base import TAC_Statement
from SEtaac.exploration_techniques import DFS, DirectedSearch, HeartBeat
from SEtaac.solver.shortcuts import *
from SEtaac.utils import gen_exec_id

log = logging.getLogger("Hackcess")
log.setLevel(logging.DEBUG)

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




# WARNING: this function modifies the state!
def resolve_sha_ops(state):
    # Let's detect first any dependencies among the SHAs.
    sha_deps = detect_sha_dependencies(state)

    # Now that we have the dependecies between SHAs, we want 
    # to resolve them starting from the leaves, up to the root SHAs.
    # NOTE: keep in mind that the graph possibly contains disjointed nodes.
    last_shas = [sha for sha in sha_deps.nodes() if sha_deps.out_degree(sha) == 0]
    
    log.info("Fixating all the SHAs")

    # This will contain the set of constraints that need to 
    # be added to the state 
    shas_models = {}
    for sha_observed in last_shas:
        log.info(f" Fixing {sha_observed.symbol.name}")
        shas_models[sha_observed.symbol.name] = get_fixed_sha_model(state, sha_observed)
        for pred_sha in nx.ancestors(sha_deps, sha_observed):
            log.info(f" Fixing {pred_sha.symbol.name}")
            shas_models[sha_observed.symbol.name] = get_fixed_sha_model(state, pred_sha)
    
    return shas_models


def analyze_state_at_call(base_state, target_call_info):
    # Here we want to grab more information regarding
    # the call.

    extra_formulas = set()
    # First thing, if any SHA3 happens, we need to fixate
    # them.
    if len(base_state.sha_observed) != 0:
        # WARNING: this function adds constraints to the state to fix 
        # the SHAs values in a new frame (i.e., push)
        extra_formulas.union(resolve_sha_ops(base_state))

    state = base_state.copy()

    # Fix the SHA model on this state.
    for ef in extra_formulas:
        # Well, technically I can push a new frame and add the constraints directly 
        # to the solver (without using add_assertions but directly assert formula).
        # IT'S A SUPER DIRTY HACK, BUT IT SHOULD MAKE THE TRICK AND SAVING THE COPY.
        # HOWEVER, HAVING THIS CONCEPT OF LAYERED SOLVER EVERYWHERE WOULD BE GREAT.
        state.add_constraint(ef)
    
    if len(target_call_info.contractAddresses) == 0:
        # This means we did not extract the targetContract statically, hence, we need
        # to know how many solutions we have for this.
        targetContract = state.solver.eval(state.registers[state.curr_stmt.arg1_var], raw=True)
        if state.solver.is_formula_sat(NotEqual(state.registers[state.curr_stmt.arg1_var], targetContract)):
            log.info(f"Multiple resolutions for CALL targetContract!")
        # TODO rest
    else:
        log.info(f"Fixated CALL targetContract at {hex(target_call_info.contractAddresses[0])}")

    log.info(f"Getting solution for memory at CALL")
    mem_offset_call = state.solver.eval(state.registers[state.curr_stmt.arg4_var], raw=True)        
    memory_at_call = state.solver.eval_memory_at(state.memory, mem_offset_call, BVV(4,256), raw=True)
    
    # Check if memory_at_call depends on SHAs (if any)
    if len(state.sha_observed) != 0:
        # Check: if I change SHA concretization, can I keep the memory_at_call the same or not?
        pass

    # Check how many solutions we have for memory_at_call
    if state.solver.is_formula_sat(NotEqual(state.memory.readn(mem_offset_call, BVV(4,256)), memory_at_call)):
        # If yes, this must be untainted, unless, maybe we want to try to change (1) mem_offset_call (if there are 
        # other solutions), or, the value of the SHAs we have fixated before
        # TODO TODO TODO
        log.info(f"Multiple resolutions for CALL targetFunction!")
    else:
        # If we are here we have a single solution, however it might be that this is just because 
        # we fixated the previous SHA. Let's try to fixate them to other values and see if it changes 
        # anything.
        log.info(f"CALL targets UNTAINTED function at {hex(bv_unsigned_value(memory_at_call))}")

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
    #init_ctx = {"CALLDATA": "0xe0ead80300000000000000000000000000000000000000000000000000000000000000SS"}
    max_calldatasize = 100 

    # Some state options
    options.GREEDY_SHA = False
    #options.LAZY_SOLVES = True

    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx, max_calldatasize=max_calldatasize)

    import ipdb; ipdb.set_trace()
    
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
    possible_entry_points = [f for f in p.function_at.values() if f.public and f.id != '0x0']
    entry_points = set()
    for ep in possible_entry_points:
        if nx.has_path(p.callgraph, source=ep, target=target_function):
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

    log.info("CALLS SUMMARY")
    for call in CallInfos.values():
        log.info(" 📞 "+str(call))


    import ipdb; ipdb.set_trace()

    

