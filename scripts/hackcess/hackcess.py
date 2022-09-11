import sys 
import logging 
import networkx as nx

from SEtaac import Project
from SEtaac.TAC.base import TAC_Statement
from SEtaac import options
from SEtaac.utils import gen_exec_id
from SEtaac.exploration_techniques import DFS, DirectedSearch, HeartBeat, SimgrViz, Prioritizer

from SEtaac.static_analyses import run_backward_slice

from taint_analyses import CalldataToFuncTarget, CalldataToContractTarget
from init_ctx_generator import get_calldata_for



import random

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
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
            type_str += "*"
        else:
            type_str += "*"
        return type_str
        
    def __str__(self):
        return f"Call at {self.call_stmt.id} | call_type: {self.call_type}"


def analyze_state_at_call(state, target_call_info):
    static_targetContract = False
    tainted_targetContract = False
    tainted_targetFunc = False 

    if len(target_call_info.contractAddresses) == 1:
        log.info(f"Fixated CALL targetContract at {hex(target_call_info.contractAddresses[0])}")
        static_targetContract = True
    else:
        #ta1 = CalldataToContractTarget(state, source_start=68, source_end=77)
        ta1 = CalldataToContractTarget(state, source_start=4)
        ta1.run()
        tainted_targetContract = ta1.is_tainted
    
    assert(state.solver.frame==0)

    if len(target_call_info.functionAddresses) == 1:
        log.info(f"Fixated CALL targetFunc at {hex(target_call_info.functionAddresses[0])}")
    else:
        if not static_targetContract:
            ta2 = CalldataToFuncTarget(state, source_start=4, sha_deps=ta1.sha_resolver.sha_deps)
        else:
            ta2 = CalldataToFuncTarget(state, source_start=4)
        ta2.run()
        tainted_targetFunc = ta2.is_tainted
    
    return tainted_targetContract, tainted_targetFunc
    

def analyze_call_from_ep(entry_point, target_call_info):
    calldata, calldatasize = get_calldata_for(entry_point)

    if calldata is None or calldatasize is None:
        return None

    # HACK 
    #init_ctx = {"CALLDATA": "0x7da1083a0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000aSSSSSSSSSSSSSSSSSSSS00000000000000000000000000"}
    
    # This is init_ctx for CallerTTU/CallerTUT
    #init_ctx =  {"CALLDATA": "0x7214ae99000000000000000000000000SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS00000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004SSSSSSSS00000000000000000000000000000000000000000000000000000000", "CALLDATASIZE":132}

    # This is a good init_ctx for JustTest002/JustTest001/ShaDepsTest
    #init_ctx = {"CALLDATA": "0x7da1083a0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000a000000SS00220000SS1100000000000000000000000000"}

    #init_ctx = {"CALLDATA": "0xe0ead80300000000000000000000000000000000000000000000000000000000000000SS"}
    #init_ctx = {"CALLDATA": "0x6ecd2306"}

    #max_calldatasize =  132

    # Some state options
    options.GREEDY_SHA = False
    options.LAZY_SOLVES = False
    #options.STATE_INSPECT = True
    
    log.info(f"CALLDATA: {calldata}")
    log.info(f"CALLDATASIZE is {calldatasize}")

    init_ctx = {"CALLDATA": calldata, "CALLDATASIZE": calldatasize}

    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx)    

    #entry_state.inspect.stop_at_stmt(stmt_name="SHA3")
    
    simgr = p.factory.simgr(entry_state=entry_state)
    
    directed_search = DirectedSearch(target_call_info.call_stmt)
    simgr.use_technique(directed_search)

    prioritizer = Prioritizer(scoring_function=lambda s: -s.globals['directed_search_distance'])
    simgr.use_technique(prioritizer)

    #simgrviz = SimgrViz()
    #simgr.use_technique(simgrviz)

    heartbeat = HeartBeat(beat_interval=100)
    simgr.use_technique(heartbeat)

    log.info(f"Symbolically executing from {entry_point.name} to CALL at {target_call_info.call_stmt.id}")
    simgr.run(find=lambda s: s.curr_stmt.id == target_call_info.call_stmt.id)
    
    for state in simgr.found:
        log.info(f"✅ Found state for CALL at {target_call_info.call_stmt.id}!")
        
        # If LAZY_SOLVES is ON, we need to check if the state is SAT
        if not state.solver.is_sat():
            log.warning(f"❌ Found state is UNSAT :(")
            continue

        assert(state.solver.frame==0)
        tainted_targetContract, tainted_targetFunc = analyze_state_at_call(state, target_call_info)
        target_call_info.taintedContractAddress = tainted_targetContract
        target_call_info.taintedFunction = tainted_targetFunc
    
    if len(simgr.found) == 0:
        log.info(f"❌ Could not reach state for CALL at {target_call_info.call_stmt.id}!")

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
            for path in nx.all_simple_paths(p.callgraph, source=ep, target=target_function):
                log.info(f"{[func.name for func in path]}")
            entry_points.add(ep)
    
    return entry_points

CallInfos = dict()


if __name__ == "__main__":
    p = Project(target_dir=sys.argv[1])
    xid = gen_exec_id()

    # First of all, let's find all the CALL statements
    CallInfos = {s.id:CallInfo(s) for s in p.statement_at.values() if s.__internal_name__ == "CALL"}
    log.info(f"Found {len(CallInfos.keys())} CALLs:")
    for n, call in enumerate(CallInfos.values()):
        log.info(f" [{n}] CALL at {call.call_stmt.id}")

    # Collect static information that can be useful for symbolic execution 
    # and for the classification of the CALL.
    for c_id, call in CallInfos.items():
        log.info(f"Investigating CALL at {c_id}")
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
            #if ep.name != "safeTransferFrom(address,address,uint256,bytes)":
            #    continue
        
            analyze_call_from_ep(ep, call)

    log.info("CALLS SUMMARY")
    for call in CallInfos.values():
        log.info(" > "+str(call))


    import ipdb; ipdb.set_trace()

    

