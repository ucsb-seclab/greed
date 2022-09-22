import sys 
import logging 
import networkx as nx

from SEtaac import Project
from SEtaac.TAC.base import TAC_Statement
from SEtaac import options
from SEtaac.utils import gen_exec_id
from SEtaac.exploration_techniques import DFS, DirectedSearch, HeartBeat, SimgrViz, Prioritizer

from SEtaac.static_analyses import run_backward_slice

#from taint_analyses import CalldataToFuncTarget, CalldataToContractTarget
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
        self.taintedContractAddress = None
        self.taintedFunction = None
        self.taintedArguments = None

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
        
        if self.taintedContractAddress is None:
            type_str += "*"
        else:
            if self.taintedContractAddress:
                type_str += "T"
            else:
                type_str += "U"

        if self.taintedFunction is None:
            type_str += "*"
        else:
            if self.taintedFunction:
                type_str += "T"
            else:
                type_str += "U"
        
        if self.taintedArguments is None:
            type_str += "*"
        else:
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
        ta1 = CalldataToContractTarget(state)
        
        assert(state.solver.frame == 0)
        
        ta1.run()
        tainted_targetContract = ta1.is_tainted
    
    assert(state.solver.frame==0)

    if len(target_call_info.functionAddresses) == 1:
        log.info(f"Fixated CALL targetFunc at {hex(target_call_info.functionAddresses[0])}")
    else:
        ta2 = CalldataToFuncTarget(state)
        ta2.run()
        tainted_targetFunc = ta2.is_tainted
    
    return tainted_targetContract, tainted_targetFunc
    

def analyze_call_from_ep(entry_point, target_call_info):
    #calldata, calldatasize = get_calldata_for(entry_point)

    #if calldata is None or calldatasize is None:
    #    return None

    # HACK 
    #init_ctx = {"CALLDATA": "0x7da1083a0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000aSSSSSSSSSSSSSSSSSSSS00000000000000000000000000"}
    
    # This is init_ctx for CallerTTU/CallerTUT
    #init_ctx =  {"CALLDATA": "0x7214ae99000000000000000000000000SSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS00000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000004SSSSSSSS00000000000000000000000000000000000000000000000000000000", "CALLDATASIZE":132}

    # This is a good init_ctx for JustTest002/JustTest001/ShaDepsTest
    #init_ctx = {"CALLDATA": "0x7da1083a0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000a000000SS00220000SS1100000000000000000000000000"}

    #init_ctx = {"CALLDATA": "0xe0ead80300000000000000000000000000000000000000000000000000000000000000SS"}
    #init_ctx = {"CALLDATA": "0x7214ae99"}

    #max_calldatasize =  132
    
    # Poly CALLDATA
    #calldata = "0xd450e04c00000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000002200000000000000000000000000000000000000000000000000000000000000420000000000000000000000000000000000000000000000000000000000000044000000000000000000000000000000000000000000000000000000000000004600000000000000000000000000000000000000000000000000000000000000143fd40012032be87b9bb23436540bc76314dd592bb74ceaba41f2bf693cabb82d67425d087050000000000000020f9ee9af32f0bfd0cc1a2cd29c1ad9e3370728f9c02545df490d55d9d1668aa3d0293f1141a785cfc5dbec2e1518e1b1d369154d0ce5796400200000000000000149a016ce184a22dbf6c17daa59eb7d3140dbd1c5406756e6c6f636bb90463656c3114aaaebe6fe48e54f431b0c390cfaf0b017d09d42d1429ecbae96a9b478d9c29e15444039658d24db635b45b29000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001408d8f59e475830d9a1bb97d74285c4d34c6dac08140bf451b2ab886ef67b12d2246afeaa3b37333555a091000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c6000000000000000000000000d2341c31f78f30d6ce46a78d9a54efe05bb1febf991cc79a1056aedf06737ac60000000000000000000000000000000000000000000000000000000000000000a7c7dd8851de5f6d6ac013ed027f21a635685ba0b271d3a837c0d318db751e31080fc0d03cbeafcbc4560caaeb6fd784be5786cdbc397d878903ed1b7e38280b41ef2163438b5c0199c999de4b8fedb5fd13017b226c6561646572223a322c227672665f76616c7565223a22425042643452795571686a65654a3947786f76686575585a4861596558523156694939572b3848723877734c4330334d624b7356584c6547676a453049393133763165385434685943775337676942727a46684a51306b3d222c227672665f70726f6f66223a2254356b77594c4e494251644e37694a78764473614874695272416b616545734856384c684167613772744946357646454c59746b3457385a414159705a4435554b45774e3551476841647650586e7a594d2b6c756f673d3d222c226c6173745f636f6e6669675f626c6f636b5f6e756d223a32323830303030302c226e65775f636861696e5f636f6e666967223a6e756c6c7d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c3f14300728fbe7a547c3643ddddafa0f8c97e54c23a76740cfeb4291ee527a5212d02219d9606637c73f6d7fad8270da734d9ecc61be2a6509e577f7640bc78bd0086405224535813f9cf386d236634da81c8fedcaf7a4914437bbf46acc8a9bac23c17d7cf8db521df9ff72d777160b698731f15819000b0db346875843067c93c00718a34cbc401906b657afe3c7410f48a25809b6e668830bf522875f135d83c7c32ed4d3e7c94643cb3af3ae1cbbd62e29abced3f6dc520289bcdafa424e09fd6000000000000000000000000000000000000000000000000000000000000"
    #calldatasize = 1381


    # Some state options
    options.GREEDY_SHA = False
    options.LAZY_SOLVES = False
    #options.STATE_INSPECT = True
    
    #log.info(f"CALLDATA: {calldata}")
    #log.info(f"CALLDATASIZE is {calldatasize}")

    #init_ctx = {"CALLDATA": calldata, "CALLDATASIZE": calldatasize}

    #entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx, max_calldatasize=max_calldatasize)
    entry_state = p.factory.entry_state(xid=xid, max_calldatasize=200)

    '''
    def bp(simgr, state):
        log.info(f"[💥] State at {state.pc} does SHA!")
    def bp2(simgr, state):
        log.info(f"[💥] Exiting OwnershipOf [{state.pc}]")
    '''
    def bp3(simgr, state):
        log.info(f"[💥] CALLPRIVATE CALLING [{hex(state.curr_stmt.arg1_val.value)}]")
    def bp4(simgr, state):
        log.info(f"[💥] RETURNPRIVATE RETURNING FROM FUNCTION")

    #entry_state.inspect.stop_at_stmt(stmt_name="CALLPRIVATE", func=bp3)
    #entry_state.inspect.stop_at_stmt(stmt_name="RETURNPRIVATE", func=bp4)
    #entry_state.inspect.stop_at_stmt(stmt_name="STATICCALL")
    #entry_state.inspect.stop_at_stmt(stmt_name="CALL")

    # Being of NextUint32
    def bp5(simgr, state):
        log.info(f"[💥] Entering NextUint32")
    def bp6(simgr, state):
        log.info(f"[💥] Exiting NextUint32")
    def bp7(simgr, state):
        log.info(f"[💥] Entering NextUint64")
    def bp8(simgr, state):
        log.info(f"[💥] Exiting NextUint64")
    def bp9(simgr, state):
        log.info(f"[💥] Entering deserializeHeader")
    def bp10(simgr, state):
        log.info(f"[💥] Entering NextHash")
    def bp11(simgr, state):
        log.info(f"[💥] Exiting NextHash")
    def bp12(simgr, state):
        log.info(f"[💥] Entering NextVarBytes")
    def bp13(simgr, state):
        log.info(f"[💥] Exiting NextVarBytes")
    def bp14(simgr, state):
        log.info(f"[💥] Entering NextVarUint")
    def bp15(simgr, state):
        log.info(f"[💥] Exiting NextVarUint")
    def bp16(simgr, state):
        log.info(f"[💥] Entering NextByte")
    def bp17(simgr, state):
        log.info(f"[💥] Exiting NextByte")

    '''
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x2559", func=bp5)
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x25e2", func=bp7)
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x255e")
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x2560")
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x25e10x2559", func=bp6)
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x1a05", func=bp9)
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x255a", func=bp5)
 
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x25e3", func=bp7)
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x2668", func=bp8)
    
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x266a", func=bp10)
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x26ad", func=bp11)

    entry_state.inspect.stop_at_stmt_id(stmt_id="0x26af", func=bp12)
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x2761", func=bp13)

    entry_state.inspect.stop_at_stmt_id(stmt_id="0x2d68", func=bp14)
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x25e10x2d67", func=bp15)
    
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x2bd8", func=bp16)
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x2c1f", func=bp17)
    '''

    #entry_state.inspect.stop_at_stmt_id(stmt_id="0x3360")

    '''
    
    entry_state.inspect.stop_at_stmt(stmt_name="SHA3", func=bp)
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x1c03", func=bp2)
    entry_state.inspect.stop_at_stmt_id(stmt_id="0x1ac1") # Calculating nextTokenId
    '''
    
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
        
        # This is just for Poly
        #if c_id != "0x241e":
        #    continue
        
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
            #if ep.name == "safeTransferFrom(address,address,uint256,bytes)":
            #if ep.name == "verifyHeaderAndExecuteTx(bytes,bytes,bytes,bytes,bytes)":
            analyze_call_from_ep(ep, call)
            #else:
            #print(f"Skipping {ep.name}")

    log.info("CALLS SUMMARY")
    for call in CallInfos.values():
        log.info(" > "+str(call))
    

