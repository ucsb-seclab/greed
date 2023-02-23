import sys

from greed import Project
from greed.exploration_techniques import DFS, DirectedSearch, HeartBeat
from greed.solver.shortcuts import *
from greed.utils import gen_exec_id


def run_it(entry_state, target_stmt):
    simgr = p.factory.simgr(entry_state=entry_state)
    
    #options.LAZY_SOLVES = True
    #simgrviz = SimgrViz()
    #simgr.use_technique(simgrviz)
    
    dfs = DFS()
    simgr.use_technique(dfs)

    directed_search = DirectedSearch(p.factory.statement(target_stmt))
    simgr.use_technique(directed_search)

    heartbeat = HeartBeat()
    simgr.use_technique(heartbeat)
    simgr.run(find=lambda s: s.curr_stmt.id == target_stmt)

    found = simgr.one_found
    
    #import ipdb; ipdb.set_trace()

    return found

JustTest001_CALL = "0x15b0x50"
JustTest002_CALL = "0xc10x45"
JustTest003_CALL = "0x15b0x50"

ShaTest_SHA = "0xb7"


# bytearray to hex 
# ''.join('{:02x}'.format(x) for x in aaa)


def test_calldata_with(state, values):
    state.solver.solver.push()
    assert(len(values) == 10 )
    idx = 68
    for x in values:
        new_cst = Equal(state.calldata[BVV(idx,256)], BVV(x,8))
        idx += 1 
        state.add_constraint(new_cst)

def break_calldata(state):
    state.solver.solver.push()
    new_cst = Equal(state.calldata[BVV(0,256)], BVV(0,8))
    state.add_constraint(new_cst) 
    
def see_calldata_memory_at_call(new_found):
    calldata_value = hex(new_found.solver.eval_one_array(new_found.calldata, BVV(100,256)))
    print(f"CALLDATA: {calldata_value}")
    mem_offset_call = new_found.solver.eval_one(new_found.registers[new_found.curr_stmt.arg4_var], raw=True)
    #print(f"mem_offset_call at {bv_unsigned_value(mem_offset_call)}")
    args_size_call = new_found.solver.eval_one(new_found.registers[new_found.curr_stmt.arg5_var], raw=True)
    #print(f"args_size_call at {bv_unsigned_value(args_size_call)}")

    memory_at_call = hex(new_found.solver.eval_one_array_at(new_found.memory, mem_offset_call, args_size_call))
    print(f"MEMORY AT CALL {memory_at_call}")
    new_found.solver.solver.pop()

if __name__ == "__main__":
    p = Project(target_dir=sys.argv[1])
    xid = gen_exec_id()
    
    # bytes start at offset 68 -> 77 (0x44)
    '''
    init_ctx = {"CALLDATA": "0x7da1083a0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000aSSSSSSSSSSSSSSSSSSSS00000000000000000000000000"}
    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx, max_calldatasize=100)

    #entry_state.add_breakpoint("0x4460x2060x2530x3b")
    
    found = run_it(entry_state, JustTest001_CALL)

    #import ipdb; ipdb.set_trace()
    calldata_value = found.solver.eval_one_array(found.calldata, 100)

    mem_offset_call = found.solver.eval_one(found.registers[found.curr_stmt.arg4_var])
    args_size_call = found.solver.eval_one(found.registers[found.curr_stmt.arg5_var])

    memory_at_call = hex(found.solver.eval_one_array_at(found.memory, mem_offset_call, args_size_call))
    print(f"CALLDATA {calldata_value} - MEMORY AT CALL {memory_at_call}")
    '''
    # Constraining it to 0
    #options.SIMGRVIZ = True
    #options.STATE_INSPECT = True
    
    #init_ctx =  {"CALLDATA": "0x7da1083a0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000a0000008000000000000000000000000000000000000000"}

    init_ctx = {"CALLDATA": "0x7da1083a0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000aSSSSSSSSSSSSSSSSSSSS00000000000000000000000000"}
    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx, max_calldatasize=100)
    #entry_state.inspect.stop_at_stmt_id("0x28a0xf10x50")


    '''
    calldata_csts = []
    for x in range(68,77):
        if x == 69:
            val = 5
        else:
            #import random
            #val = random.randint(0,100000)
            val = 0
        print(f"Setting CALLDATA[{x}] to {val}")
        new_cst = Equal(entry_state.calldata[BVV(x,256)], BVV(val,8))
        calldata_csts.append(new_cst)
        entry_state.add_constraint(new_cst)
    '''

    new_found= run_it(entry_state, JustTest001_CALL)
    calldata_value = hex(new_found.solver.eval_one_array_at(new_found.calldata, BVV(68,256), BVV(10,256)))

    mem_offset_call = new_found.solver.eval_one(new_found.registers[new_found.curr_stmt.arg4_var], raw=True)
    print(f"mem_offset_call at {bv_unsigned_value(mem_offset_call)}")
    args_size_call = new_found.solver.eval_one(new_found.registers[new_found.curr_stmt.arg5_var], raw=True)
    print(f"args_size_call at {bv_unsigned_value(args_size_call)}")

    memory_at_call = hex(new_found.solver.eval_one_array_at(new_found.memory, mem_offset_call, args_size_call))
    print(f"CALLDATA {calldata_value} - MEMORY AT CALL {memory_at_call}")

    #sha_symbol = new_found.sha_observed[0].symbol
    #print(f"VALUE FOR SHA SYMBOL WAS {hex(new_found.solver.eval_one(sha_symbol))}")
    
    import ipdb; ipdb.set_trace()


    '''
    init_ctx = {"CALLDATA": "0x7da1083a0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000a0112217440000000000000000000000000000000000000"}
    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx, max_calldatasize=100)
    calldata_csts = []

    for x in range(68,77):
        if x != 67:
            val = 3
        else:
            val = 2
        new_cst = Equal(entry_state.calldata[BVV(x,256)], BVV(val,8))
        calldata_csts.append(new_cst)
        entry_state.add_constraint(new_cst)

    new_found = run_it(entry_state, JustTest001_CALL)
    calldata_value = hex(new_found.solver.eval_one_array_at(new_found.calldata, 68, 10)[0])

    mem_offset_call = new_found.solver.eval_one(new_found.registers[new_found.curr_stmt.arg4_var])
    args_size_call = new_found.solver.eval_one(new_found.registers[new_found.curr_stmt.arg5_var])

    memory_at_call = hex(new_found.solver.eval_one_array_at(new_found.memory, mem_offset_call, args_size_call))
    print(f"CALLDATA {calldata_value} - MEMORY AT CALL {memory_at_call}")
    '''

    import ipdb; ipdb.set_trace()
    
    

    
