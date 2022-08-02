
import logging
import sys 

from SEtaac import Project
from SEtaac import options
from SEtaac.utils import gen_exec_id
from SEtaac.exploration_techniques import DFS, HeartBeat
from SEtaac.utils.solver.shortcuts import *


LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("SEtaac")

if __name__ == "__main__":
    p = Project(target_dir=sys.argv[1])

    for s in [s for s in p.statement_at.values() if s.__internal_name__ == 'CALLDATALOAD']:
        
        if s.byte_offset_val:
            if is_concrete(s.byte_offset_val):
                offset_val = bv_unsigned_value(s.byte_offset_val)
                print(f"[{s.id}] Access to CALLDATA[{offset_val}]")
        else:
            offset_val = s.byte_offset_var
        
        # Is the result register used in a comparison against 0xfffffffff? 
        register_result = s.res1_var
        
        # Let's look into the current block as of now 
        curr_block = p.factory.block(s.block_id)
        for stmt in curr_block.statements:
            if stmt.__internal_name__ == "GT":
                found_reg_result = False
                found_magic_constant = False
                
                for arg_var, arg_val in stmt.arg_vals.items():
                    if arg_var == register_result:
                        found_reg_result = True
                        continue
                    if is_concrete(arg_val):
                        if bv_unsigned_value(arg_val) == 0xffffffffffffffff:
                            found_magic_constant = True
                            continue
                if found_reg_result and found_magic_constant:
                    print(f"   CALLDATALOAD[{offset_val}] is an offset in the CALLDATA memory")



'''
for f in list(p.function_at.values()):
    # skip if no signature
    if f.signature is None:
        continue
            
    log.info(f"Analysing func: [{f.signature}]")

    log.info("  Test 1: no arguments")
    init_ctx = {"CALLDATA": f.signature, "CALLDATASIZE": 4}
    entry_state = p.factory.entry_state(xid=gen_exec_id(), init_ctx=init_ctx)
    simgr = p.factory.simgr(entry_state=entry_state)
    simgr.use_technique(DFS())
    simgr.run()

    if len([s for s in simgr.states if s.revert]) == len(simgr.deadended):
        log.info("   Prototype is not empty")


    log.info("  Test 2: let's follow the CALLDATALOAD")
    init_ctx = {"CALLDATA": f.signature}
    entry_state = p.factory.entry_state(xid=gen_exec_id(), init_ctx=init_ctx)
    simgr = p.factory.simgr(entry_state=entry_state)
    simgr.use_technique(DFS())
    simgr.run(find=lambda s: s.curr_stmt.__internal_name__ == "CALLDATALOAD")
'''