import sys 

from SEtaac import Project
from SEtaac import options
from SEtaac.utils import gen_exec_id
from SEtaac.utils.solver.shortcuts import *
from SEtaac.exploration_techniques import TypeAware

if __name__ == "__main__":
    p = Project(target_dir=sys.argv[1])
    xid = gen_exec_id()
    
    for f in p.function_at.values():
        print(f"Exploring {f.signature}")
        if f.signature == None:
            continue
        init_ctx = {"CALLDATA": f.signature}
        entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx)
        simgr = p.factory.simgr(entry_state=entry_state)
        tase = TypeAware(f.signature)
        simgr.use_technique(tase)
        simgr.run()

        import ipdb; ipdb.set_trace()
