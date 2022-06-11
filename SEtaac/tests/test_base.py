from SEtaac import Project

p = Project("/home/degrigis/projects/hackcess/SEtaac/SEtaac/tests/IR_DICT.dill", 
            "/home/degrigis/projects/hackcess/SEtaac/SEtaac/tests/TAC_CFG.dill")

import ipdb; ipdb.set_trace()

#xid = gen_exec_id()
entry_state = p.factory.entry_state(xid=1)
simulation_manager = p.factory.simgr(entry_state=entry_state)

import ipdb; ipdb.set_trace()