from SEtaac import Project

p = Project("/home/degrigis/projects/hackcess/SEtaac/SEtaac/tests/IR_DICT.dill", 
            "/home/degrigis/projects/hackcess/SEtaac/SEtaac/tests/TAC_CFG.dill")

block = p.factory.block('0x0')

for x in p.TAC_code_raw.keys():
    p.factory.block(x)

import ipdb; ipdb.set_trace()

#xid = gen_exec_id()
#entry_state = p.factory.entry_state(xid=1)
#simulation_manager = p.factory.simgr(entry_state=entry_state)