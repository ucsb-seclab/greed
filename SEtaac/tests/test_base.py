from SEtaac import Project

p = Project("./IR_DICT.dill",
            "./TAC_CFG.dill")

project = p 

block = p.factory.block('0x0')
state = p.factory.entry_state(1)

# for x in blocks:
#     for s in x:
#         if s.__internal_name__ == 'CALLPRIVATE':
#             if s.res_vars:
#                 pass

import ipdb; ipdb.set_trace()

#xid = gen_exec_id()
#entry_state = p.factory.entry_state(xid=1)
#simulation_manager = p.factory.simgr(entry_state=entry_state)