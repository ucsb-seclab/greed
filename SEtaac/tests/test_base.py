from SEtaac.utils import gen_exec_id
from SEtaac import Project

p = Project("./IR_DICT.dill", "./TAC_CFG.dill")

xid = gen_exec_id()
entry_state = p.factory.entry_state(xid=xid)
simulation_manager = p.factory.simgr(entry_state=entry_state)

import IPython; IPython.embed()
#import ipdb; ipdb.set_trace()