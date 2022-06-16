from SEtaac import Project
from SEtaac.utils import gen_exec_id

p = Project("./IR_DICT.dill",
            "./TAC_CFG.dill")

xid = gen_exec_id()
entry_state = p.factory.entry_state(xid=1)
simgr = p.factory.simgr(entry_state=entry_state)

try:
    simgr.run()
except KeyboardInterrupt:
    pass

import ipdb; ipdb.set_trace()
