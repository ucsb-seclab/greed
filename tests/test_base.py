import argparse

from SEtaac import Project
from SEtaac.utils import gen_exec_id

parser = argparse.ArgumentParser()
parser.add_argument('--target', type=str, action='store', help='Path to Gigahorse output folder', required=True)
args = parser.parse_args()

p = Project(f"{args.target}/IR_DICT.dill",
            f"{args.target}/TAC_CFG.dill")

xid = gen_exec_id()
entry_state = p.factory.entry_state(xid=1)
simgr = p.factory.simgr(entry_state=entry_state)

try:
    simgr.run()
except KeyboardInterrupt:
    pass

import IPython; IPython.embed()
