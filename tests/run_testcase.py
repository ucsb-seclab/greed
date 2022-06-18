#!/usr/bin/env python3

import argparse

from SEtaac import Project, utils
from SEtaac.utils import gen_exec_id

parser = argparse.ArgumentParser()
parser.add_argument('--target', type=str, action='store', help='Path to Gigahorse output folder', required=True)
args = parser.parse_args()

p = Project(f"{args.target}/IR_DICT.dill",
            f"{args.target}/TAC_CFG.dill")

xid = gen_exec_id()
entry_state = p.factory.entry_state(xid=xid)
simgr = p.factory.simgr(entry_state=entry_state)

def parse_log(state):
    log_stmt = state.curr_stmt

    # manually set arg_vals, since we didn't handle this statement yet
    log_stmt.set_arg_val(state)

    if not (log_stmt.offset_val == 0 and log_stmt.size_val == 0):
        return

    length_ptr = log_stmt.topic_val
    length = utils.bytes_to_int(state.memory.read(length_ptr, 32))

    value_ptr = log_stmt.topic_val + 32
    value = bytes(state.memory.read(value_ptr, length)).decode()

    print('--->', value)

while len(simgr.active) > 0:
    simgr.run(find=lambda s: s.curr_stmt.__internal_name__ == 'LOG1')
    for s in simgr.found:
        parse_log(s)

    simgr.move(from_stash='found', to_stash='active')


