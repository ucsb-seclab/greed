#!/usr/bin/env python3
import IPython
import argparse
import logging
import z3
import networkx as nx

from SEtaac import Project
from SEtaac.utils import gen_exec_id, get_one_model, eval_one_array

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("SEtaac")


def is_directly_reachable(block_a, block_b, callgraph, factory):
    if block_a == block_b:
        return True
    elif block_a.function == block_b.function:
        # check if reachable in intra-procedural cfg
        return block_b in block_a.descendants
    elif block_a.function and block_b.function:
        # for each path (in the callgraph) from function_a to function_b
        callgraph_paths = nx.all_simple_paths(callgraph, block_a.function, block_b.function)
        for path in callgraph_paths:
            first_hop = path[1]
            # check if we can reach the "first hop" (i.e., any "CALLPRIVATE <first_hop>" in function_a)
            for callprivate_block_id in block_a.function.callprivate_target_sources[first_hop.id]:
                callprivate_block = factory.block(callprivate_block_id)
                return is_directly_reachable(block_a, callprivate_block, callgraph, factory)
    else:
        assert block_a.id == 'fake_exit' or block_b.id == 'fake_exit'
        return False


def is_indirectly_reachable(state_a, block_b):
    factory = state_a.project.factory
    callgraph = state_a.project.callgraph

    block_a_id = state_a.curr_stmt.block_id
    block_a = factory.block(block_a_id)
    if is_directly_reachable(block_a, block_b, callgraph, factory):
        return True
    elif not state_a.callstack:
        return False
    else:
        # then look at callstack
        callstack = list(state_a.callstack)
        while callstack:
            return_stmt_id, _ = callstack.pop()
            return_stmt = factory.statement(return_stmt_id)
            return_block = factory.block(return_stmt.block_id)

            # check if any RETURNPRIVATE is reachable
            for returnprivate_block_id in block_a.function.returnprivate_block_ids:
                returnprivate_block = factory.block(returnprivate_block_id)
                if is_directly_reachable(block_a, returnprivate_block, callgraph, factory):
                    break
            else:
                # executed if there is no break
                return False

            if is_directly_reachable(return_block, block_b, callgraph, factory):
                return True
        return False


def main(args):
    p = Project(target_dir=args.target)

    xid = gen_exec_id()
    entry_state = p.factory.entry_state(xid=xid)

    # target_block_id = '0x115'
    # target_block_id = '0x30e0x1f5'
    # target_block_id = '0x1820x16f'
    # target_block_id = '0x18e1' --> this is never found (lost in constraint solving)
    # target_block_id = '0x507' --> this is never found (lost in constraint solving)

    if args.block:
        target_block_id = args.block
        target_block = p.factory.block(target_block_id)
        target_stmt = target_block.first_ins
    elif args.stmt:
        target_stmt_id = args.stmt
        target_stmt = p.factory.statement(target_stmt_id)
        target_block = p.factory.block(target_stmt.block_id)
    else:
        print('Please specify either a target statement or a target block.')
        exit(1)

    if not target_stmt:
        print('Target not found.')
        exit(1)

    simgr = p.factory.simgr(entry_state=entry_state)

    try:
        simgr.run(find=lambda s: s.curr_stmt == target_stmt,
                  prune=lambda s: not is_indirectly_reachable(s, target_block))
    except KeyboardInterrupt:
        pass

    found = simgr.one_found
    print('found! now concretizing calldata...')

    # this is to hi-jack a call
    # found.curr_stmt.set_arg_val(found)
    # found.constraints.append(found.curr_stmt.address_val == 0x41414141)
    # found.constraints.append(found.curr_stmt.value_val == 0x42424242)


    s = found.solver
    model = get_one_model(s)
    calldata = bytes(eval_one_array(model, found.calldata, model[found.calldatasize].as_long())).hex()
    print(f'CALLDATA: {calldata}')

    IPython.embed()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("target", type=str, action="store", help="Path to Gigahorse output folder")
    parser.add_argument("--block", type=str, action="store", help="Address of the target block")
    parser.add_argument("--stmt", type=str, action="store", help="Address of the target statement")
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug output")

    args = parser.parse_args()

    # setup logging
    if args.debug:
        log.setLevel("DEBUG")
    else:
        log.setLevel("INFO")

    main(args)
