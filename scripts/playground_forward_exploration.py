#!/usr/bin/env python3
import argparse
import logging

import networkx as nx

from SEtaac import Project
from SEtaac import options
from SEtaac.utils import gen_exec_id
from SEtaac.utils.solver.shortcuts import *
from SEtaac.exploration_techniques import DFS, DirectedSearch

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("SEtaac")


def find_paths_with_stmt(p, target_stmt):
    target_block = p.factory.block(target_stmt.block_id)

    xid = gen_exec_id()
    entry_state = p.factory.entry_state(xid=xid)

    simgr = p.factory.simgr(entry_state=entry_state)

    try:
        options.LAZY_SOLVES = True
        simgr.run(find=lambda s: s.curr_stmt == target_stmt,
                  prune=lambda s: not is_reachable(s, target_block),
                  find_all=True)
    except KeyboardInterrupt:
        pass

    #print('found! now getting to a STOP/RETURN...')
    return simgr.found
    # todo: uncomment this part
    # simgr.move(from_stash='found', to_stash='active')
    # simgr._stashes['deadended'] = []
    # simgr._stashes['pruned'] = []
    #
    # target_stmts = [stmt for stmt in p.statement_at.values() if stmt.__internal_name__ in ['STOP', 'RETURN']]
    # target_blocks = [p.factory.block(stmt.block_id) for stmt in target_stmts]
    # try:
    #     simgr.run(find=lambda s: s.curr_stmt in target_stmts,
    #               prune=lambda s: not any([is_reachable(s, target_block) for target_block in target_blocks]),
    #               find_all=True)
    # except KeyboardInterrupt:
    #     pass
    #
    # return simgr.found


def execute_trace(entry_state, trace):
    p = entry_state.project

    simgr = p.factory.simgr(entry_state=entry_state)

    for target_stmt in trace:
        simgr.move(from_stash='found', to_stash='active')
        target_block = p.factory.block(stmt.block_id)
        simgr.run(find=lambda s: s.curr_stmt == target_stmt,
                  prune=lambda s: not is_reachable(s, target_block),
                  find_all=True)

    return simgr


def main(args):
    p = Project(target_dir=args.target)

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
    elif not target_block:
        print('Block not found.')
        exit(1)

    xid = gen_exec_id()
    entry_state = p.factory.entry_state(xid=xid)

    simgr = p.factory.simgr(entry_state=entry_state)

    options.LAZY_SOLVES = True

    directed_search = DirectedSearch(target_stmt)
    simgr.use_technique(directed_search)

    dfs = DFS()
    simgr.use_technique(dfs)

    try:
        simgr.run()
    except KeyboardInterrupt:
        pass

    import IPython; IPython.embed(); exit()


    # # todo: consider all critical paths
    # critical_paths = find_paths_with_stmt(p, target_stmt)
    # if not critical_paths:
    #     log.fatal('No paths found')
    #     exit()
    # critical_path = critical_paths[0]

    # this is to hi-jack a call
    # found.curr_stmt.set_arg_val(found)
    # found.constraints.append(found.curr_stmt.address_val == 0x41414141)
    # found.constraints.append(found.curr_stmt.value_val == 0x42424242)

    print(f"SAT: {critical_path.solver.is_sat()}")
    # calldata = bytes(solver.eval_one_array(critical_path.calldata.base, critical_path.MAX_CALLDATA_SIZE)).hex()
    # print(f'CALLDATA: {calldata}')

    # # find storage reads in critical path
    # critical_reads = dict()
    # for offset_term in critical_path.storage.reads:
    #     if not is_concrete(offset_term):
    #         raise Exception('NOT SUPPORTED: symbolic storage offset in critical reads')
    #     offset_concrete = bv_unsigned_value(offset_term)
    #     critical_reads[offset_term] = offset_concrete
    #
    # # find writes to storage offsets in critical reads
    # sstores = [s for s in p.statement_at.values() if s.__internal_name__ == 'SSTORE']
    # interesting_sstores = defaultdict(list)
    # for sstore in sstores:
    #     offset_term = sstore.arg1_val
    #     if not is_concrete(offset_term):
    #         # solver.is_formula_sat(Equal(sstore.arg1_val, list(critical_reads.keys())[0]))
    #         raise Exception('NOT SUPPORTED: symbolic storage offset in critical reads')
    #     # offset_concrete = bv_unsigned_value(offset_term)
    #     interesting_sstores[offset_term].append(sstore)
    #
    # for offset_term in critical_reads:
    #     num_offset_term_candidates = len(interesting_sstores[offset_term])
    #     for i in range(num_offset_term_candidates + 1):
    #         print(list(itertools.permutations(interesting_sstores[offset_term], i)))
    #         # here get the paths, prepend the paths, set initial storage, and re-trace all. if not sat, continue with the next attempt
    #         # probably need a nested loop for all paths for each sstore
    #         # actually "sat" here means that storage[offset_term] is set correctly, then we can continue to the other offset_terms
    #
    #
    # import IPython;
    # IPython.embed();
    # exit()



    # try to 1) set storage to the initial storage and 2) iteratively prepend new path combinations to the critical
    # path until we find one that's sat. With such approach, find a solution for each of the critical reads, one after
    # the other

    # score candidates for "how close to the solution" and "how many collisions with other storage offsets"


    #
    # # assume initial storage is all 0s
    # initial_storage = {idx: 0 for idx in critical_reads}
    #
    # # todo: assign the initial storage to the entry state and re-trace it?
    # sloads = [s for s in critical_path.trace if s.__internal_name__ == 'SLOAD']
    # sstores = [s for s in critical_path.trace if s.__internal_name__ == 'SSTORE']
    # # todo: if symbolic store maybe try to concretize calldata so that we can set storage to target values


    #
    # # find writes to storage offsets in constraints
    # storage_writes = defaultdict(list)
    # for addr, stmt in p.statement_at.items():
    #     if (stmt.__internal_name__ == 'SSTORE'):
    #         if stmt.key_val and stmt.value_val:
    #             storage_writes[addr].append((stmt.key_val, stmt.value_val))
    #         else:
    #             block = p.factory.block(stmt.block_id)
    #
    #             entry_state = p.factory.entry_state(xid=found.xid)
    #             simgr_tmp = p.factory.simgr(entry_state=entry_state)
    #             simgr_tmp.run(find=lambda s: s.curr_stmt == stmt,
    #                           prune=lambda s: not is_reachable(s, block),
    #                           find_all=True)
    #             for found_tmp in simgr_tmp.found:
    #                 # todo: make found_tmp reach a RETURN statement before dumping this
    #                 # todo: dump gadgets' side-effects
    #                 found_tmp.curr_stmt.set_arg_val(found_tmp)
    #                 storage_writes[addr].append({'idx': found_tmp.curr_stmt.key_val,
    #                                              'value': found_tmp.curr_stmt.value_val,
    #                                              'constraints': found_tmp.constraints,
    #                                              'side-effects': None})
    #
    # # storage_writes are atomic, try to combine them to obtain the result that we want (found.storage.)
    #
    # s_tmp = get_solver()
    # s_tmp.add(storage_writes['0x14a'][0]['constraints'])
    # s_tmp.add(storage_writes['0x14a'][0]['value'] == target_storage[0])
    # s_tmp.check()

    # print('critical paths: ', critical_paths)
    # IPython.embed()


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
