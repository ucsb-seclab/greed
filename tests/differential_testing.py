#!/usr/bin/env python
import argparse
import os
import web3

from collections import defaultdict
from eth_dynamic.analysis import Analyzer, BaseAnalysisAddOn, CallTracer
from eth_dynamic.utils import LoadBalancedWebsocketProvider
from greed import Project
from greed.utils.files import load_csv
from greed.utils.extra import gen_exec_id


class ExternalCallError(BaseException):
    pass

class Tracer(BaseAnalysisAddOn):
    PRE_OPERATION_PRIORITY: int = 110
    POST_OPERATION_PRIORITY: int = 110
    POST_TRANSACTION_PRIORITY: int = 90

    def __init__(self, call_tracer: CallTracer, target_dir: str):
        self.call_tracer = call_tracer

        self.trace = list()
        self.block_trace = list()

        self.depth = 0

        self.p = Project(target_dir=target_dir)

        self.evm_to_tac = defaultdict(dict)
        for pc, func, tac in load_csv(f"{target_dir}/Statement_IRStatement.csv"):
            if tac not in self.p.statement_at:
                continue
            self.evm_to_tac[pc][func] = tac

    @staticmethod
    def peek_stack(computation, i):
        if computation._stack.values[-1 - i][0] is int:
            return computation._stack.values[-1 - i][1]
        else:
            return int.from_bytes(computation._stack.values[-1 - i][1], byteorder='big')

    def pre_opcode_hook(self, opcode, computation):
        self.depth = len(self.call_tracer.call_stack) - 1
        pc = hex(computation.code.program_counter - 0x1)

        if self.depth == 0 or (self.depth == 1 and opcode.mnemonic in ['CALL', 'STATICCALL', 'DELEGATECALL', 'CALLCODE']):
            op = None
            tac_pcs = None
            if pc in self.p.block_at:
                # print('-'*20)
                # print(f"Block {pc}")
                # print('-'*20)
                self.block_trace.append(pc)

            if pc in self.evm_to_tac:
                tac_pc = list(self.evm_to_tac[pc].values())[0]
                tac_pcs = list(self.evm_to_tac[pc].values())
                op = self.p.factory.statement(tac_pc)
                if len(self.evm_to_tac[pc]) == 1:
                    pass
                else:
                    op.arg_vals = {v: None for v in op.arg_vars}
                    op.res_vals = {v: None for v in op.res_vars}
            # print(f"[{pc}] {opcode.mnemonic} --> {op or '???'}")

            arg_vals = dict()
            res_vals = dict()
            if op is not None and opcode.mnemonic == op.__internal_name__:
                arg_vals = {v: Tracer.peek_stack(computation, i) for i, v in enumerate(op.arg_vars)}

            self.trace.append((op, pc, tac_pcs, arg_vals, res_vals))
        
        elif (self.depth == 1 and opcode.mnemonic in ['RETURN', 'REVERT']):
            arg_vals = {v: Tracer.peek_stack(computation, i) for i, v in enumerate(['offset', 'size'])}
            res_vals = {'returndata': computation.memory_read_bytes(arg_vals['offset'], arg_vals['size'])}
            self.trace.append((opcode.mnemonic, pc, None, arg_vals, res_vals))


    def post_opcode_hook(self, opcode, computation):
        if self.depth == 0 or (self.depth == 1 and opcode.mnemonic in ['CALL', 'STATICCALL', 'DELEGATECALL', 'CALLCODE']):
            backup = list()
            op, pc, tac_pcs, arg_vals, res_vals = self.trace[-1]
            if opcode.mnemonic in ['CALL', 'STATICCALL', 'DELEGATECALL', 'CALLCODE'] and op in ['RETURN', 'REVERT']:
                backup = [self.trace.pop()]

                op, pc, tac_pcs, arg_vals, res_vals = self.trace[-1]

            if pc != hex(computation.code.program_counter - 0x1):
                return

            if op is not None and opcode.mnemonic == op.__internal_name__:
                self.trace.pop()
                res_vals = {v: Tracer.peek_stack(computation, i) for i, v in enumerate(op.res_vars)}
                self.trace.append((op, pc, tac_pcs, arg_vals, res_vals))

            self.trace += backup
        

def retrace(tracer, tx_data, block_info):
    xid = gen_exec_id()

    init_ctx = {
        "CALLDATA": tx_data["input"],
        "CALLDATASIZE": len(tx_data["input"][2:]) // 2,
        "CALLER": tx_data["from"],
        "ORIGIN": tx_data["from"],
        "ADDRESS": tx_data["to"],
        "NUMBER": tx_data["blockNumber"],
        "DIFFICULTY": block_info["totalDifficulty"],
        "TIMESTAMP": block_info["timestamp"]
    }

    state = tracer.p.factory.entry_state(xid=xid, init_ctx=init_ctx)

    # init empty simgr
    simgr = tracer.p.factory.simgr(entry_state=state)
    simgr.active.pop()

    # execute and actually follow the control flow, when we desync (different block) wait for greed to get back in sync
    print("\n\n")
    print('-' * 20)

    MAX_DESYNC = 10

    print(f"{'py-evm':^60} | {'greed':^60}")
    pyevm_str = f"[{tracer.trace[0][1]}] {tracer.trace[0][0]}"
    greed_str = f"[{state.pc}] {state.curr_stmt}"
    print(f"{pyevm_str:<60} | {greed_str:<60}")

    trace = list(tracer.trace[1:])
    for (pyevm_op, pc, tac_pcs, arg_vals, res_vals) in tracer.trace[1:]:
        while trace[0] != (pyevm_op, pc, tac_pcs, arg_vals, res_vals):
            trace.pop(0)
        trace.pop(0)

        if pyevm_op is None or state.pc in tac_pcs:
            continue

        old_state = state.copy()
        successors = simgr.single_step_state(state)

        if len(successors) == 0:
            # there are no successors
            print(f"Unrecoverable de-sync ({successors}), expected {tac_pcs}. there are no successors")
            exit(1)
        elif sum([s.pc in tac_pcs for s in successors]) > 1:
            # there are successors, and more than one is valid
            print(f"Unrecoverable de-sync ({successors}), expected {tac_pcs}. there are successors, and more than one is valid")
            exit(1)
        elif sum([s.pc in tac_pcs for s in successors]) == 1:
            # there are successors, and one of them is valid
            filtered_successors = [s for s in successors if s.pc in tac_pcs]
            state = filtered_successors[0]
        else:
            # there are successors, but none of them is valid. Try to get greed back in sync, stepping BFS
            state = old_state
            simgr = tracer.p.factory.simgr(entry_state=state)
            offset = len(state.trace) + 1

            for i in range(MAX_DESYNC):
                if simgr.found:
                    break
                simgr.step(find=lambda s: s.pc in tac_pcs)
            if not simgr.found:
                print(f"Unrecoverable de-sync({simgr}), expected {tac_pcs}. there are successors, but none of them is valid. failed to get greed back in sync")
                exit(1)
            state = simgr.one_found

            for op in state.trace[offset:]:
                greed_str = f"[{op.id}] {op}"
                print(f"{' ':<60} | {greed_str:<60}")

            # import IPython; IPython.embed(); exit()

        pyevm_str = f"[{pc}] {pyevm_op}"
        greed_str = f"[{state.pc}] {state.curr_stmt}"
        print(f"{pyevm_str:<60} | {greed_str:<60}")

        if pyevm_op.__internal_name__ in ['CALL', 'STATICCALL', 'DELEGATECALL', 'CALLCODE']:
            print(f"Stopping re-tracing on external call")
            return
        

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--blocks", nargs='+', type=int, action="store")
    parser.add_argument("--transactions", nargs='+', type=str, action="store")
    parser.add_argument("--analysis-path", type=str, action="store", default="/data/blockchain/contracts")

    args = parser.parse_args()

    # CONNECT TO GETH
    print('connecting to geth...')
    provider = LoadBalancedWebsocketProvider.auto_connect()
    w3 = web3.Web3(provider)
    assert w3.isConnected()
    print('connected')

    if (args.blocks and args.transactions) or (not args.blocks and not args.transactions):
        print("Illegal arguments. Please specify either --blocks or --transactions")
        exit(1)

    blocks = list()
    if args.transactions:
        for txn_hash in args.transactions:
            blocks.append(w3.eth.getTransaction(txn_hash)["blockNumber"])
    elif args.blocks:
        blocks = args.blocks

    for block_number in blocks:
        print(f"Retracing block: {block_number}")
        # LOOP THROUGH ALL TRANSACTIONS
        block_info = w3.eth.get_block(block_number)
        analyzer = Analyzer.from_block_number(w3, block_number)
        for txn_hash in block_info['transactions']:
            tx_data = w3.eth.getTransaction(txn_hash)

            addr = tx_data['to']
            if addr is None:
                continue

            target_dir = f"{args.analysis_path}/{addr[0:5]}/{addr}"

            # IF args.blocks, SKIP WHEN WE DON'T HAVE THE ANALYSIS
            if args.blocks and not os.path.isdir(target_dir):
                print(f"Replaying tx with missing target ({addr}): {txn_hash.hex()}")
                analyzer.next_transaction()
                continue
            # IF args.transactions, SKIP WHEN TRACING THE TX WAS NOT REQUESTED
            elif args.transactions and txn_hash.hex() not in args.transactions:
                print(f"Replaying tx: {txn_hash.hex()}")
                analyzer.next_transaction()
                continue
            elif not os.path.isdir(target_dir):
                print(f"Replaying REQUESTED tx because target is missing ({addr}): {txn_hash.hex()}")
                analyzer.next_transaction()
                continue

            # OTHERWISE RETRACE
            print(f"\n\n\nRetracing tx with target ({addr}): {txn_hash.hex()}")
            call_tracer = CallTracer()
            call_tracer.install_on(analyzer)

            tracer = Tracer(call_tracer, target_dir)
            tracer.install_on(analyzer)

            try:
                analyzer.next_transaction()
            except ExternalCallError:
                pass

            retrace(tracer, tx_data, block_info)
