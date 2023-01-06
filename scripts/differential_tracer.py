#!/usr/bin/env python
import web3
import argparse

from collections import defaultdict
from eth_dynamic_tools.analysis import Analyzer, BaseAnalysisAddOn, CallTracer
from SEtaac import Project
from SEtaac.utils import load_csv, gen_exec_id


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

        if opcode.mnemonic in ['CALL', 'STATICCALL', 'DELEGATECALL', 'CALLCODE']:
            target = hex(Tracer.peek_stack(computation, 1))
            target = w3.toChecksumAddress(target)
            print(f"Call to {target}")

            this = self.call_tracer.call_stack[0].callee
            this = w3.toChecksumAddress(this)
            if target == this:
                print("DETECTED RE-ENTRANT CALL")
                # exit(1)

        if self.depth == 0:
            op = None
            tac_pcs = None
            if pc in self.p.block_at:
                print('-'*20)
                print(f"Block {pc}")
                print('-'*20)
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
            print(f"[{pc}] {opcode.mnemonic} --> {op or '???'}")

            arg_vals = dict()
            res_vals = dict()
            if op is not None and op.arg_vars:
                arg_vals = {v: Tracer.peek_stack(computation, i) for i, v in enumerate(op.arg_vars)}

            self.trace.append((op, pc, tac_pcs, arg_vals, res_vals))

    def post_opcode_hook(self, opcode, computation):
        if self.depth == 0:
            op, pc, tac_pcs, arg_vals, res_vals = self.trace[-1]

            if pc != hex(computation.code.program_counter - 0x1):
                return

            self.trace.pop()

            res_vals = dict()
            if op is not None and op.arg_vars:
                res_vals = {v: Tracer.peek_stack(computation, i) for i, v in enumerate(op.res_vars)}

            self.trace.append((op, pc, tac_pcs, arg_vals, res_vals))


def retrace(tracer, tx_data):
    xid = gen_exec_id()
    state = tracer.p.factory.entry_state(xid=xid, max_calldatasize=len(tx_data['input']))

    # execute and actually follow the control flow, when we desync (different block) wait for greed to get back in sync
    print("\n\n")
    print('-' * 20)

    MAX_DESYNC = 10

    print(f"{'py-evm':^60} | {'greed':^60}")
    pyevm_str = f"[{tracer.trace[0][1]}] {tracer.trace[0][0]}"
    greed_str = f"[{state.pc}] {state.curr_stmt}"
    print(f"{pyevm_str:<60} | {greed_str:<60}")
    for (pyevm_op, pc, tac_pcs, arg_vals, res_vals) in tracer.trace[1:]:
        if pyevm_op is None:
            continue

        successors = state.curr_stmt.handle(state)

        if len(successors) != 1:
            # try to recover multiple successors
            successors = [s for s in successors if s.pc in tac_pcs]
            assert len(successors) == 1, f"Unrecoverable de-sync ({successors})"
            state = successors[0]

        if state.pc not in tac_pcs:
            greed_str = f"[{state.pc}] {state.curr_stmt}"
            print(f"{' ':<60} | {greed_str:<60}")

            # try to get greed back in sync, stepping bfs
            simgr = tracer.p.factory.simgr(entry_state=state)
            offset = len(state.trace)

            for i in range(MAX_DESYNC):
                if simgr.found:
                    break
                simgr.step(find=lambda s: s.pc in tac_pcs)
            assert simgr.found, f"Unrecoverable de-sync, expected {tac_pcs}"
            state = simgr.one_found

            for op in state.trace[offset:]:
                greed_str = f"[{op.id}] {op}"
                print(f"{' ':<60} | {greed_str:<60}")

            # import IPython; IPython.embed(); exit()

        pyevm_str = f"[{pc}] {pyevm_op}"
        greed_str = f"[{state.pc}] {state.curr_stmt}"
        print(f"{pyevm_str:<60} | {greed_str:<60}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--tx-hash", type=str, action="store")
    parser.add_argument("--target-dir", type=str, action="store")
    parser.add_argument("--w3", type=str, default="ws://128.111.49.121:8546")

    args = parser.parse_args()

    # CONNECT TO GETH
    provider = web3.WebsocketProvider(
        args.w3,
        websocket_timeout=60 * 5,
        websocket_kwargs={
            'max_size': 1024 * 1024 * 1024,  # 1 Gb max payload
        },
    )
    w3 = web3.Web3(provider)
    assert w3.isConnected()

    # GET ANALYZER
    tx_data = w3.eth.getTransaction(args.tx_hash)
    block_number = tx_data['blockNumber']
    analyzer = Analyzer.from_block_number(w3, block_number)

    # RUN ANALYSIS
    for txn_hash in analyzer.block['transactions']:
        if txn_hash.hex() == args.tx_hash:
            print('-' * 20)
            # if this is the target transaction, register the analysis add on
            call_tracer = CallTracer()
            call_tracer.install_on(analyzer)

            tracer = Tracer(call_tracer, args.target_dir)
            tracer.install_on(analyzer)

            analyzer.next_transaction()

            retrace(tracer, tx_data)
            exit()

        print(f"Replaying non-target tx: {txn_hash.hex()}")

        analyzer.next_transaction()






