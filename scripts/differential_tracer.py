#!/usr/bin/env python

import random
import copy
import argparse
import typing
import os
import sys
import web3
import web3.types
import web3.exceptions
import eth.chains.mainnet.constants

from collections import defaultdict

from eth.exceptions import (
    HeaderNotFound,
)
from eth_utils import (
    encode_hex
)
from eth_hash.auto import keccak
from eth_typing import Address, Hash32
from eth.vm.state import BaseState
from eth.vm.opcode import Opcode
from eth.vm.opcode_values import DIFFICULTY
from eth.abc import AccountDatabaseAPI, BlockHeaderAPI, DatabaseAPI, ComputationAPI, ChainContextAPI, \
    ExecutionContextAPI, AtomicDatabaseAPI, StateAPI, OpcodeAPI, SignedTransactionAPI
from eth.rlp.headers import BlockHeader
from eth.rlp.transactions import SignedTransactionMethods
from eth.constants import EMPTY_SHA3
from eth.rlp.sedes import *
from eth.db.chain import ChainDB
from eth.db.atomic import AtomicDB
from eth.db.header import _decode_block_header
from eth.validation import validate_canonical_address, validate_is_bytes, validate_word
from eth.vm.base import VM
from eth.vm.interrupt import (
    MissingBytecode,
)
from eth.db.backends.memory import MemoryDB
import eth.vm.forks
import eth.vm.forks.arrow_glacier
import eth.vm.forks.arrow_glacier.state
import eth.vm.forks.arrow_glacier.computation

from eth_account import Account
import eth_account.signers.local

from SEtaac.utils import load_csv, load_csv_map, load_csv_multimap
from SEtaac.TAC import tac_opcode_to_class_map
from SEtaac.solver.shortcuts import *
from SEtaac import Project
from SEtaac.utils import gen_exec_id

#
# Constants
#

# the opcode for PREVRANDAO
PREVRANDAO = DIFFICULTY

#
# Parse args (for testing)
#

parser = argparse.ArgumentParser()
parser.add_argument("tx_hash", type=str, action="store")
parser.add_argument("target_dir", type=str, action="store")

args = parser.parse_args()

#
# Connect to geth
#

web3_host = os.getenv('WEB3_HOST', 'ws://127.0.0.1:8546')

provider = web3.WebsocketProvider(
    web3_host,
    websocket_timeout=60 * 5,
    websocket_kwargs={
        'max_size': 1024 * 1024 * 1024,  # 1 Gb max payload
    },
)
w3 = web3.Web3(provider)
assert w3.isConnected()


tx_data = dict(w3.eth.getTransaction(args.tx_hash))
receipt_data = w3.eth.getTransactionReceipt(args.tx_hash)


#
# Helper functions
#

def build_block_header(w3: web3.Web3, block_number: int) -> BlockHeader:
    """
    Load a block header from geth in the format pyevm likes (not json)
    """
    result = w3.provider.make_request('debug_getHeaderRlp', [block_number])
    b = bytes.fromhex(result['result'][2:])
    return _decode_block_header(b)


def build_transaction(w3: web3.Web3, block_number: int, transaction_index: int) -> SignedTransactionMethods:
    """
    Load a transaction from geth in the format pyevm likes (not json)
    """
    raw_txn = w3.eth.get_raw_transaction_by_block(block_number, transaction_index)
    import ipdb;
    ipdb.set_trace()
    return get_vm_for_block(block_number).get_transaction_builder().decode(raw_txn)


#
# Stub classes that help plugging into pyevm
#

class StubChainContext:
    """only useful to specify chain id"""

    def __init__(self) -> None:
        self.chain_id = 1


class StubMemoryDB(MemoryDB):
    """
    in-memory database that loads from geth as a fallback

    expects access to global 'provider'
    """

    def __init__(
            self,
            w3: web3.Web3,
            kv_store: typing.Dict[bytes, bytes] = None
    ) -> None:
        self._w3 = w3
        super().__init__(kv_store)

    def __getitem__(self, key: bytes) -> bytes:
        if not super()._exists(key):
            got = provider.make_request('debug_dbGet', ['0x' + bytes(key).hex()])
            b = bytes.fromhex(got['result'][2:])
            super().__setitem__(key=key, value=b)
        return super().__getitem__(key)

    def __setitem__(self, key: bytes, value: bytes) -> None:
        self.kv_store[key] = value

    def _exists(self, key: bytes) -> bool:
        return key in self.kv_store

    def __delitem__(self, key: bytes) -> None:
        del self.kv_store[key]

    def __iter__(self) -> typing.Iterator[bytes]:
        return iter(self.kv_store)

    def __len__(self) -> int:
        return len(self.kv_store)

    def __repr__(self) -> str:
        return f"MemoryDB({self.kv_store!r})"


class MyChainDB(ChainDB):
    """
    Stub blockchain db that adds awareness of geth's storage scheme
    """

    @staticmethod
    def _get_block_header_by_hash(db: DatabaseAPI, block_hash: Hash32) -> BlockHeaderAPI:
        """
        Returns the requested block header as specified by block hash.

        Raises BlockNotFound if it is not present in the db.
        """
        validate_word(block_hash, title="Block Hash")
        try:
            bblock_number = db[b'H' + bytes(block_hash)]
            block_number = int.from_bytes(bblock_number, byteorder='big', signed=False)
            try:
                header_rlp = db[
                    b'h' +
                    int.to_bytes(block_number, length=8, signed=False, byteorder='big') +
                    bytes(block_hash)
                    ]
            except KeyError:
                # might be in the freezer
                resp = provider.make_request('debug_dbAncient', ['headers', block_number])
                if 'result' in resp:
                    header_rlp = bytes.fromhex(resp['result'][2:])
                else:
                    raise
        except KeyError:
            raise HeaderNotFound(f"No header with hash {encode_hex(block_hash)} found")
        return _decode_block_header(header_rlp)


#
# HACK - ADD SUPPORT FOR PARIS HARDFORK
#

PARIS_OPCODES = copy.deepcopy(eth.vm.forks.arrow_glacier.computation.ArrowGlacierComputation.opcodes)


def prevrandao(computation: ComputationAPI) -> None:
    computation.stack_push_int(computation.state.execution_context.prevrandao)


PARIS_OPCODES[PREVRANDAO] = Opcode.as_opcode(
    gas_cost=PARIS_OPCODES[DIFFICULTY].gas_cost,
    mnemonic='PREVRANDAO',
    logic_fn=prevrandao
)


class ParisComputation(eth.vm.forks.arrow_glacier.computation.ArrowGlacierComputation):
    opcodes: typing.Dict[int, OpcodeAPI] = PARIS_OPCODES


class ParisState(eth.vm.forks.arrow_glacier.state.ArrowGlacierState):
    computation_class: typing.Type[ComputationAPI] = ParisComputation


class ParisVM(eth.vm.forks.arrow_glacier.ArrowGlacierVM):
    """
    VM for Paris hardfork
    """
    # fork name
    fork = 'paris'

    _state_class: typing.Type[BaseState] = ParisState

    @classmethod
    def create_execution_context(
            cls,
            header: BlockHeaderAPI,
            prev_hashes: typing.Iterable[Hash32],
            chain_context: ChainContextAPI) -> ExecutionContextAPI:
        ret = super().create_execution_context(header, prev_hashes, chain_context)
        ret.prevrandao = int.from_bytes(header.mix_hash, byteorder='big', signed=False)
        return ret


#
# Hack for making the EVM debuggable via instruction hook
#

OpcodeHook = typing.Callable[[Opcode, ComputationAPI], typing.Any]


def sample_opcode_hook(
        opcode: Opcode,
        computation: ComputationAPI = None
):
    # print(f'{computation.msg.code_address.hex()}: {computation.code.program_counter} {opcode.mnemonic}')
    return opcode(computation=computation)


def get_vm_for_block(block_number: int, hook: OpcodeHook = None) -> typing.Type[VM]:
    """
    Construct the approprate VM for the given block number, and optionally insert the given hook
    to run after each instruction.
    """
    assert block_number >= eth.chains.mainnet.constants.PETERSBURG_MAINNET_BLOCK

    if block_number < eth.chains.mainnet.constants.ISTANBUL_MAINNET_BLOCK:
        TargetVM = eth.vm.forks.petersburg.PetersburgVM
    elif block_number < eth.chains.mainnet.constants.MUIR_GLACIER_MAINNET_BLOCK:
        TargetVM = eth.vm.forks.istanbul.IstanbulVM
    elif block_number < eth.chains.mainnet.constants.BERLIN_MAINNET_BLOCK:
        TargetVM = eth.vm.forks.muir_glacier.MuirGlacierVM
    elif block_number < eth.chains.mainnet.constants.LONDON_MAINNET_BLOCK:
        TargetVM = eth.vm.forks.berlin.BerlinVM
    elif block_number < eth.chains.mainnet.constants.ARROW_GLACIER_MAINNET_BLOCK:
        TargetVM = eth.vm.forks.london.LondonVM
    elif block_number < eth.chains.mainnet.constants.GRAY_GLACIER_MAINNET_BLOCK:
        TargetVM = eth.vm.forks.arrow_glacier.ArrowGlacierVM
    elif block_number < 15537394:
        TargetVM = eth.vm.forks.gray_glacier.GrayGlacierVM
    else:
        TargetVM = ParisVM

    TargetStateClass = TargetVM.get_state_class()
    TargetAccountDBClass = TargetStateClass.get_account_db_class()

    class MyAccountDb(TargetAccountDBClass):
        """
        Stub account db that adds awareness of geth's storage pattern

        most code copy+pasted from pyevm
        """
        called_set_balance = False

        def get_code(self, address: Address) -> bytes:
            validate_canonical_address(address, title="Storage Address")

            code_hash = self.get_code_hash(address)
            if code_hash == EMPTY_SHA3:
                return b''
            else:
                try:
                    return self._journaldb[b'c' + bytes(code_hash)]
                except KeyError:
                    raise MissingBytecode(code_hash) from KeyError
                finally:
                    if code_hash in self._get_accessed_node_hashes():
                        self._accessed_bytecodes.add(address)

        def set_code(self, address: Address, code: bytes) -> None:
            validate_canonical_address(address, title="Storage Address")
            validate_is_bytes(code, title="Code")

            account = self._get_account(address)

            code_hash = keccak(code)
            self._journaldb[b'c' + bytes(code_hash)] = code
            self._set_account(address, account.copy(code_hash=code_hash))

        def get_balance(self, address: Address) -> int:
            if not self.called_set_balance:
                return 10000000000000000000
            else:
                return super().get_balance(address)

        def set_balance(self, address: Address, balance: int) -> None:
            self.called_set_balance = True
            return super().set_balance(address, balance)

    class MyStateClass(TargetStateClass):
        """only used to pass account db stub"""
        account_db_class: typing.Type[AccountDatabaseAPI] = MyAccountDb

    class MyVM(TargetVM):
        """only used to pass account db stub (via MyStateClass)"""
        _state_class: typing.Type[BaseState] = MyStateClass

        # Stub this if you want to skip signature verification.
        def validate_transaction(
                self,
                transaction: SignedTransactionAPI
        ) -> None:
            return True

    if hook is not None:
        # stub opcodes with a hook
        for i, opcode in sorted(MyStateClass.computation_class.opcodes.items()):
            def new_call(opcode=opcode, **kwargs):  # use opcode=opcode to ensure it's bound to the func
                return hook(opcode, **kwargs)

            # copy+pasted from pyevm opcode.py
            props = {
                '__call__': staticmethod(new_call),
                'mnemonic': opcode.mnemonic,
                'gas_cost': opcode.gas_cost,
            }
            opcode_cls = type(f"opcode:{opcode.mnemonic}:stub", (Opcode,), props)

            # override opcode with our hooked one
            MyStateClass.computation_class.opcodes[i] = opcode_cls()

    return MyVM


raw_txn = w3.eth.get_raw_transaction(args.tx_hash)
txn = eth.vm.forks.gray_glacier.GrayGlacierVM.get_transaction_builder().decode(raw_txn)

db = MyChainDB(AtomicDB(StubMemoryDB(w3)))

p = Project(target_dir=args.target_dir)

evm_to_tac = defaultdict(dict)
for pc, func, tac in load_csv(f"{args.target_dir}/Statement_IRStatement.csv"):
    if tac not in p.statement_at:
        continue
    evm_to_tac[pc][func] = tac


depth = 0
block_trace = list()
trace = list()
trace_data = list()
def myhook(opcode: Opcode, computation: ComputationAPI):
    global depth

    def peek_stack(i):
        if computation._stack.values[-1 - i][0] is int:
            return computation._stack.values[-1 - i][1]
        else:
            return int.from_bytes(computation._stack.values[-1 - i][1], byteorder='big')

    pc = hex(computation.code.program_counter - 0x1)

    op = None
    tac_pcs = None
    if depth < 0:
        print(f"Invalid depth: {depth}")
        exit(1)
    elif depth == 0:
        if pc in p.block_at:
            print('-'*20)
            print(f"Block {pc}")
            print('-'*20)
            block_trace.append(pc)

        if pc in evm_to_tac:
            tac_pc = list(evm_to_tac[pc].values())[0]
            tac_pcs = list(evm_to_tac[pc].values())
            op = p.factory.statement(tac_pc)
            if len(evm_to_tac[pc]) == 1:
                pass
            else:
                op.arg_vals = {v: None for v in op.arg_vars}
                op.res_vals = {v: None for v in op.res_vars}
        print(f"[{pc}] {opcode.mnemonic} --> {op or '???'}")

    if opcode.mnemonic in ['RETURN', 'REVERT', 'SELFDESTRUCT', 'STOP']:
        depth -= 1
    elif opcode.mnemonic in ['CALL', 'CALLCODE', 'STATICCALL', 'DELEGATECALL']:
        depth += 1

    arg_vals = dict()
    if op is not None and op.arg_vars:
        arg_vals = {v: peek_stack(i) for i,v in enumerate(op.arg_vars)}

    opcode(computation=computation)

    res_vals = dict()
    if op is not None and op.res_vars:
        res_vals = {v: peek_stack(i) for i,v in enumerate(op.res_vars)}

    if op is not None:
        trace.append((op, pc, tac_pcs, arg_vals, res_vals))


block_number = tx_data['blockNumber']
VMClass = get_vm_for_block(block_number, myhook)
vm = VMClass(
    header=build_block_header(w3, block_number),
    chain_context=StubChainContext(),
    chaindb=db,
    consensus_context=None,
)

old_block = w3.eth.get_block(block_number - 1)
state_root = bytes(old_block['stateRoot'])

header = vm.get_header()
header = header.copy(gas_used=0, state_root=state_root)
execution_context = vm.create_execution_context(header, vm.previous_hashes, vm.chain_context)
vm._state = vm.get_state_class()(vm.chaindb.db, execution_context, header.state_root)

receipt, comp = vm.apply_transaction(
    header=header,
    transaction=txn,
)


xid = gen_exec_id()
state = p.factory.entry_state(xid=xid, max_calldatasize=len(txn.data))

# we can't do this because if a callprivate is not in the trace then the corresponding returnprivate will set wrong vars
# for (op, pc, arg_vals, res_vals) in trace:
#     print(f"Tracing: [{pc}] {op}")
#     state.pc = pc
#
#     if op.__internal_name__ not in ['CALLPRIVATE', 'RETURNPRIVATE']:
#         for v in op.arg_vars:
#             if state.solver.is_formula_unsat(Equal(state.registers[v], BVV(arg_vals[v], 256))):
#                 raise Exception(f"Wrong arguments for {v}")
#
#     op.handle(state)
#     assert state.solver.is_sat(), f"UNSAT [{pc}] {op}"
#
#     if op.__internal_name__ not in ['CALLPRIVATE', 'RETURNPRIVATE']:
#         for v in op.res_vars:
#             if state.solver.is_formula_unsat(Equal(state.registers[v], BVV(res_vals[v], 256))):
#                 raise Exception(f"Wrong results for {v}")

# execute and actually follow the control flow, when we desync (different block) wait for greed to get back in sync
print("\n\n")
print('-'*20)

print(f"{'py-evm':^60} | {'greed':^60}")
pyevm_str = f"[{trace[0][1]}] {trace[0][0]}"
greed_str = f"[{state.pc}] {state.curr_stmt}"
print(f"{pyevm_str:<60} | {greed_str:<60}")
for (pyevm_op, pc, tac_pcs, arg_vals, res_vals) in trace[1:]:
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
        simgr = p.factory.simgr(entry_state=state)
        offset = len(state.trace)
        for i in range(10):
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
