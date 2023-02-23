#!/usr/bin/env python3
import argparse
import hashlib
import logging

from web3 import Web3

from greed import Project
from greed import options
from greed.exploration_techniques import ExplorationTechnique
from greed.utils import gen_exec_id
from greed.utils.solver.shortcuts import *

LOGGING_FORMAT = "%(levelname)s | %(name)s | %(message)s"
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger("greed")

# get w3 instance
w3 = Web3(Web3.HTTPProvider('http://127.0.0.1:8545'))


class MonitorSLOAD(ExplorationTechnique):
    def __init__(self):
        self.offsets = list()

    def check_state(self, simgr, state):
        if state.curr_stmt.__internal_name__ == "SLOAD":
            storage_offset = state.curr_stmt.arg1_val
            assert is_concrete(storage_offset), "SLOAD from symbolic offset"
            self.offsets.append(bv_unsigned_value(storage_offset))

        return state


def get_hash(contract_address):
    # fetch the code from the blockchain
    code = bytes.fromhex(w3.eth.getCode(contract_address).hex()[2:])

    # calculate hash
    return hashlib.sha256(code).hexdigest()


def get_reference_contract_address(address):
    _hash = get_hash(address)

    with open(f'/media/nicola-eth-parallel/data/get_hash.parallel/results/{_hash}') as f:
        return f.readlines()[0].strip()


def get_all_clone_addresses(address):
    _hash = get_hash(address)

    with open(f'/media/nicola-eth-parallel/data/get_hash.parallel/results/{_hash}') as f:
        return [l.strip() for l in f.readlines()]


def main(args):
    proxy_contract_address = args.target.split("/")[-1]
    proxy_contract_address = w3.toChecksumAddress(proxy_contract_address)
    assert w3.isChecksumAddress(proxy_contract_address), f"invalid contract address {proxy_contract_address}"

    proxy_contract_address = get_reference_contract_address(proxy_contract_address)
    
    p = Project(target_dir=args.target)

    # find start address (block) of function implementation()
    implementation_func_sig = "0x5c60da1b"
    for addr, f in p.function_at.items():
        if f.signature == implementation_func_sig:
            implementation_func_addr = addr
            break
    else:
        print("error: not a proxy contract")
        exit(1)

    # initialize simulation manager
    xid = gen_exec_id()
    init_ctx = {"CALLDATA": implementation_func_sig}
    entry_state = p.factory.entry_state(xid=xid, init_ctx=init_ctx, max_calldatasize=4)
    simgr = p.factory.simgr(entry_state=entry_state)
    options.LAZY_SOLVES = False

    # explore up to the implementation function's entry point
    try:
        simgr.run(find=lambda s: s.curr_stmt.block_id == implementation_func_addr)
    except KeyboardInterrupt:
        pass
    assert simgr.one_found, "could not reach implementation function"

    # add MonitorSLOAD exploration technique and prepare simulation manager
    monitor_sload = MonitorSLOAD()
    simgr.use_technique(monitor_sload)

    simgr.move(from_stash="active", to_stash="pruned")
    simgr.move(from_stash="found", to_stash="active")

    # run and monitor implementation()
    simgr.run()

    # lookup implementation contract
    assert len(monitor_sload.offsets) == 1, f"error while processing SLOADS ({monitor_sload.offsets})"
    sload_offset = monitor_sload.offsets[0]

    implementations_inspected = list()
    for clone_proxy_contract_address in get_all_clone_addresses(proxy_contract_address):
        print("-"*20)
        print(f"inspecting proxy contract {clone_proxy_contract_address}")
        sload_value_onchain = w3.eth.get_storage_at(clone_proxy_contract_address, sload_offset)

        implementation_contract_address = "0x"+sload_value_onchain.hex()[-40:]
        implementation_contract_address = w3.toChecksumAddress(implementation_contract_address)

        if implementation_contract_address in implementations_inspected:
            continue
        else:
            implementations_inspected.append(implementation_contract_address)
            print(f"found implementation: {implementation_contract_address}")

        with open(f"{args.target}/IsStorageIndex.csv") as f:
            proxy_storage = set([l.strip().split('\t')[0] for l in f.readlines()])

        try:
            implementation_contract_reference_address = get_reference_contract_address(implementation_contract_address)
            with open(f"{args.target.replace(clone_proxy_contract_address, implementation_contract_reference_address)}/IsStorageIndex.csv") as f:
                implementation_storage = set([l.strip().split('\t')[0] for l in f.readlines()])
        except:
            print("ERROR")
            continue

        found_overlap = False
        for offset in proxy_storage.intersection(implementation_storage):
            found_overlap = True
            print(f"FOUND POTENTIAL OVERLAP: {offset}")
        if not found_overlap:
            print("NO OVERLAP FOUND")

    #import IPython; IPython.embed();

    # todo
    # 1. rename bytecode.hex -> contract.hex for all contracts
    # 2. find all duplicate contracts and add symlinks in gigahorse's folder
    # 3. find all duplicate for proxies in "all_proxies" and add to proxy list (these are multiple deployment of the same proxy that could point to different implementations)
    #    ^^^ actually a shortcut is to recycle the analysis, query storage offsets for the proxy duplicates, and check if the implementation address is different


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument("target", type=str, action="store", help="Path to Gigahorse output folder")
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug output")

    args = parser.parse_args()

    # setup logging
    if args.debug:
        log.setLevel("DEBUG")
    else:
        log.setLevel("INFO")

    main(args)

