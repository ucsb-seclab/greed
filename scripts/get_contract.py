import argparse
import web3
import os 
import tempfile 
import requests
import sys

# Geth on the kapur machine
RPC_ENDPOINT = 'http://0.0.0.0:8545'

def is_contract(w3, contract_addr):
    if w3.eth.getCode(contract_addr).hex() != "0x":
        return True 
    else:
        return False


if __name__ == "__main__":
    address = sys.argv[1]
    w3 = web3.Web3(web3.Web3.HTTPProvider(RPC_ENDPOINT))
    
    if is_contract(w3, address):
        contract = w3.eth.contract(address=address)
        data = w3.eth.getCode(address).hex()
        with open("./contract.hex", "w") as contract_file:
            contract_file.write(data)