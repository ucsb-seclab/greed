import os 
from web3 import Web3

# w3 = Web3(Web3.WebsocketProvider('ws://localhost:8546'))
URL = "https://ropsten.infura.io/v3/8e233025e9624d29b8a8a22eaa13c6f5"
w3 = Web3(Web3.HTTPProvider(URL))

# Where to dump intermediate files 
WORKSPACE = "/tmp/.SEtaac"
isExist = os.path.exists(WORKSPACE)
if not isExist:
  # Create a new directory if it does not exist 
  os.makedirs(WORKSPACE)
