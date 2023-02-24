# greed

<img align="left" width="250"  src="greed.png">

A symbolic executor for the TAC IR used by Gigahorse

### Installation
```bash
# Clone this repo
git clone git@github.com:ucsb-seclab/greed.git
# Create a virtual environment (e.g., using virtualenvwrapper)
mkvirtualenv greed
# Activate the virtual environment
workon greed
# Install greed
pip install -e greed
# Setup greed and gigahorse
./setup.sh
# Setup the preferred solver (bitwuzla or boolector)
./setup_yices2.sh
```

### Usage
First, the contract needs to be pre-processed with `gigahorse`. This can be done in two ways:
```bash
# IMPORTANT: create a new folder 
# Analyses will pollute the current working directory
mkdir /tmp/test_contract
cd /tmp/test_contract/

# From the solidity source
cp <contract_source> contract.sol
analyze_source.sh contract.sol

# From the contract bytecode
cp <contract_bytecode> contract.hex
analyze_contract_hex.sh contract.hex

# To get the decompiled source
decompile.sh contract.hex

```

The source analysis only works on `x86_64` systems. The bytecode analyses should work on any system where `gigahorse` can be properly compiled. 

Finally, to run `greed`:
```bash
greed /tmp/test_contract --debug
```

### Testing
```bash
# Manually run a single test using run_testcase.py
cd greed/tests
./run_testcase.py test_math --debug
# Or run the full suite with pytest
pytest
```

### Architecture
#### Offline representation

* `Project`: calls the TAC_Parser to parse functions, blocks, and statements from Gigahorse
  * `Factory`: used to access several objects
  * `Function(s)`: contain blocks + an intra-procedural CFG
    * `Block(s)`: contain statements
      * `Statement(s)`: represent TAC operations. Every statement has a `.handle(state)` method that given a state applies such operations to derive its successors

#### Runtime representation

* `SimulationManager`: stores and manages states in "stashes"
  * `State(s)`: hold the transaction context at every step
    * `Storage`: symbolic modulo 2^256 store
    * `Memory`: symbolic modulo 2^256 store
    * `Registers`: symbolic modulo 2^256 store
