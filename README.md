# SEtaac

A symbolic executor for the TAC IR used by Gigahorse

### Installation
```bash
# Clone this repo
git clone git@github.com:ucsb-seclab/SEtaac.git
# Create a virtual environment (e.g., using virtualenvwrapper)
mkvirtualenv SEtaac
# Activate the virtual environment
workon SEtaac
# Install SEtaac (will run setup.sh)
pip install -e SEtaac
```

### Usage
First, the contract needs to be pre-processed with `gigahorse`. This can be done in three ways:
```bash
# IMPORTANT: create a new folder 
# Analyses will pollute the current working directory
mkdir /tmp/test_contract
cd /tmp/test_contract/

# From the solidity source
cp <contract_source> contract.sol
analyze_source.sh contract.sol

# From the deployment bytecode
cp <deployment_bytecode> contract.deployment.hex
analyze_deployment_hex.sh contract.deployment.hex

# From the contract bytecode
cp <contract_bytecode> contract.hex
analyze_contract_hex.sh contract.hex

# To get the decompiled source
decompile.sh contract.hex

```

The source analysis only works on `x86_64` systems. The bytecode analyses work on both `aarch64` and `x86_64`. 

Finally, to run `SEtaac`:
```bash
SEtaac /tmp/test_contract --debug
```

### Testing
```bash
# Manually run a single test using run_testcase.py
cd SEtaac/tests
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
```