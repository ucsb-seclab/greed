# SEtaac

A symbolic executor for the TAC IR used by Gigahorse

### Installation
```bash
# Create a virtual environment (e.g., using virtualenvwrapper)
mkvirtualenv SEtaac
# Activate the virtual environment
workon SEtaac
# Install SEtaac
pip install -e SEtaac
# Run the setup script 
SEtaac/setup.sh
```

### Usage
First, the contract needs to be pre-processed with `gigahorse`. This can be done in three ways:
```bash
# From the solidity source
mkdir /tmp/test_contract
cd /tmp/test_contract/
cp <contract_source> contract.sol
analyze_source.sh contract.sol

# From the deployment bytecode
cp <deployment_bytecode> contract.deployment.hex
analyze_deployment_hex.sh contract.deployment.hex

# From the contract bytecode
cp <contract_bytecode> contract.hex
analyze_contract_hex.sh contract.hex
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