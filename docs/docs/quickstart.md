
# ⚡️ Quick Start 


## Installing from Source

???+ tip
       ⭐️ We strongly suggest using a python virtual environment rather than installing
       greed globally. Doing so reduces dependency conflicts and aids in
       reproducibility while debugging. Some popular tools that accomplish this
       include [virtualenv](https://virtualenv.pypa.io/en/latest/) and [virtualenvwrapper](https://virtualenvwrapper.readthedocs.io/en/latest/).


```bash
git clone git@github.com:ucsb-seclab/greed.git
mkvirtualenv greed
workon greed
./setup.sh
```


## Usage 
First, the contract needs to be pre-processed with gigahorse. This can be done in two ways:

```bash
# Create a new folder. The analyses will pollute the current working directory
mkdir /tmp/test_contract
cd /tmp/test_contract/

# OPTION 1: From the solidity source
cp <contract_source> contract.sol
analyze_source.sh contract.sol

# OPTION 2: From the contract bytecode
cp <contract_bytecode> contract.hex
analyze_hex.sh contract.hex
```

You can find the scripts `analyze_source.sh` and `analyze_hex.sh` in `/greed/resources`.

Then, to use `greed` in your python project:
```python
from greed import Project

p = Project(target_dir="/tmp/test_contract/")

entry_state = p.factory.entry_state(xid=0)
simgr = p.factory.simgr(entry_state=entry_state)
simgr.run()
```

Or to run greed from the command line:
```bash
greed /tmp/test_contract [--debug] [--find <address>]
```

## Reporting Bugs 🪳
Please report any bugs through the [Issue](https://github.com/ucsb-seclab/greed/issues) section on our GitHub! If you can provide a POC for your issue it would greatly speed up the resolution of your problem :)