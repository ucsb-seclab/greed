#!/bin/bash

# navigate to this script's directory
SETAAC_DIR=`dirname "${BASH_SOURCE[0]}"`
SETAAC_DIR=`readlink -f $SETAAC_DIR`

cd $SETAAC_DIR

# init the submodules (gigahorse-toolkit has submodules)
git submodule update --init --recursive

# link our clients into gigahorse-toolkit
for client in $SETAAC_DIR/gigahorse_clients/{*.dl_compiled,*.py,lib} $SETAAC_DIR/gigahorse_clients/lib; do
  ln -sf $client $SETAAC_DIR/gigahorse-toolchain/clients/
done

# link our scripts into virtualenv's bin dir
for script in $SETAAC_DIR/scripts/{*.sh,*.py}; do
  ln -sf $script $VIRTUAL_ENV/bin/
done

# create alias for run.py
ln -sf $SETAAC_DIR/scripts/run.py $VIRTUAL_ENV/bin/SEtaac

command -v >&- mkisofs || echo "mkisofs is not installed. solc-select might not work correctly (sudo apt install mkisofs)"
solc-select versions | grep -q 0.8.7 || solc-select install 0.8.7

# NOTE: no need to setup gigahorse-toolkit since we use the pre-compiled datalog
