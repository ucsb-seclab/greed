#!/bin/bash

# navigate to this script's directory
SETAAC_DIR=`dirname "${BASH_SOURCE[0]}"`
SETAAC_DIR=`readlink -f $SETAAC_DIR`

cd $SETAAC_DIR

# init the submodules (gigahorse-toolkit has submodules)
git submodule update --init --recursive

# link our clients into gigahorse-toolkit
for client in $SETAAC_DIR/gigahorse_clients/*; do
  ln -sf $client $SETAAC_DIR/gigahorse-toolchain/clients/
done

# link our scripts into virtualenv's bin dir
for script in $SETAAC_DIR/scripts/*; do
  ln -sf $script $VIRTUAL_ENV/bin/
done

# create alias for run.py
ln -sf $SETAAC_DIR/scripts/run.py $VIRTUAL_ENV/bin/SEtaac

# this is needed by solc-select
sudo apt install mkisofs
solc-select install 0.8.7

# we probably don't need to setup gigahorse-toolkit if we use the pre-compiled datalog
