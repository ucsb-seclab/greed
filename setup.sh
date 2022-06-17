#!/bin/bash

# navigate to this script's directory
SETAAC_DIR=`dirname "${BASH_SOURCE[0]}"`
SETAAC_DIR=`readlink -f $SETAAC_DIR`

cd $SETAAC_DIR

# init the submodules (gigahorse-toolkit has submodules)
git submodule update --init --recursive

# link our clients into gigahorse-toolkit
for c in $SETAAC_DIR/gigahorse_clients/*; do
  CLIENT_ABS_PATH=`readlink -f $c`
  ln -sf $CLIENT_ABS_PATH $SETAAC_DIR/gigahorse-toolchain/clients/
done

# we probably don't need to setup gigahorse-toolkit if we use the pre-compiled datalog
