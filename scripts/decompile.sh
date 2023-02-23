#!/bin/bash

FILEPATH=`readlink -f "${BASH_SOURCE[0]}"`
GREED_DIR=`dirname $FILEPATH`
GREED_DIR=`readlink -f $GREED_DIR/../`
GIGAHORSE_DIR=$GREED_DIR/gigahorse-toolchain

arch=$(uname -i)

# decompile
if [ -f $GIGAHORSE_DIR/clients/source_decompiler.$arch.dl_compiled ]; then
  LD_LIBRARY_PATH=$GIGAHORSE_DIR/souffle-addon/ $GIGAHORSE_DIR/clients/source_decompiler.$arch.dl_compiled &&
  $GIGAHORSE_DIR/clients/get_source.py
else
  echo Decompilation not supported on arch $arch
  exit 1
fi