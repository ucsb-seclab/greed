#!/bin/bash

FILEPATH=`readlink -f "${BASH_SOURCE[0]}"`
SETAAC_DIR=`dirname $FILEPATH`
SETAAC_DIR=`readlink -f $SETAAC_DIR/../`
GIGAHORSE_DIR=$SETAAC_DIR/gigahorse-toolchain

arch=$(uname -i)

if [ ! -d $GIGAHORSE_DIR/clients/lib/$arch/ ]; then
  echo Analysis not supported on arch $arch
  exit 1
fi

# decompile
if [ -f $GIGAHORSE_DIR/clients/source_decompiler.$arch.dl_compiled ]; then
  LD_LIBRARY_PATH=$GIGAHORSE_DIR/clients/lib/$arch/ $GIGAHORSE_DIR/clients/source_decompiler.$arch.dl_compiled &&
  $GIGAHORSE_DIR/clients/get_source.py
else
  echo Decompilation not supported on arch $arch
  exit 1
fi
