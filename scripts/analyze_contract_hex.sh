#!/bin/bash

if [[ $# = 0 ]]; then
  echo usage: $0 \<contract .hex file\>
  exit 1
elif [ -f $1 ]; then
  HEX_FILE=$1
else
  echo $1 is not a file
  exit 1
fi

FILEPATH=`readlink -f "${BASH_SOURCE[0]}"`
SETAAC_DIR=`dirname $FILEPATH`
SETAAC_DIR=`readlink -f $SETAAC_DIR/../`
GIGAHORSE_DIR=$SETAAC_DIR/gigahorse-toolchain

arch=$(uname -i)

$GIGAHORSE_DIR/generatefacts $HEX_FILE facts &&
LD_LIBRARY_PATH=$GIGAHORSE_DIR/clients/lib/$arch/ $GIGAHORSE_DIR/clients/main.$arch.dl_compiled -F facts &&
$GIGAHORSE_DIR/clients/visualizeout.py &&
$GIGAHORSE_DIR/clients/check_bad_opcode.py &&
$GIGAHORSE_DIR/clients/export_ir.py &&
$GIGAHORSE_DIR/clients/export_cfg.py

# decompile
LD_LIBRARY_PATH=$GIGAHORSE_DIR/clients/lib/$arch/ $GIGAHORSE_DIR/clients/source_decompiler.$arch.dl_compiled -F facts &&
$GIGAHORSE_DIR/clients/get_source.py
