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

SETAAC_DIR=`dirname "${BASH_SOURCE[0]}"`
SETAAC_DIR=`readlink -f $SETAAC_DIR/../`
GIGAHORSE_DIR=$SETAAC_DIR/gigahorse-toolchain

$GIGAHORSE_DIR/generatefacts $HEX_FILE facts &&
($SETAAC_DIR/scripts/main.x86_64.dl_compiled -F facts || $SETAAC_DIR/scripts/main.aarch64.dl_compiled -F facts) &&
$GIGAHORSE_DIR/clients/visualizeout.py &&
$GIGAHORSE_DIR/clients/check_bad_opcode.py &&
$GIGAHORSE_DIR/clients/export_ir.py &&
$GIGAHORSE_DIR/clients/export_cfg.py
