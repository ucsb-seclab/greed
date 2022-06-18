#!/bin/bash

if [[ $# = 0 ]]; then
  echo usage: $0 \<contract .hex file\>
  exit 1
elif [ -f $1 ]; then
  HEX_RAW_FILE=$1
else
  echo $1 is not a file
  exit 1
fi

SETAAC_DIR=`dirname "${BASH_SOURCE[0]}"`
SETAAC_DIR=`readlink -f $SETAAC_DIR/../`
GIGAHORSE_DIR=$SETAAC_DIR/gigahorse-toolchain

$SETAAC_DIR/scripts/extract_contract_code.py $HEX_RAW_FILE > contract.hex

# analyze hex
$SETAAC_DIR/scripts/analyze_hex.sh contract.hex
