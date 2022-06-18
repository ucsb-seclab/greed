#!/bin/bash

if [[ $# = 0 ]]; then
  echo usage: $0 \<contract .hex file\>
  exit 1
elif [ -f $1 ]; then
  SOURCE_FILE=$1
else
  echo $1 is not a file
  exit 1
fi

SETAAC_DIR=`dirname "${BASH_SOURCE[0]}"`
SETAAC_DIR=`readlink -f $SETAAC_DIR/../`

# compile with solc-select
SOLC_VERSION=0.8.7 solc --bin source.sol | sed "1,/Binary:/d" > contract.hex.raw

$SETAAC_DIR/scripts/extract_contract_code.py contract.hex.raw > contract.hex

# analyze hex
$SETAAC_DIR/scripts/analyze_hex.sh contract.hex
