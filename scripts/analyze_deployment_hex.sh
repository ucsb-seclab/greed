#!/bin/bash

if [[ $# = 0 ]]; then
  echo usage: $0 \<deployment .hex file\>
  exit 1
elif [ -f $1 ]; then
  $DEPLOYMENT_HEX_FILE=$1
else
  echo $1 is not a file
  exit 1
fi

FILEPATH=`readlink -f "${BASH_SOURCE[0]}"`
SETAAC_DIR=`dirname $FILEPATH`
SETAAC_DIR=`readlink -f $SETAAC_DIR/../`
GIGAHORSE_DIR=$SETAAC_DIR/gigahorse-toolchain

$SETAAC_DIR/scripts/deployment_to_contract_hex.py $DEPLOYMENT_HEX_FILE > contract.hex

# analyze hex
$SETAAC_DIR/scripts/analyze_contract_hex.sh contract.hex
