#!/bin/bash

if [[ $# = 0 ]]; then
  echo usage: $0 \<contract .sol file\>
  exit 1
elif [ -f $1 ]; then
  SOURCE_FILE=$1
else
  echo $1 is not a file
  exit 1
fi

FILEPATH=`readlink -f "${BASH_SOURCE[0]}"`
GREED_DIR=`dirname $FILEPATH`
GREED_DIR=`readlink -f $GREED_DIR/../`
GIGAHORSE_DIR=$GREED_DIR/gigahorse-toolchain

arch=$(uname -i)

# compile with solc-select
SOLC_VERSION=0.8.7 solc --bin-runtime $SOURCE_FILE | sed -rn '/Binary of the runtime part:/{n;p;}' | tail -n 1 | tr -d '\n' > contract.hex || { echo "${bold}${red}Failed to run solc${normal}"; exit 1; }

# analyze deployment hex
$GREED_DIR/resources/analyze_hex.sh --file contract.hex
