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
SETAAC_DIR=`dirname $FILEPATH`
SETAAC_DIR=`readlink -f $SETAAC_DIR/../`

arch=$(uname -i)

if [ "$arch" != "x86_64" ]; then
  echo Source analysis not supported on arch $arch
  exit 1
fi

# compile with solc-select
SOLC_VERSION=0.8.7 solc --bin $SOURCE_FILE | sed "1,/Binary:/d" > contract.deployment.hex

# analyze deployment hex
$SETAAC_DIR/scripts/analyze_deployment_hex.sh contract.deployment.hex
