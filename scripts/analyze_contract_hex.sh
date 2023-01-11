#!/bin/bash

while (( $# >= 1 )); do
    case $1 in
    --file) HEX_FILE=$2; shift; shift;;
    *) break;
    esac;
done

if [[ -z $HEX_FILE ]]; then
  echo usage: analyze_contract_hex.sh --file \<contract .hex file\>
  exit 1
elif [ ! -f $HEX_FILE ]; then
  echo $HEX_FILE is not a file
  exit 1
fi

FILEPATH=`readlink -f "${BASH_SOURCE[0]}"`
SETAAC_DIR=`dirname $FILEPATH`
SETAAC_DIR=`readlink -f $SETAAC_DIR/../`
GIGAHORSE_DIR=$SETAAC_DIR/gigahorse-toolchain

if [ ! -f $GIGAHORSE_DIR/clients/main.dl_compiled ]; then
  echo "Can't find main.dl_compiled (something went wrong in setup.sh)"
  exit 1
elif [ ! -f $GIGAHORSE_DIR/clients/guards.dl_compiled ]; then
  echo "Can't find guards.dl_compiled (something went wrong in setup.sh)"
  exit 1
fi

echo "Running gigahorse.py"
/usr/bin/time -v $GIGAHORSE_DIR/gigahorse.py -q QUIET -T 3600 --reuse_datalog_bin --disable_inline -C $GIGAHORSE_DIR/clients/guards.dl_compiled,$GIGAHORSE_DIR/clients/visualizeout.py $HEX_FILE &> exec_info &&
curr_dir=$(pwd); cd $GIGAHORSE_DIR; gigahorse_version=$(git rev-parse HEAD); cd $curr_dir; printf "\tGigahorse version: $gigahorse_version\n" >> exec_info &&
curr_dir=$(pwd); cd $SETAAC_DIR; greed_version=$(git rev-parse HEAD); cd $curr_dir; printf "\tgreed version: $greed_version\n" >> exec_info &&
cp .temp/contract/out/* . &&
cp .temp/contract/contract.dasm .temp/contract/*.csv . &&
rm -rf .temp bytecode.hex
