#!/bin/bash

INLINING_ROUNDS=6

while (( $# >= 1 )); do
    case $1 in
    --file) HEX_FILE=$2; shift; shift;;
    --inlining-rounds) INLINING_ROUNDS=$2; shift; shift;;
    *) break;
    esac;
done

if [[ -z $HEX_FILE ]]; then
  echo usage: analyze_contract_hex.sh --file \<contract .hex file\> [--inlining-rounds \<num inlining rounds\>]
  exit 1
elif [ ! -f $HEX_FILE ]; then
  echo $HEX_FILE is not a file
  exit 1
fi

FILEPATH=`readlink -f "${BASH_SOURCE[0]}"`
SETAAC_DIR=`dirname $FILEPATH`
SETAAC_DIR=`readlink -f $SETAAC_DIR/../`
GIGAHORSE_DIR=$SETAAC_DIR/gigahorse-toolchain

arch=$(uname -i)

if [ ! -f $GIGAHORSE_DIR/clients/main.dl_compiled ]; then
  echo "Can't find main.dl_compiled (something went wrong in setup.sh)"
  exit 1
elif [ ! -f $GIGAHORSE_DIR/clients/function_inliner.dl_compiled ]; then
  echo "Can't find function_inliner.dl_compiled (something went wrong in setup.sh)"
  exit 1
elif [ ! -f $GIGAHORSE_DIR/clients/guards.dl_compiled ]; then
  echo "Can't find guards.dl_compiled (something went wrong in setup.sh)"
  exit 1
fi

echo "Running main.dl"
$GIGAHORSE_DIR/generatefacts $HEX_FILE facts &&
LD_LIBRARY_PATH=$GIGAHORSE_DIR/souffle-addon/ $GIGAHORSE_DIR/clients/main.dl_compiled -F facts || { echo "${bold}${red}Failed to run main.dl_compiled${normal}"; exit 1; }

echo "Running $INLINING_ROUNDS of inlining (override with --rounds)"
for i in $(seq 1 $INLINING_ROUNDS); do
  echo "Running inlining round $i.."
  LD_LIBRARY_PATH=$GIGAHORSE_DIR/souffle-addon/ $GIGAHORSE_DIR/clients/function_inliner.dl_compiled || { echo "${bold}${red}Failed to run function_inliner.dl_compiled${normal}"; exit 1; }
done

echo "Running guards.dl"
LD_LIBRARY_PATH=$GIGAHORSE_DIR/souffle-addon/ $GIGAHORSE_DIR/clients/guards.dl_compiled -F facts || { echo "${bold}${red}Failed to run guards.dl_compiled${normal}"; exit 1; }

echo "Running visualizeout.py (to compute .tac output)"
$GIGAHORSE_DIR/clients/visualizeout.py || { echo "${bold}${red}Failed to run visualizeout.py${normal}"; exit 1; }

echo "Checking bad opcodes"
$GIGAHORSE_DIR/clients/check_bad_opcode.py || { echo "${bold}${red}Failed to run check_bad_opcode.py${normal}"; exit 1; }
