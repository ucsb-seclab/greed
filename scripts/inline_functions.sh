#!/bin/bash

ROUNDS=1

while (( $# >= 1 )); do
    case $1 in
    --rounds) ROUNDS=$2; shift; shift;;
    *) break;
    esac;
done

FILEPATH=`readlink -f "${BASH_SOURCE[0]}"`
SETAAC_DIR=`dirname $FILEPATH`
SETAAC_DIR=`readlink -f $SETAAC_DIR/../`
GIGAHORSE_DIR=$SETAAC_DIR/gigahorse-toolchain

echo "Running $ROUNDS of inlining (override with --rounds)"

for i in $(seq 1 $ROUNDS); do
  echo "Running inlining round $i.."
  LD_LIBRARY_PATH=$GIGAHORSE_DIR/souffle-addon/ $GIGAHORSE_DIR/clients/function_inliner.dl_compiled
done

echo "Running visualizeout.py (to re-compute .tac output)"
$GIGAHORSE_DIR/clients/visualizeout.py
