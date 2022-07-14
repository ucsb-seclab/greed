#!/bin/bash

FILEPATH=`readlink -f "${BASH_SOURCE[0]}"`
SETAAC_DIR=`dirname $FILEPATH`
SETAAC_DIR=`readlink -f $SETAAC_DIR/../`
GIGAHORSE_DIR=$SETAAC_DIR/gigahorse-toolchain

LD_LIBRARY_PATH=$GIGAHORSE_DIR/souffle-addon/ $GIGAHORSE_DIR/clients/function_inliner.dl_compiled
