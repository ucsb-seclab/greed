#!/bin/bash

if [ ! $VIRTUAL_ENV ]; then
 echo "${bold}${red}Can't install outside of a Python virtualenv${normal}"; exit 1
fi

bold=$(tput bold)
normal=$(tput sgr0)
red=$(tput setaf 160)

while (( $# >= 1 )); do
    case $1 in
    --path) SETAAC_DIR=$2; shift; shift;;
    *) break;
    esac;
done

# navigate to this script's directory
if [ -z $SETAAC_DIR ]; then
  SETAAC_DIR=`dirname "${BASH_SOURCE[0]}"`
  SETAAC_DIR=`readlink -f $SETAAC_DIR` || { echo "${bold}${red}Can't find SEtaac absolute path (please specify it with --path PATH)${normal}"; exit 1; }
fi
GIGAHORSE_DIR=$SETAAC_DIR/gigahorse-toolchain

cd $SETAAC_DIR

pip install z3-solver
