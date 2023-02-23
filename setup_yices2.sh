#!/bin/bash

if [ ! $VIRTUAL_ENV ]; then
 echo "${bold}${red}Can't install outside of a Python virtualenv${normal}"; exit 1
fi

bold=$(tput bold)
normal=$(tput sgr0)
red=$(tput setaf 160)

while (( $# >= 1 )); do
    case $1 in
    --path) GREED_DIR=$2; shift; shift;;
    *) break;
    esac;
done

# navigate to this script's directory
if [ -z $GREED_DIR ]; then
  GREED_DIR=`dirname "${BASH_SOURCE[0]}"`
  GREED_DIR=`readlink -f $GREED_DIR` || { echo "${bold}${red}Can't find greed absolute path (please specify it with --path PATH)${normal}"; exit 1; }
fi
GIGAHORSE_DIR=$GREED_DIR/gigahorse-toolchain

cd $GREED_DIR

# clone the yices2 repo
if [ ! -d $GREED_DIR/yices2 ]; then
  git clone git@github.com:SRI-CSL/yices2.git yices2
fi

cd $GREED_DIR/yices2

# check if all required packages are installed (cmake, cython, libgmp-dev)
dpkg -l | grep -q gcc || { echo "${bold}${red}gcc is not installed. Please install it before proceeding (e.g., sudo apt install gcc)${normal}"; exit 1; }
dpkg -l | grep -q cmake || { echo "${bold}${red}cmake is not installed. Please install it before proceeding (e.g., sudo apt install cmake)${normal}"; exit 1; }
dpkg -l | grep -q gperf || { echo "${bold}${red}gperf is not installed. Please install it before proceeding (e.g., sudo apt install gperf)${normal}"; exit 1; }
dpkg -l | grep -q libgmp-dev || { echo "${bold}${red}libgmp-dev is not installed. Please install it before proceeding (e.g., sudo apt install libgmp-dev)${normal}"; exit 1; }

autoconf || { echo "${bold}${red}Failed to run autoconf${normal}"; exit 1; }
./configure || { echo "${bold}${red}Failed to run ./configure${normal}"; exit 1; }
make || { echo "${bold}${red}Failed to run make${normal}"; exit 1; }

VIRTUAL_ENV_BIN=$VIRTUAL_ENV/bin
VIRTUAL_ENV_LIB=`echo $VIRTUAL_ENV/lib/python3.*/site-packages`

# finally, link bitwuzla/build/lib/ to the virtualenv's site-packages dir
ln -sf $GREED_DIR/yices2/build/*-release/bin/* $VIRTUAL_ENV_BIN/
ln -sf $GREED_DIR/yices2/build/*-release/lib/* $VIRTUAL_ENV_LIB/
cp $VIRTUAL_ENV/lib/python3.*/site-packages/libyices.so.* $VIRTUAL_ENV_LIB/libyices.so

# clone the yices2 repo
if [ ! -d $GREED_DIR/yices2_python_bindings ]; then
  git clone git@github.com:ruaronicola/yices2_python_bindings.git yices2_python_bindings
fi

pip install -e yices2_python_bindings
