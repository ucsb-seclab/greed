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

# clone the boolector repo
if [ ! -d $SETAAC_DIR/boolector ]; then
  git clone git@github.com:Boolector/boolector.git
fi

cd $SETAAC_DIR/boolector

# check if all required packages are installed (cmake, cython)
dpkg -l | grep -q cmake || { echo "${bold}${red}cmake is not installed. Please install it before proceeding (e.g., sudo apt install cmake)${normal}"; exit 1; }
dpkg -l | grep -q cython || { echo "${bold}${red}cython is not installed. Please install it before proceeding (e.g., sudo apt install cython)${normal}"; exit 1; }

# Download and build CaDiCaL
./contrib/setup-cadical.sh || { echo "${bold}${red}Failed to run setup-cadical.sh${normal}"; exit 1; }

# Download and build BTOR2Tools
./contrib/setup-btor2tools.sh || { echo "${bold}${red}Failed to run setup-btor2tools.sh${normal}"; exit 1; }

# Build Boolector with Python bindings
./configure.sh --python || { echo "${bold}${red}Failed to run configure.sh --python${normal}"; exit 1; }
cd build
make || { echo "${bold}${red}Failed to build boolector${normal}"; exit 1; }

# finally, link bitwuzla/build/lib/ to the virtualenv's site-packages dir
ln -sf $SETAAC_DIR/boolector/build/lib/* $VIRTUAL_ENV/lib/python3.8/site-packages/
