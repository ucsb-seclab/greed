#!/bin/bash

if [ ! $VIRTUAL_ENV ]; then
 echo "${bold}${red}Can't install outside of a Python virtualenv${normal}"; exit 1
fi

bold=$(tput bold)
normal=$(tput sgr0)
red=$(tput setaf 160)

j=1

while (( $# >= 1 )); do
    case $1 in
    -j) j=$2; shift; shift;;
    --no-gigahorse) NO_GIGAHORSE=TRUE; shift; shift;;
    *) break;
    esac;
done

# navigate to this script's directory
GREED_DIR=`dirname "${BASH_SOURCE[0]}"`
GREED_DIR=`readlink -f $GREED_DIR` || { echo "${bold}${red}Can't find greed absolute path ${normal}"; exit 1; }
GIGAHORSE_DIR=$GREED_DIR/gigahorse-toolchain
cd $GREED_DIR

########################################################################################################################
########################################################################################################################

# link our scripts into virtualenv's bin dir
echo "Linking scripts into virtualenv's bin directory.."
for script in $GREED_DIR/resources/{*.sh,*.py}; do
  ln -sf $script $VIRTUAL_ENV/bin/
done

# create alias for run.py
echo "Creating alias run.py -> greed.."
ln -sf $GREED_DIR/resources/run.py $VIRTUAL_ENV/bin/greed

# pip install greed
pip install -e .

########################################################################################################################
########################################################################################################################
# GIGAHORSE
########################################################################################################################

if [ -z $NO_GIGAHORSE ]; then
  echo "Number of parallel datalog jobs: $j (override with $0 -j N)"
  read -rsn1 -p "Setting up gigahorse.. Press any key to continue (ctrl-c to abort)"
  echo

  # clone the gigahorse-toolchain repo
  if [ ! -d $GREED_DIR/gigahorse-toolchain ]; then
    git clone --recursive https://github.com/nevillegrech/gigahorse-toolchain.git $GIGAHORSE_DIR
    cd $GIGAHORSE_DIR
    git checkout 59599ecb2397c42e342140189593cabdcce1a2d6
  fi

  # apply patches
  cd $GIGAHORSE_DIR
  for PATCH_FILE in $GREED_DIR/resources/patches/*.patch; do
    git apply --reverse --check $PATCH_FILE &>/dev/null || git apply $PATCH_FILE
  done
  cd $GREED_DIR

  # compile gigahorse clients
  command -v >&- souffle || { echo "${bold}${red}souffle is not installed. Please install it before proceeding (https://souffle-lang.github.io/build, version 2.0.2 preferred)${normal}"; echo "${bold}${red}Or maybe you forgot --no-gigahorse?${normal}"; exit 1; }
  dpkg -l | grep -q libboost-all-dev || { echo "${bold}${red}libboost-all-dev is not installed. Please install it before proceeding (e.g., sudo apt install libboost-all-dev)${normal}"; echo "${bold}${red}Or maybe you forgot --no-gigahorse?${normal}"; exit 1; }

  echo "Compiling gigahorse clients. This will take some time.."

  # compile souffle
  cd $GIGAHORSE_DIR/souffle-addon
  make || { echo "${bold}${red}Failed to build gigahorse's souffle-addon${normal}"; exit 1; }
  cd $GREED_DIR

  function compile () {
    echo "Compiling $1.."
    souffle --jobs $j -M "GIGAHORSE_DIR=$GIGAHORSE_DIR BULK_ANALYSIS=" -o $GIGAHORSE_DIR/clients/$1_compiled.tmp $GIGAHORSE_DIR/$2 -L $GIGAHORSE_DIR/souffle-addon || { echo "${bold}${red}Failed to build $1_compiled${normal}"; exit 1; } &&
    mv $GIGAHORSE_DIR/clients/$1_compiled.tmp $GIGAHORSE_DIR/clients/$1_compiled &&
    mv $GIGAHORSE_DIR/clients/$1_compiled.tmp.cpp $GIGAHORSE_DIR/clients/$1_compiled.cpp &&
    echo "Successfully compiled $1.."
  }
  compile "main.dl" "logic/main.dl"
  compile "function_inliner.dl" "clientlib/function_inliner.dl"
  compile "loops_semantics.dl" "clientlib/loops_semantics.dl"
  compile "guards.dl" "clientlib/guards.dl"

  command -v >&- mkisofs || echo "${bold}${red}mkisofs is not installed. solc-select might not work correctly (e.g., sudo apt install mkisofs)${normal}"
  solc-select versions | grep -q 0.8.7 || { echo "Installing solc 0.8.7"; solc-select install 0.8.7; }
else
  true
fi

########################################################################################################################
########################################################################################################################
# YICES
########################################################################################################################

# clone the yices2 repo
if [ ! -d $GREED_DIR/yices2 ]; then
  git clone https://github.com/SRI-CSL/yices2.git $GREED_DIR/yices2
fi

cd $GREED_DIR/yices2

# check if all required packages are installed (cmake, cython, libgmp-dev)
dpkg -l | grep -q gcc || { echo "${bold}${red}gcc is not installed. Please install it before proceeding (e.g., sudo apt install gcc)${normal}"; exit 1; }
dpkg -l | grep -q cmake || { echo "${bold}${red}cmake is not installed. Please install it before proceeding (e.g., sudo apt install cmake)${normal}"; exit 1; }
dpkg -l | grep -q gperf || { echo "${bold}${red}gperf is not installed. Please install it before proceeding (e.g., sudo apt install gperf)${normal}"; exit 1; }
dpkg -l | grep -q libgmp-dev || { echo "${bold}${red}libgmp-dev is not installed. Please install it before proceeding (e.g., sudo apt install libgmp-dev)${normal}"; exit 1; }

# install
autoconf || { echo "${bold}${red}Failed to run autoconf${normal}"; exit 1; }
./configure || { echo "${bold}${red}Failed to run ./configure${normal}"; exit 1; }
make || { echo "${bold}${red}Failed to run make${normal}"; exit 1; }

# finally, link yices2/build/lib/ to the virtualenv's site-packages dir
VIRTUAL_ENV_BIN=$VIRTUAL_ENV/bin
VIRTUAL_ENV_LIB=`echo $VIRTUAL_ENV/lib/python3.*/site-packages`
ln -sf $GREED_DIR/yices2/build/*-release/bin/* $VIRTUAL_ENV_BIN/
ln -sf $GREED_DIR/yices2/build/*-release/lib/* $VIRTUAL_ENV_LIB/
cp $VIRTUAL_ENV/lib/python3.*/site-packages/libyices.so.* $VIRTUAL_ENV_LIB/libyices.so

cd $GREED_DIR

# clone the yices2_python_bindings repo
if [ ! -d $GREED_DIR/yices2_python_bindings ]; then
  git clone https://github.com/ruaronicola/yices2_python_bindings.git $GREED_DIR/yices2_python_bindings
fi

pip install -e yices2_python_bindings
