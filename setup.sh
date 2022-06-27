#!/bin/bash

bold=$(tput bold)
normal=$(tput sgr0)
red=$(tput setaf 160)

j=1

while (( $# >= 1 )); do
    case $1 in
    -j) j=$2; shift; shift;;
    *) break;
    esac;
done

# navigate to this script's directory
SETAAC_DIR=`dirname "${BASH_SOURCE[0]}"`
SETAAC_DIR=`readlink -f $SETAAC_DIR`
GIGAHORSE_DIR=$SETAAC_DIR/gigahorse-toolchain

arch=$(uname -i)

cd $SETAAC_DIR

# init the submodules (gigahorse-toolkit has submodules)
# echo "Initializing gigahorse submodule.."
git submodule update --init --recursive

# compile gigahorse clients
command -v >&- souffle || { echo "${bold}${red}souffle is not installed. Please install it before proceeding (https://souffle-lang.github.io/build, version 2.0.2 preferred)${normal}"; exit 1; }
dpkg -l | grep -q libboost-all-dev || echo "${bold}${red}libboost-all-dev is not installed. Please install it before proceeding (sudo apt install libboost-all-dev)${normal}"

echo "Compiling gigahorse clients. This will take some time.."
echo "Number of parallel datalog jobs: $j (override with $0 -j N)"

cd $GIGAHORSE_DIR/souffle-addon
make &> /dev/null || { echo "${bold}${red}Failed to build gigahorse's souffle-addon${normal}"; exit 1; }
cd $SETAAC_DIR
souffle --jobs 1 -M "GIGAHORSE_DIR=$GIGAHORSE_DIR BULK_ANALYSIS=" -o $GIGAHORSE_DIR/clients/main.dl_compiled.tmp $GIGAHORSE_DIR/logic/main.dl -L $GIGAHORSE_DIR/souffle-addon || { echo "${bold}${red}Failed to build main.dl_compiled${normal}"; exit 1; }
mv $GIGAHORSE_DIR/clients/main.dl_compiled.tmp $GIGAHORSE_DIR/clients/main.dl_compiled
mv $GIGAHORSE_DIR/clients/main.dl_compiled.tmp.cpp $GIGAHORSE_DIR/clients/main.dl_compiled.cpp

# link our clients into gigahorse-toolkit
echo "Linking clients into gigahorse-toolkit.."
for client in $SETAAC_DIR/gigahorse_clients/{*.dl_compiled,*.py,lib} $SETAAC_DIR/gigahorse_clients/lib; do
  ln -sf $client $SETAAC_DIR/gigahorse-toolchain/clients/
done

# link our scripts into virtualenv's bin dir
echo "Linking scripts into virtualenv's bin directory.."
for script in $SETAAC_DIR/scripts/{*.sh,*.py}; do
  ln -sf $script $VIRTUAL_ENV/bin/
done

# create alias for run.py
echo "Creating alias run.py -> SEtaac.."
ln -sf $SETAAC_DIR/scripts/run.py $VIRTUAL_ENV/bin/SEtaac

command -v >&- mkisofs || echo "${bold}${red}mkisofs is not installed. solc-select might not work correctly (sudo apt install mkisofs)${normal}"
solc-select versions | grep -q 0.8.7 || { echo "Installing solc 0.8.7"; solc-select install 0.8.7; }
