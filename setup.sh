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
    --path) SETAAC_DIR=$2; shift; shift;;
    --no-gigahorse) NO_GIGAHORSE=TRUE; shift; shift;;
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

# init the submodules (gigahorse-toolkit has submodules)
# echo "Initializing gigahorse submodule.."
git submodule update --init --recursive

# link our scripts into virtualenv's bin dir
echo "Linking scripts into virtualenv's bin directory.."
for script in $SETAAC_DIR/scripts/{*.sh,*.py}; do
  ln -sf $script $VIRTUAL_ENV/bin/
done

# create alias for run.py
echo "Creating alias run.py -> SEtaac.."
ln -sf $SETAAC_DIR/scripts/run.py $VIRTUAL_ENV/bin/SEtaac

if [ -z $NO_GIGAHORSE ]; then
  echo "Number of parallel datalog jobs: $j (override with $0 -j N)"
  read -rsn1 -p "Setting up gigahorse.. Press any key to continue (ctrl-c to abort)"
  echo

  # compile gigahorse clients
  command -v >&- souffle || { echo "${bold}${red}souffle is not installed. Please install it before proceeding (https://souffle-lang.github.io/build, version 2.0.2 preferred)${normal}"; echo "${bold}${red}Or maybe you forgot --no-gigahorse?${normal}"; exit 1; }
  dpkg -l | grep -q libboost-all-dev || { echo "${bold}${red}libboost-all-dev is not installed. Please install it before proceeding (e.g., sudo apt install libboost-all-dev)${normal}"; echo "${bold}${red}Or maybe you forgot --no-gigahorse?${normal}"; exit 1; }

  echo "Compiling gigahorse clients. This will take some time.."

  cd $GIGAHORSE_DIR/souffle-addon
  make &> /dev/null || { echo "${bold}${red}Failed to build gigahorse's souffle-addon${normal}"; exit 1; }
  cd $SETAAC_DIR

  # main
  echo "Compiling main.dl.."
  souffle --jobs $j -M "GIGAHORSE_DIR=$GIGAHORSE_DIR BULK_ANALYSIS=" -o $GIGAHORSE_DIR/clients/main.dl_compiled.tmp $GIGAHORSE_DIR/logic/main.dl -L $GIGAHORSE_DIR/souffle-addon || { echo "${bold}${red}Failed to build main.dl_compiled${normal}"; exit 1; } &&
  mv $GIGAHORSE_DIR/clients/main.dl_compiled.tmp $GIGAHORSE_DIR/clients/main.dl_compiled &&
  mv $GIGAHORSE_DIR/clients/main.dl_compiled.tmp.cpp $GIGAHORSE_DIR/clients/main.dl_compiled.cpp &&
  echo "Successfully compiled main.dl.."


  # function inliner
  echo "Compiling function_inliner.dl.."
  souffle --jobs $j -M "GIGAHORSE_DIR=$GIGAHORSE_DIR BULK_ANALYSIS=" -o $GIGAHORSE_DIR/clients/function_inliner.dl_compiled.tmp $GIGAHORSE_DIR/clientlib/function_inliner.dl -L $GIGAHORSE_DIR/souffle-addon || { echo "${bold}${red}Failed to build function_inliner.dl_compiled${normal}"; exit 1; } &&
  mv $GIGAHORSE_DIR/clients/function_inliner.dl_compiled.tmp $GIGAHORSE_DIR/clients/function_inliner.dl_compiled &&
  mv $GIGAHORSE_DIR/clients/function_inliner.dl_compiled.tmp.cpp $GIGAHORSE_DIR/clients/function_inliner.dl_compiled.cpp &&
  echo "Successfully compiled function_inliner.dl.."

  # guards analysis
  echo "Compiling guards.dl.."
  souffle --jobs $j -M "GIGAHORSE_DIR=$GIGAHORSE_DIR BULK_ANALYSIS=" -o $GIGAHORSE_DIR/clients/guards.dl_compiled.tmp $GIGAHORSE_DIR/clientlib/guards.dl -L $GIGAHORSE_DIR/souffle-addon || { echo "${bold}${red}Failed to build guards.dl_compiled${normal}"; exit 1; } &&
  mv $GIGAHORSE_DIR/clients/guards.dl_compiled.tmp $GIGAHORSE_DIR/clients/guards.dl_compiled &&
  mv $GIGAHORSE_DIR/clients/guards.dl_compiled.tmp.cpp $GIGAHORSE_DIR/clients/guards.dl_compiled.cpp &&
  echo "Successfully compiled guards.dl.."

  command -v >&- mkisofs || echo "${bold}${red}mkisofs is not installed. solc-select might not work correctly (e.g., sudo apt install mkisofs)${normal}"
  solc-select versions | grep -q 0.8.7 || { echo "Installing solc 0.8.7"; solc-select install 0.8.7; }
else
  true
fi

# link our clients into gigahorse-toolkit
echo "Linking clients into gigahorse-toolchain.."
for client in $SETAAC_DIR/gigahorse_clients/{*.dl_compiled,*.py,lib} $SETAAC_DIR/gigahorse_clients/lib; do
  ln -sf $client $SETAAC_DIR/gigahorse-toolchain/clients/
done