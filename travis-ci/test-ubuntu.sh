#!/bin/sh

# Build the compiler and run the repository's supported example test suite.
set -eu

SCRIPT_DIR=\
$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
MYREPO_ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
cd "$MYREPO_ROOT"

# ATS-generated C can contain labels that GCC reports as unused.
ATSCCOMP="$SCRIPT_DIR/gcc-no-unused-label.sh"
export ATSCCOMP

if [ ! -x ./configure ]; then
  echo "configure is missing or not executable; run ./autogen.sh first." >&2
  exit 1
fi

# configure was generated with AM_INIT_AUTOMAKE and checks for this helper.
# autogen.sh intentionally does not run automake --add-missing.
if [ ! -f ./compile ]; then
  if ! command -v automake >/dev/null 2>&1; then
    echo "automake is required to provide the compile helper." >&2
    exit 1
  fi
  cp "$(automake --print-libdir)/compile" ./compile
fi

./configure --prefix="$MYREPO_ROOT/_install"
mkdir -p bootstrap1
make all
make test
