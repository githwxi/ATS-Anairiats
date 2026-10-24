#!/bin/sh

# Build the compiler and run the repository's supported example test suite.
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
cd "$REPO_ROOT"

if [ ! -x ./configure ]; then
  echo "configure is missing or not executable; run ./autogen.sh first." >&2
  exit 1
fi

./configure --prefix="$REPO_ROOT/_install"
make all
make test
