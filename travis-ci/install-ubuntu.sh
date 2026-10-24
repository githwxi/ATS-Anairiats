#!/bin/sh

# Install the packages needed to build ATS/Anairiats and run its test suite
# on an Ubuntu Travis worker.
set -eu

if ! command -v apt-get >/dev/null 2>&1; then
  echo "This dependency installer requires Ubuntu (apt-get)." >&2
  exit 1
fi

if [ "$(id -u)" -eq 0 ]; then
  SUDO=
else
  SUDO=sudo
fi

$SUDO apt-get update
DEBIAN_FRONTEND=noninteractive $SUDO apt-get install -y \
  automake \
  byacc \
  build-essential \
  libgmp-dev
