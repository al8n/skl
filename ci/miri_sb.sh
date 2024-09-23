#!/bin/bash
set -e

# Check if TARGET and CONFIG_FLAGS are provided, otherwise panic
if [ -z "$1" ]; then
  echo "Error: TARGET is not provided"
  exit 1
fi

if [ -z "$2" ]; then
  echo "Error: CONFIG_FLAGS are not provided"
  exit 1
fi

TARGET=$1
CONFIG_FLAGS=$2

rustup toolchain install nightly --component miri
rustup override set nightly
cargo miri setup

export MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-disable-isolation -Zmiri-symbolic-alignment-check"
export RUSTFLAGS="--cfg test_$CONFIG_FLAGS"

cargo miri test --tests --target $TARGET --lib --features memmap
