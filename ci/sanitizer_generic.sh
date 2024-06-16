#!/bin/bash

set -ex

export ASAN_OPTIONS="detect_odr_violation=0 detect_leaks=0"

# Run address sanitizer
RUSTFLAGS="-Z sanitizer=address" \
cargo test --tests --features memmap 

# Run leak sanitizer
RUSTFLAGS="-Z sanitizer=leak" \
cargo test --tests --features memmap

