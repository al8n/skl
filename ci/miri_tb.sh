#!/bin/bash
set -e

rustup toolchain install nightly --component miri
rustup override set nightly
cargo miri setup

export MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-disable-isolation -Zmiri-symbolic-alignment-check -Zmiri-tree-borrows"

cargo miri test --all-features --target x86_64-unknown-linux-gnu
# cargo miri test --tests --target aarch64-unknown-linux-gnu #crossbeam_utils has problem on this platform
cargo miri test --all-features --target i686-unknown-linux-gnu
cargo miri test --all-features --target powerpc64-unknown-linux-gnu
