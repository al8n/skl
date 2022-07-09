#!/bin/bash
set -e

rustup toolchain install nightly --component miri
rustup override set nightly
cargo miri setup

export MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-disable-isolation"

cargo miri test --no-default-features --features core --target x86_64-unknown-linux-gnu
cargo miri test --no-default-features --features core --target aarch64-unknown-linux-gnu
cargo miri test --no-default-features --features core --target i686-unknown-linux-gnu
cargo miri test --no-default-features --features core --target powerpc64-unknown-linux-gnu