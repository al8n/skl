#!/bin/bash

set -ex

export ASAN_OPTIONS="detect_odr_violation=0 detect_leaks=0"

# Run address sanitizer
RUSTFLAGS="-Z sanitizer=address" \
cargo test --lib --all-features --target x86_64-unknown-linux-gnu

# Run leak sanitizer
RUSTFLAGS="-Z sanitizer=leak" \
cargo test --lib --all-features --target x86_64-unknown-linux-gnu

# Run memory sanitizer
RUSTFLAGS="-Zsanitizer=memory -Zsanitizer-memory-track-origins" \
RUSTDOCFLAGS="-Zsanitizer=memory -Zsanitizer-memory-track-origins" \
cargo test -Z build-std --all --release --target x86_64-unknown-linux-gnu --all-features

# Run thread sanitizer
RUSTFLAGS="-Z sanitizer=thread" \
cargo -Zbuild-std test --lib --all-features --target x86_64-unknown-linux-gnu


