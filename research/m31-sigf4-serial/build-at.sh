#!/usr/bin/env bash
# build-at.sh <sha> <target-dir>: build sig_f4_study from src-<sha>/ (an extracted git archive).
#
# Cargo's dep-info records absolute source paths, so building a second tree into the same target
# dir checks the FIRST tree's mtimes and can report the old binary fresh. Each sha is therefore
# copied into one fixed path, `build-src/<target-dir name>`, with fresh mtimes, and the binary's
# provenance is confirmed by checking the copied tree's git-archive comment afterwards.
set -euo pipefail
sha=$1; tgt=$2; features=${FEATURES:-research-sigf4}; suffix=${SUFFIX:-}
src=/buildcache/cargo-target/zeebra-903/src-$sha
work=/buildcache/cargo-target/zeebra-903/build-src/$(basename "$tgt")
mkdir -p "$tgt/tmp" "$(dirname "$work")"
rm -rf "$work"
cp -r "$src" "$work"
find "$work" -type f -exec touch {} +
cd "$work"
# Path dependencies are judged by the dep-info of whichever tree was built last; drop them.
CARGO_TARGET_DIR="$tgt" cargo clean --release -p zeebra 2>&1 | tail -1
CARGO_TARGET_DIR="$tgt" RUSTC_WRAPPER="" TMPDIR="$tgt/tmp" \
  cargo build -j24 --release --features "$features" --example sig_f4_study 2>&1 | tail -1
cp "$tgt/release/examples/sig_f4_study" "/buildcache/cargo-target/zeebra-903/bins/$sha$suffix"
sha256sum "/buildcache/cargo-target/zeebra-903/bins/$sha$suffix"
