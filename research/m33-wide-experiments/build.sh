#!/usr/bin/env bash
# Builds the timed study (`research-sigf4`) at each named commit from git archive, in parallel,
# each in its own target dir: the merge base and the candidate of a #971 paired A/B.
set -euo pipefail
repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
base=/buildcache/cargo-target/zeebra-971
export RUSTC_WRAPPER="" CARGO_INCREMENTAL=0 TMPDIR=$base/tmp
mkdir -p "$base/bin" "$TMPDIR"
build() {
    local commit=$1 src=$base/src-$1
    mkdir -p "$src"
    git -C "$repo" archive "$commit" | tar -x -C "$src"
    (cd "$src" && CARGO_TARGET_DIR=$base/target-$commit cargo build --release --locked -j12 \
        --features research-sigf4 --example sig_f4_study > "$base/build-$commit.log" 2>&1)
    cp "$base/target-$commit/release/examples/sig_f4_study" "$base/bin/sig_f4_study-sig-$commit"
}
for commit in "$@"; do
    build "$commit" &
done
wait
for commit in "$@"; do
    sha256sum "$base/bin/sig_f4_study-sig-$commit"
done
