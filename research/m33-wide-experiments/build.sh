#!/usr/bin/env bash
# Builds the timed study (`research-sigf4`) at each named commit from git archive, in parallel,
# each in its own target dir: the merge base and the candidate of a #971 paired A/B.
#   ZB_ALIGN_LOOPS=64 build.sh <commits>   # Gate C's placement control: every loop 64-byte aligned,
#                                          # in both arms, as `sig_f4_study-sig-align64-<commit>`
set -euo pipefail
repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
base=/buildcache/cargo-target/zeebra-971
export RUSTC_WRAPPER="" CARGO_INCREMENTAL=0 TMPDIR=$base/tmp
flavor=sig
if [[ -n "${ZB_ALIGN_LOOPS:-}" ]]; then
    # RUSTFLAGS replaces .cargo/config.toml's rustflags, so the ISA floor is repeated.
    export RUSTFLAGS="-C target-cpu=x86-64-v3 -C llvm-args=-align-loops=$ZB_ALIGN_LOOPS"
    flavor=sig-align$ZB_ALIGN_LOOPS
fi
mkdir -p "$base/bin" "$TMPDIR"
build() {
    local commit=$1 src=$base/src-$1
    mkdir -p "$src"
    git -C "$repo" archive "$commit" | tar -x -C "$src"
    (cd "$src" && CARGO_TARGET_DIR=$base/target-$flavor-$commit cargo build --release --locked -j12 \
        --features research-sigf4 --example sig_f4_study > "$base/build-$flavor-$commit.log" 2>&1)
    cp "$base/target-$flavor-$commit/release/examples/sig_f4_study" "$base/bin/sig_f4_study-$flavor-$commit"
}
for commit in "$@"; do
    build "$commit" &
done
wait
for commit in "$@"; do
    sha256sum "$base/bin/sig_f4_study-$flavor-$commit"
done
