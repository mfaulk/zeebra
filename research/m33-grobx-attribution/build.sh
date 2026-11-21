#!/usr/bin/env bash
# Builds the #970 arms from git archive of one commit, each in its own target dir, in parallel.
set -euo pipefail
commit=$1
repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
base=/buildcache/cargo-target/zeebra-970
src=$base/src-$commit
export RUSTC_WRAPPER="" CARGO_INCREMENTAL=0 TMPDIR=$base/tmp
mkdir -p "$src" "$base/bin" "$TMPDIR"
git -C "$repo" archive "$commit" | tar -x -C "$src"
cd "$src"
build() {
    local name=$1 features=$2
    CARGO_TARGET_DIR=$base/target-$name cargo build --release --locked -j12 \
        --features "$features" --example sig_f4_study > "$base/build-$name-$commit.log" 2>&1
    cp "$base/target-$name/release/examples/sig_f4_study" "$base/bin/sig_f4_study-$name-$commit"
}
build sig research-sigf4 &
build split research-sigf4-split &
build work research-sigf4,research-work &
wait
sha256sum "$base"/bin/sig_f4_study-*-"$commit"
