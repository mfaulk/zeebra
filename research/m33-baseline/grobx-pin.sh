#!/usr/bin/env bash
# Build tools/external/grobx-driver against M33's current grobx pin, beside the repository's own
# pin (the M31 continuity row), and print the driver's SHA-256. The repository pin is not moved.
#
#   research/m33-baseline/grobx-pin.sh [REV] [LOCKFILE]
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
rev="${1:-8005a2a1670a7264617a6f49eeb2618d7fa21701}"   # grobx 0.155.1, 2026-11-20
lock="${2:-$here/grobx-0.155.1.Cargo.lock}"
old="$(sed -n 's/^const REVISION: &str = "\([0-9a-f]*\)";/\1/p' "$root/tools/external/grobx-driver/src/main.rs")"
target="/buildcache/cargo-target/zeebra-grobx-${rev:0:8}"
src="$target/src"
rm -rf "$src"
mkdir -p "$src" "$target/tmp"
cp -r "$root/tools/external/grobx-driver/." "$src/"
sed -i "s/$old/$rev/g" "$src/Cargo.toml" "$src/src/main.rs"
locked=()
if [[ -f "$lock" ]]; then cp "$lock" "$src/Cargo.lock"; locked=(--locked); fi
(cd "$src" && CARGO_TARGET_DIR="$target" TMPDIR="$target/tmp" RUSTC_WRAPPER='' \
  RUSTFLAGS='-C target-cpu=x86-64-v3' CARGO_PROFILE_RELEASE_LTO=fat \
  CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 cargo build --release "${locked[@]}" -j"${JOBS:-16}")
[[ -f "$lock" ]] || cp "$src/Cargo.lock" "$lock"
sha256sum "$target/release/grobx-driver"
