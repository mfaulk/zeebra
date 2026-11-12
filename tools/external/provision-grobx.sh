#!/usr/bin/env bash
# Build the GPL driver as a separate executable with pinned source and lockfile.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
driver_target="${ZEEBRA_GROBX_TARGET:-/buildcache/cargo-target/zeebra-grobx}"
install_prefix="${ZEEBRA_EXT_PREFIX:-$HOME/.local/opt/zeebra-ext}"
mkdir -p "$driver_target/tmp" "$install_prefix/bin"
(
  cd "$repo_root/tools/external/grobx-driver"
  CARGO_TARGET_DIR="$driver_target" TMPDIR="$driver_target/tmp" RUSTC_WRAPPER='' \
    RUSTFLAGS='-C target-cpu=x86-64-v3' CARGO_PROFILE_RELEASE_LTO=fat \
    CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 cargo build --release --locked
)
ln -sf "$driver_target/release/grobx-driver" "$install_prefix/bin/grobx-driver"
"$install_prefix/bin/grobx-driver" --version
