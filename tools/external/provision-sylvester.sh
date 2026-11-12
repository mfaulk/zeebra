#!/usr/bin/env bash
# Build the pinned F4/certificate driver outside the root dependency graph.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
driver_target="${ZEEBRA_SYLVESTER_TARGET:-/buildcache/cargo-target/zeebra-sylvester}"
install_prefix="${ZEEBRA_EXT_PREFIX:-$HOME/.local/opt/zeebra-ext}"
mkdir -p "$driver_target/tmp" "$install_prefix/bin"
(
  cd "$repo_root/tools/external/sylvester-driver"
  CARGO_TARGET_DIR="$driver_target" TMPDIR="$driver_target/tmp" RUSTC_WRAPPER='' \
    RUSTFLAGS='-C target-cpu=x86-64-v3' CARGO_PROFILE_RELEASE_LTO=fat \
    CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 cargo build --release --locked
)
ln -sf "$driver_target/release/sylvester-driver" "$install_prefix/bin/sylvester-driver"
"$install_prefix/bin/sylvester-driver" --version
