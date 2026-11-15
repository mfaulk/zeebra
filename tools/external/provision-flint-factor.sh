#!/usr/bin/env bash
# Build the FLINT univariate-factoring driver (#784) against the prefix's pinned FLINT.
#
# FLINT itself is provisioned by provision.sh (msolve links it), so this only compiles the small C
# driver. -Wl,-rpath bakes the prefix in, so the driver can never pick up the system's older
# libflint.so.22 (pulled in by Singular).
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
install_prefix="${ZEEBRA_EXT_PREFIX:-$HOME/.local/opt/zeebra-ext}"
if [ ! -f "$install_prefix/include/flint/nmod_poly_factor.h" ]; then
  echo "provision-flint-factor: no FLINT headers under $install_prefix; run tools/external/provision.sh first" >&2
  exit 1
fi
cflags="-O2 -std=gnu17 -march=x86-64-v3"
mkdir -p "$install_prefix/bin"
# shellcheck disable=SC2086 # cflags is a deliberate word list
gcc $cflags -Wall -Wextra -Werror \
  -DDRIVER_CFLAGS="\"$cflags\"" \
  -I"$install_prefix/include" \
  "$repo_root/tools/external/flint-factor-driver/flint_factor.c" \
  -L"$install_prefix/lib" -Wl,-rpath,"$install_prefix/lib" -lflint -lgmp \
  -o "$install_prefix/bin/flint-factor-driver"
"$install_prefix/bin/flint-factor-driver" --version
