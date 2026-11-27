#!/usr/bin/env bash
# Build the FLINT and NTL per-primitive univariate drivers (#1206).
#
# FLINT comes from $ZEEBRA_EXT_PREFIX when provision.sh has put its headers there (the Linux bench
# host), else from Homebrew (macOS). NTL comes from $NTL_PREFIX, else Homebrew, else /usr; set
# NTL_PREFIX=none to build the FLINT driver alone. -Wl,-rpath bakes each library's directory in,
# so a driver can never pick up another copy at run time.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
src="$repo_root/tools/external/univariate-primitives"
install_prefix="${ZEEBRA_EXT_PREFIX:-$HOME/.local/opt/zeebra-ext}"
brew_prefix="$(brew --prefix 2>/dev/null || true)"

if [ -f "$install_prefix/include/flint/nmod_poly.h" ]; then
  flint_prefix="$install_prefix"
elif [ -n "$brew_prefix" ] && [ -f "$brew_prefix/include/flint/nmod_poly.h" ]; then
  flint_prefix="$brew_prefix"
else
  echo "provision-univariate-primitives: no FLINT headers; run tools/external/provision.sh (Linux) or brew install flint (macOS)" >&2
  exit 1
fi

case "$(uname -m)" in
  x86_64) arch_flags="-march=x86-64-v3" ;;
  *) arch_flags="-mcpu=native" ;;
esac
mkdir -p "$install_prefix/bin"

cflags="-O2 -std=gnu17 $arch_flags"
# shellcheck disable=SC2086 # cflags is a deliberate word list
cc $cflags -Wall -Wextra -Werror -DDRIVER_CFLAGS="\"$cflags\"" \
  -I"$flint_prefix/include" "$src/flint_primitives.c" \
  -L"$flint_prefix/lib" -Wl,-rpath,"$flint_prefix/lib" -lflint -lgmp \
  -o "$install_prefix/bin/flint-primitives-driver"
"$install_prefix/bin/flint-primitives-driver" --version

ntl_prefix="${NTL_PREFIX:-}"
if [ -z "$ntl_prefix" ]; then
  if [ -n "$brew_prefix" ] && [ -f "$brew_prefix/include/NTL/ZZ_pX.h" ]; then
    ntl_prefix="$brew_prefix"
  elif [ -f /usr/include/NTL/ZZ_pX.h ]; then
    ntl_prefix=/usr
  else
    ntl_prefix=none
  fi
fi
if [ "$ntl_prefix" = none ]; then
  echo "provision-univariate-primitives: no NTL; built the FLINT driver only (NTL_DRIVER=none for the harness)" >&2
  exit 0
fi
cxxflags="-O2 -std=c++17 $arch_flags"
# NTL's headers are not -Wextra clean, so they are system headers here.
# shellcheck disable=SC2086 # cxxflags is a deliberate word list
c++ $cxxflags -Wall -Wextra -Werror -DDRIVER_CFLAGS="\"$cxxflags\"" \
  -isystem "$ntl_prefix/include" "$src/ntl_primitives.cpp" \
  -L"$ntl_prefix/lib" -Wl,-rpath,"$ntl_prefix/lib" -lntl -lgmp \
  -o "$install_prefix/bin/ntl-primitives-driver"
"$install_prefix/bin/ntl-primitives-driver" --version
