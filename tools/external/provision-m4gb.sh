#!/usr/bin/env bash
# Build the M4GB reference (#1030) at a pinned commit, one binary per (variables, prime).
#
#   tools/external/provision-m4gb.sh "8 10 12 14" "31 32003"
#
# M4GB is GPL-3.0-or-later and runs only as a subprocess (src/grobner/external/m4gb.rs,
# docs/research/external-provenance-policy.md). Upstream fixes MAXVARS and FIELDSIZE at compile
# time, so each pair is its own binary, installed as $PREFIX/bin/m4gb_n<N>_gf<P> with a .build
# sidecar naming the revision, compiler and flags. Upstream builds through autotools; neither
# host has them, and the only generated header (lib/config.h) defines nothing the sources read,
# so the solver is compiled directly. Idempotent: an existing binary with a matching sidecar is
# kept.
set -euo pipefail

readonly REVISION=01860a52dacb111d6e1533bc7547b2dc8f034073
readonly REPO=https://github.com/cr-marcstevens/m4gb
PREFIX="${ZEEBRA_EXT_PREFIX:-$HOME/.local/opt/zeebra-ext}"
SRC="$PREFIX/src/m4gb"
CXX="${CXX:-c++}"

if [ $# -ne 2 ]; then
  echo "usage: $0 \"<variable counts>\" \"<primes>\"" >&2
  exit 2
fi

# The same ISA floor as Zeebra's own x86_64 builds (.cargo/config.toml); elsewhere the compiler's
# default, as Zeebra has no target-cpu there either. Never -march=native: upstream's configure
# adds it, which would make the comparison depend on the build machine.
case "$(uname -m)" in
  x86_64) ISA_FLAGS="-march=x86-64-v3" ;;
  *) ISA_FLAGS="" ;;
esac
FLAGS="-std=c++11 -O3 -pthread $ISA_FLAGS"

mkdir -p "$PREFIX/bin" "$PREFIX/src"
if [ ! -d "$SRC/.git" ]; then
  git clone --quiet "$REPO" "$SRC"
fi
git -C "$SRC" fetch --quiet origin "$REVISION" 2>/dev/null || true
git -C "$SRC" checkout --quiet --detach "$REVISION"
if [ "$(git -C "$SRC" rev-parse HEAD)" != "$REVISION" ]; then
  echo "provision-m4gb: checkout is not $REVISION" >&2
  exit 1
fi
: > "$SRC/lib/config.h"
if [ -n "$(git -C "$SRC" status --porcelain --untracked-files=no)" ]; then
  echo "provision-m4gb: tracked upstream files are modified in $SRC" >&2
  exit 1
fi

compiler="$("$CXX" --version | head -n 1)"
for n in $1; do
  for p in $2; do
    out="$PREFIX/bin/m4gb_n${n}_gf${p}"
    sidecar="revision=$REVISION
cxx=$compiler
flags=$FLAGS -DMAXVARS=$n -DFIELDSIZE=$p
config=lib/config.h empty (autotools bypassed)"
    if [ -x "$out" ] && [ "$(cat "$out.build" 2>/dev/null)" = "$sidecar" ]; then
      echo "kept  $out"
      continue
    fi
    # shellcheck disable=SC2086 # FLAGS is a word list
    "$CXX" $FLAGS -w "-DMAXVARS=$n" "-DFIELDSIZE=$p" -o "$out" \
      "$SRC/src/m4gb.cpp" "$SRC/contrib/runtime_stats.cpp"
    printf '%s\n' "$sidecar" > "$out.build"
    echo "built $out"
  done
done
