#!/usr/bin/env bash
# Provisions the two SAT oracles for #220 (kissat, CryptoMiniSat) and the CMS XOR driver.
#
# External tools are oracles, not components: nothing here is linked into Zeebra, and both solvers
# are run as separate processes. CryptoMiniSat 5.18 needs GMP and, by default, fetches CaDiCaL and
# CadiBack over git at configure time; -DNOCADICAL=ON turns that off (only backbone simplification
# is lost, which an XOR-only system does not use). GMP is built here when the prefix lacks it, with
# the same pin and the same gnu17 workaround as provision.sh.
#
# Idempotent: each artefact is skipped when already installed.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PREFIX="${ZEEBRA_EXT_PREFIX:-$HOME/.local/opt/zeebra-ext}"
SRC="$PREFIX/src"
BUILD="$PREFIX/build"
JOBS="${ZEEBRA_EXT_JOBS:-24}"

# Every sha256 below was recorded from the file this script downloads, on 2026-11-18.
readonly KISSAT_COMMIT=8af8e56f174b778aef3aa45af9f739b2a5f492c2 # tag rel-4.0.4
readonly KISSAT_SHA256=c4ec54f5034ec096a2ce0dbb38ecd235e673c999d7073c771dcc21c4f32fc123
readonly CMS_COMMIT=97c6efeae45d93c45d2ebc3e4e83c2014c79513d # tag release/v5.18.0
readonly CMS_SHA256=29a30d796f61cda45037dfb91167c4c4008ad45c2c039931631a89dfe6b22110
readonly GMP_VERSION=6.3.0
readonly GMP_SHA256=a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898

log() { printf '[provision-sat] %s\n' "$*" >&2; }

check() {
  local got
  got="$(sha256sum "$1" | cut -d' ' -f1)"
  if [ "$got" != "$2" ]; then
    log "checksum mismatch for ${1##*/}: got $got, want $2"
    rm -f "$1"
    exit 1
  fi
}

# GitHub regenerates archive bytes rarely but not never; a mismatch here means re-pin, not bypass.
github_tarball() {
  local repo="$1" commit="$2" sum="$3" out="$SRC/${1##*/}-$2.tar.gz"
  if [ ! -f "$out" ]; then
    log "downloading $repo@$commit"
    gh api "repos/$repo/tarball/$commit" >"$out"
  fi
  check "$out" "$sum"
  printf '%s\n' "$out"
}

# Each archive is extracted into its own new, empty directory.
extract() {
  local archive="$1" dir="$2"
  rm -rf "$dir"
  mkdir -p "$dir"
  tar -xf "$archive" -C "$dir" --strip-components=1
}

mkdir -p "$SRC" "$BUILD" "$PREFIX/bin"

if [ ! -f "$PREFIX/lib/pkgconfig/gmp.pc" ]; then
  archive="$SRC/gmp-$GMP_VERSION.tar.xz"
  [ -f "$archive" ] || curl -fsSL --retry 3 -o "$archive" \
    "https://ftp.gnu.org/gnu/gmp/gmp-$GMP_VERSION.tar.xz"
  check "$archive" "$GMP_SHA256"
  extract "$archive" "$BUILD/gmp-src"
  mkdir -p "$BUILD/gmp"
  (cd "$BUILD/gmp" && "$BUILD/gmp-src/configure" CC="gcc -std=gnu17" --prefix="$PREFIX" \
    --enable-cxx >/dev/null && make -j"$JOBS" >/dev/null && make install >/dev/null)
  log "installed GMP $GMP_VERSION"
fi

if [ ! -x "$PREFIX/bin/kissat" ]; then
  extract "$(github_tarball arminbiere/kissat "$KISSAT_COMMIT" "$KISSAT_SHA256")" "$BUILD/kissat"
  (cd "$BUILD/kissat" && ./configure >/dev/null && make -j"$JOBS" >/dev/null)
  install -m 755 "$BUILD/kissat/build/kissat" "$PREFIX/bin/kissat"
  log "installed kissat $("$PREFIX/bin/kissat" --version)"
fi

if [ ! -f "$PREFIX/include/cryptominisat5/cryptominisat.h" ]; then
  extract "$(github_tarball msoos/cryptominisat "$CMS_COMMIT" "$CMS_SHA256")" "$BUILD/cms-src"
  mkdir -p "$BUILD/cms"
  PKG_CONFIG_PATH="$PREFIX/lib/pkgconfig" cmake -S "$BUILD/cms-src" -B "$BUILD/cms" \
    -DCMAKE_BUILD_TYPE=Release -DNOCADICAL=ON -DENABLE_PYTHON_INTERFACE=OFF \
    -DCMAKE_PREFIX_PATH="$PREFIX" -DCMAKE_INSTALL_PREFIX="$PREFIX" >/dev/null
  cmake --build "$BUILD/cms" -j"$JOBS" >/dev/null
  cmake --install "$BUILD/cms" >/dev/null
  log "installed CryptoMiniSat at $CMS_COMMIT"
fi

libdir="$PREFIX/lib64"
[ -d "$libdir" ] || libdir="$PREFIX/lib"
g++ -O2 -std=c++17 -Wall -Wextra -Werror \
  -I"$PREFIX/include" "$repo_root/tools/external/cms-xor-driver/cms_xor.cpp" \
  -L"$libdir" -Wl,-rpath,"$libdir" -Wl,-rpath,"$PREFIX/lib" -lcryptominisat5 \
  -o "$PREFIX/bin/cms-xor-driver"
"$PREFIX/bin/cms-xor-driver" --version
