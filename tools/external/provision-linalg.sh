#!/usr/bin/env bash
# Provision the linear-algebra comparands of #1209 and build their drivers.
#
#   tools/external/provision-linalg.sh [flint] [m4ri] [fflas] [spasm] [libs]
#
# With no arguments, every comparand; `libs` builds the libraries without the drivers. FLINT `nmod_mat`, M4RI, FFLAS-FFPACK (with Givaro) and SpaSM
# run as separate processes on exported matrices; nothing here is linked into Zeebra
# (docs/research/external-provenance-policy.md §7). Each driver is a small C or C++ program in
# tools/external/linalg-drivers/, installed as $PREFIX/bin/linalg-<name>, and prints the protocol
# that tools/external/linalg-comparands.py reads and `--version` (a contract line and the
# compiler flags).
#
# Where the dependencies come from:
#   GMP, FLINT  macOS: Homebrew (FLINT 3.6.0, the version provision.sh pins).
#               Linux: the prefix provision.sh installs; run it first.
#   BLAS        macOS: Homebrew OpenBLAS. Linux: an OpenBLAS pkg-config module, or
#               ZEEBRA_EXT_BLAS_LIBS (for instance "-L/opt/openblas/lib -lopenblas").
#   OpenMP      macOS: Homebrew libomp (Apple clang has no runtime). Linux: the compiler's.
#   argp        macOS: Homebrew argp-standalone (SpaSM's tools use it). Linux: glibc.
#   M4RI, Givaro, FFLAS-FFPACK, SpaSM: built here from a pinned tarball or commit.
#
# Sources and build trees go under ZEEBRA_EXT_SRC (default $PREFIX/src), which may be a scratch
# directory deleted afterwards; installed libraries, headers and drivers stay under the prefix.
# Idempotent: a step whose installed artefact is present is skipped.
set -euo pipefail

PREFIX="${ZEEBRA_EXT_PREFIX:-$HOME/.local/opt/zeebra-ext}"
SRC="${ZEEBRA_EXT_SRC:-$PREFIX/src}"
JOBS="${ZEEBRA_EXT_JOBS:-8}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
DRIVERS="$REPO_ROOT/tools/external/linalg-drivers"

# --- pinned versions (sha256 recorded from the downloaded files, 2026-11-28) ----------------
readonly M4RI_VERSION=20260122
readonly M4RI_SHA256=7e033ca1fd36be8861e2f67d9d124c398fc0d830209bb0226462485876346404
readonly GIVARO_VERSION=4.2.2
readonly GIVARO_SHA256=53e9fb290deb0e20799c62d250d65c2226013d60b4cebe6b0b54c73000cb8fff
readonly FFLAS_VERSION=2.5.0
readonly FFLAS_SHA256=dafb4c0835824d28e4f823748579be6e4c8889c9570c6ce9cce1e186c3ebbb23
readonly SPASM_COMMIT=09c40943f1d4b754f89fb97fc9ddf2b8e53e967e
readonly GH=https://github.com

# The ISA floor matches Zeebra's own builds (.cargo/config.toml sets x86-64-v3 on x86_64 and
# nothing elsewhere). Never -march=native: the comparison must not depend on the build machine.
case "$(uname -m)" in
  x86_64) ISA_FLAGS="-march=x86-64-v3" ;;
  *) ISA_FLAGS="" ;;
esac
OPT_FLAGS="-O3 $ISA_FLAGS"

log() { printf '[provision-linalg] %s\n' "$*"; }

sha256() {
  if command -v sha256sum > /dev/null 2>&1; then
    sha256sum "$1" | cut -d' ' -f1
  else
    shasum -a 256 "$1" | cut -d' ' -f1
  fi
}

# fetch <file> <sha256> <url>
fetch() {
  local out="$SRC/$1"
  if [ -f "$out" ] && [ "$(sha256 "$out")" = "$2" ]; then return 0; fi
  log "downloading $1"
  curl -fsSL --retry 3 --retry-delay 2 -o "$out" "$3"
  if [ "$(sha256 "$out")" != "$2" ]; then
    echo "provision-linalg: sha256 mismatch for $1" >&2
    rm -f "$out"
    exit 1
  fi
}

# --- platform -------------------------------------------------------------------------------
OS="$(uname -s)"
if [ "$OS" = Darwin ]; then
  BREW="$(brew --prefix)"
  DEP_PREFIX="$BREW"
  OMP_PREFIX="$BREW/opt/libomp"
  BLAS_PREFIX="$BREW/opt/openblas"
  BLAS_LIBS="${ZEEBRA_EXT_BLAS_LIBS:--L$BLAS_PREFIX/lib -lopenblas}"
  BLAS_CFLAGS="-I$BLAS_PREFIX/include"
  OMP_CFLAGS="-Xpreprocessor -fopenmp -I$OMP_PREFIX/include"
  OMP_LIBS="-L$OMP_PREFIX/lib -lomp"
  CC="${CC:-clang}"
  CXX="${CXX:-clang++}"
  export PKG_CONFIG_PATH="$PREFIX/lib/pkgconfig:$BLAS_PREFIX/lib/pkgconfig${PKG_CONFIG_PATH:+:$PKG_CONFIG_PATH}"
  RPATHS="-Wl,-rpath,$PREFIX/lib -Wl,-rpath,$BREW/lib -Wl,-rpath,$BLAS_PREFIX/lib -Wl,-rpath,$OMP_PREFIX/lib"
else
  DEP_PREFIX="$PREFIX"
  export PKG_CONFIG_PATH="$PREFIX/lib/pkgconfig${PKG_CONFIG_PATH:+:$PKG_CONFIG_PATH}"
  if [ -n "${ZEEBRA_EXT_BLAS_LIBS:-}" ]; then
    BLAS_LIBS="$ZEEBRA_EXT_BLAS_LIBS"
    BLAS_CFLAGS="${ZEEBRA_EXT_BLAS_CFLAGS:-}"
  elif pkg-config --exists openblas; then
    BLAS_LIBS="$(pkg-config --libs openblas)"
    BLAS_CFLAGS="$(pkg-config --cflags openblas)"
  else
    echo "provision-linalg: no OpenBLAS found; set ZEEBRA_EXT_BLAS_LIBS" >&2
    exit 1
  fi
  OMP_CFLAGS="-fopenmp"
  OMP_LIBS="-fopenmp"
  CC="${CC:-gcc}"
  CXX="${CXX:-g++}"
  RPATHS="-Wl,-rpath,$PREFIX/lib"
fi

mkdir -p "$PREFIX/bin" "$PREFIX/lib" "$SRC"

# --- M4RI -----------------------------------------------------------------------------------
# Built without OpenMP: upstream's own default, and the one-thread arm is what #1209 asks of it.
provision_m4ri_lib() {
  if [ -f "$PREFIX/include/m4ri/m4ri.h" ]; then log "M4RI $M4RI_VERSION present"; return 0; fi
  fetch "m4ri-$M4RI_VERSION.tar.gz" "$M4RI_SHA256" \
    "$GH/malb/m4ri/releases/download/$M4RI_VERSION/m4ri-$M4RI_VERSION.tar.gz"
  tar xzf "$SRC/m4ri-$M4RI_VERSION.tar.gz" -C "$SRC"
  log "building M4RI $M4RI_VERSION"
  (
    cd "$SRC/m4ri-$M4RI_VERSION"
    CC="$CC" CFLAGS="$OPT_FLAGS" ./configure --prefix="$PREFIX" --disable-openmp --disable-png \
      --disable-static
    make "-j$JOBS"
    make install
  ) > "$SRC/m4ri.log" 2>&1
}

# --- Givaro and FFLAS-FFPACK ----------------------------------------------------------------
provision_givaro() {
  if [ -f "$PREFIX/lib/pkgconfig/givaro.pc" ]; then log "Givaro $GIVARO_VERSION present"; return 0; fi
  fetch "givaro-$GIVARO_VERSION.tar.gz" "$GIVARO_SHA256" \
    "$GH/linbox-team/givaro/releases/download/v$GIVARO_VERSION/givaro-$GIVARO_VERSION.tar.gz"
  tar xzf "$SRC/givaro-$GIVARO_VERSION.tar.gz" -C "$SRC"
  log "building Givaro $GIVARO_VERSION"
  (
    cd "$SRC/givaro-$GIVARO_VERSION"
    CC="$CC" CXX="$CXX" CXXFLAGS="$OPT_FLAGS" CFLAGS="$OPT_FLAGS" \
      ./configure --prefix="$PREFIX" --with-gmp="$DEP_PREFIX" --disable-static
    make "-j$JOBS"
    make install
  ) > "$SRC/givaro.log" 2>&1
}

provision_fflas() {
  if [ -f "$PREFIX/lib/pkgconfig/fflas-ffpack.pc" ]; then log "FFLAS-FFPACK $FFLAS_VERSION present"; return 0; fi
  fetch "fflas-ffpack-$FFLAS_VERSION.tar.gz" "$FFLAS_SHA256" \
    "$GH/linbox-team/fflas-ffpack/releases/download/v$FFLAS_VERSION/fflas-ffpack-$FFLAS_VERSION.tar.gz"
  tar xzf "$SRC/fflas-ffpack-$FFLAS_VERSION.tar.gz" -C "$SRC"
  log "building FFLAS-FFPACK $FFLAS_VERSION (header-only templates plus a small library)"
  (
    cd "$SRC/fflas-ffpack-$FFLAS_VERSION"
    CC="$CC" CXX="$CXX" CXXFLAGS="$OPT_FLAGS $OMP_CFLAGS" LDFLAGS="$OMP_LIBS" \
      ./configure --prefix="$PREFIX" --without-archnative --enable-openmp \
      --with-blas-libs="$BLAS_LIBS" --with-blas-cflags="$BLAS_CFLAGS" --disable-static
    make "-j$JOBS"
    make install
  ) > "$SRC/fflas.log" 2>&1
}

# --- SpaSM ----------------------------------------------------------------------------------
provision_spasm_lib() {
  if [ -f "$PREFIX/include/spasm.h" ]; then log "SpaSM @ ${SPASM_COMMIT:0:8} present"; return 0; fi
  local repo="$SRC/spasm"
  if [ ! -d "$repo/.git" ]; then git clone --quiet "$GH/cbouilla/spasm.git" "$repo"; fi
  git -C "$repo" checkout --quiet --detach "$SPASM_COMMIT"
  log "building SpaSM @ ${SPASM_COMMIT:0:8}"
  local cmake_extra=() cmake_flags="$ISA_FLAGS"
  if [ "$OS" = Darwin ]; then
    # FFLAS-FFPACK's headers include <omp.h>, which SpaSM's C++ file does not get through the
    # OpenMP_C target it links.
    cmake_flags="$ISA_FLAGS -I$OMP_PREFIX/include"
    cmake_extra=(
      "-DOpenMP_C_FLAGS=$OMP_CFLAGS" "-DOpenMP_C_LIB_NAMES=omp"
      "-DOpenMP_CXX_FLAGS=$OMP_CFLAGS" "-DOpenMP_CXX_LIB_NAMES=omp"
      "-DOpenMP_omp_LIBRARY=$OMP_PREFIX/lib/libomp.dylib"
      "-DCMAKE_PREFIX_PATH=$BREW;$BREW/opt/argp-standalone"
    )
  fi
  (
    rm -rf "$repo/build"
    cmake -S "$repo" -B "$repo/build" -DCMAKE_C_COMPILER="$CC" -DCMAKE_CXX_COMPILER="$CXX" \
      -DBUILD_TESTING=OFF -DCMAKE_C_FLAGS="$cmake_flags" -DCMAKE_CXX_FLAGS="$cmake_flags" \
      "${cmake_extra[@]}"
    cmake --build "$repo/build" --target spasm "-j$JOBS"
    # Upstream has no install rule; the library and its one header are all a driver needs.
    cp "$repo/build/src/"libspasm.* "$PREFIX/lib/"
    cp "$repo/src/spasm.h" "$PREFIX/include/spasm.h"
  ) > "$SRC/spasm.log" 2>&1
  if [ "$OS" = Darwin ]; then
    install_name_tool -id "$PREFIX/lib/libspasm.dylib" "$PREFIX/lib/libspasm.dylib"
  fi
}

# --- drivers --------------------------------------------------------------------------------
# build_driver <name> <compiler> <source> <flags and libraries...>
build_driver() {
  local name="$1" compiler="$2" source="$3"
  shift 3
  local flags="$OPT_FLAGS"
  log "building linalg-$name"
  # shellcheck disable=SC2086 # the flag strings are deliberate word lists
  "$compiler" $flags -Wall -Wextra -DDRIVER_CFLAGS="\"$flags\"" -I"$DRIVERS" -isystem "$PREFIX/include" \
    -isystem "$DEP_PREFIX/include" "$DRIVERS/$source" -L"$PREFIX/lib" -L"$DEP_PREFIX/lib" "$@" $RPATHS \
    -o "$PREFIX/bin/linalg-$name"
  "$PREFIX/bin/linalg-$name" --version
}

provision_flint() {
  if [ ! -f "$DEP_PREFIX/include/flint/nmod_mat.h" ]; then
    echo "provision-linalg: no FLINT under $DEP_PREFIX (run tools/external/provision.sh on Linux)" >&2
    exit 1
  fi
  build_driver flint "$CC" flint_linalg.c -lflint -lgmp -lm
}

provision_m4ri() {
  provision_m4ri_lib
  build_driver m4ri "$CC" m4ri_linalg.c -DM4RI_VERSION_STRING="\"$M4RI_VERSION\"" -Wno-unused-parameter -lm4ri -lm
}

provision_fflas_driver() {
  provision_givaro
  provision_fflas
  # shellcheck disable=SC2046,SC2086 # pkg-config output is a word list
  build_driver fflas "$CXX" fflas_linalg.cpp -std=c++17 $OMP_CFLAGS \
    $(pkg-config --cflags fflas-ffpack) $(pkg-config --libs fflas-ffpack) $BLAS_LIBS $OMP_LIBS
}

provision_spasm() {
  provision_givaro
  provision_fflas
  provision_spasm_lib
  # shellcheck disable=SC2086
  build_driver spasm "$CC" spasm_linalg.c -std=gnu11 $OMP_CFLAGS -lspasm $OMP_LIBS -lm
}

steps=("$@")
if [ "${#steps[@]}" -eq 0 ]; then steps=(flint m4ri fflas spasm); fi
for step in "${steps[@]}"; do
  case "$step" in
    flint) provision_flint ;;
    m4ri) provision_m4ri ;;
    fflas) provision_fflas_driver ;;
    spasm) provision_spasm ;;
    libs) provision_m4ri_lib; provision_givaro; provision_fflas; provision_spasm_lib ;;
    *)
      echo "provision-linalg: unknown comparand $step" >&2
      exit 64
      ;;
  esac
done
log "drivers are in $PREFIX/bin (linalg-*)"
