#!/usr/bin/env bash
# Provisions the external computer-algebra comparands for M25 into a user prefix.
#
# No root is needed: every dependency is built from a pinned source tarball or a pinned git
# commit and installed under ${ZEEBRA_EXT_PREFIX}. Nothing here is linked into Zeebra — the
# comparands are run as separate processes (docs/research/external-provenance-policy.md §7),
# which is what makes the GPL ones (msolve, Groebner.jl, Singular) usable at all.
#
# Idempotent: each step checks for its own installed artefact and skips if present.
# Re-running after a partial failure resumes from the first missing artefact.

set -euo pipefail

PREFIX="${ZEEBRA_EXT_PREFIX:-$HOME/.local/opt/zeebra-ext}"
SRC="$PREFIX/src"
BUILD="$PREFIX/build"
JOBS="${ZEEBRA_EXT_JOBS:-32}"

# --- pinned versions -------------------------------------------------------------------------
# Every sha256 below was recorded from the file this script downloads, on 2026-11-06.
readonly GMP_VERSION=6.3.0
readonly GMP_SHA256=a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898
readonly MPFR_VERSION=4.2.2
readonly MPFR_SHA256=b67ba0383ef7e8a8563734e2e889ef5ec3c3b898a01d00fa0a6869ad81c6ce01
readonly FLINT_VERSION=3.6.0
readonly FLINT_SHA256=b95e2c7792f5eea4a1c8d2d42c4098434756832e57a094b295eb5dfdc9b4c36b
readonly MSOLVE_VERSION=0.11.0
readonly MSOLVE_SHA256=0f32011c4333efb662ce8f5febf6b5dc1a8e6f1e4a935361b9af5009bd5cdb98
readonly JULIA_VERSION=1.11.7
readonly JULIA_SHA256=aa5924114ecb89fd341e59aa898cd1882b3cb622ca4972582c1518eff5f68c05
readonly GROEBNER_JL_VERSION=0.10.11
readonly ABSTRACTALGEBRA_JL_VERSION=0.50.5
readonly SAGEBRUSH_COMMIT=86d9f1c787030752dcaab1ddb8d99cf1b7fa5e1b

# GMP 6.3.0 and MPFR 4.2.2 predate C23 and their configure probes call a declared-`()` function
# with arguments, which GCC 15+ rejects outright rather than warning about ("too many arguments
# to function 'g'; expected 0, have 6"). Without this GMP's configure ends in "could not find a
# working compiler". msolve's own sources build clean under C23 but are kept on the same
# standard as the libraries they link.
readonly C_STD="-std=gnu17"

INSTALLED=()
SKIPPED=()

log()  { printf '[provision] %s\n' "$*"; }
note() { INSTALLED+=("$1"); }
skip() { SKIPPED+=("$1"); }

# fetch <url> <filename> <sha256>
fetch() {
  local url="$1" out="$SRC/$2" want="$3" got
  if [ -f "$out" ]; then
    got="$(sha256sum "$out" | cut -d' ' -f1)"
    if [ "$got" = "$want" ]; then
      return 0
    fi
    log "checksum mismatch for $2, re-downloading"
    rm -f "$out"
  fi
  log "downloading $2"
  curl -fsSL -o "$out" "$url"
  got="$(sha256sum "$out" | cut -d' ' -f1)"
  if [ "$got" != "$want" ]; then
    echo "provision: sha256 mismatch for $2" >&2
    echo "  expected $want" >&2
    echo "  got      $got" >&2
    exit 1
  fi
}

mkdir -p "$PREFIX/bin" "$SRC" "$BUILD"

# --- GMP -------------------------------------------------------------------------------------
provision_gmp() {
  if [ -f "$PREFIX/include/gmp.h" ]; then skip "GMP $GMP_VERSION"; return 0; fi
  fetch "https://gmplib.org/download/gmp/gmp-$GMP_VERSION.tar.xz" \
        "gmp-$GMP_VERSION.tar.xz" "$GMP_SHA256"
  tar xf "$SRC/gmp-$GMP_VERSION.tar.xz" -C "$SRC"
  rm -rf "$BUILD/gmp"; mkdir -p "$BUILD/gmp"
  log "building GMP $GMP_VERSION"
  (
    cd "$BUILD/gmp"
    CC="gcc $C_STD" "$SRC/gmp-$GMP_VERSION/configure" --prefix="$PREFIX" --enable-cxx
    make "-j$JOBS"
    make install
  ) > "$BUILD/gmp.log" 2>&1
  note "GMP $GMP_VERSION"
}

# --- MPFR ------------------------------------------------------------------------------------
# FLINT needs MPFR as well as GMP; a modern FLINT does not bundle it, so it is built here.
provision_mpfr() {
  if [ -f "$PREFIX/include/mpfr.h" ]; then skip "MPFR $MPFR_VERSION"; return 0; fi
  fetch "https://www.mpfr.org/mpfr-$MPFR_VERSION/mpfr-$MPFR_VERSION.tar.xz" \
        "mpfr-$MPFR_VERSION.tar.xz" "$MPFR_SHA256"
  tar xf "$SRC/mpfr-$MPFR_VERSION.tar.xz" -C "$SRC"
  rm -rf "$BUILD/mpfr"; mkdir -p "$BUILD/mpfr"
  log "building MPFR $MPFR_VERSION"
  (
    cd "$BUILD/mpfr"
    CC="gcc $C_STD" "$SRC/mpfr-$MPFR_VERSION/configure" --prefix="$PREFIX" --with-gmp="$PREFIX"
    make "-j$JOBS"
    make install
  ) > "$BUILD/mpfr.log" 2>&1
  note "MPFR $MPFR_VERSION"
}

# --- FLINT -----------------------------------------------------------------------------------
# The release tarball ships a generated `configure`, so no autotools are needed. This matters:
# this machine has no autoconf/automake/libtool and no root, and automake 1.17/1.18 cannot even
# run under Perl 5.42 (core `threads` was removed), so a git checkout would be a dead end.
provision_flint() {
  if [ -f "$PREFIX/include/flint/nmod.h" ]; then skip "FLINT $FLINT_VERSION"; return 0; fi
  fetch "https://github.com/flintlib/flint/releases/download/v$FLINT_VERSION/flint-$FLINT_VERSION.tar.gz" \
        "flint-$FLINT_VERSION.tar.gz" "$FLINT_SHA256"
  tar xzf "$SRC/flint-$FLINT_VERSION.tar.gz" -C "$SRC"
  log "building FLINT $FLINT_VERSION (slow: several minutes)"
  (
    cd "$SRC/flint-$FLINT_VERSION"
    ./configure --prefix="$PREFIX" --with-gmp="$PREFIX" --with-mpfr="$PREFIX" --disable-static
    make "-j$JOBS"
    make install
  ) > "$BUILD/flint.log" 2>&1
  note "FLINT $FLINT_VERSION"
}

# --- msolve ----------------------------------------------------------------------------------
# The msolve.lip6.fr tarball is the *preconfigured* distribution (INSTALL, "If you are working
# on a distribution"); the GitHub release and a git checkout both require `./autogen.sh` and so
# autotools. Its configure.ac declares the same version 0.11.0 as git master at b364edcb.
# -Wl,-rpath bakes the prefix into the binary, so msolve runs with no LD_LIBRARY_PATH.
provision_msolve() {
  if [ -x "$PREFIX/bin/msolve" ]; then skip "msolve $MSOLVE_VERSION"; return 0; fi
  fetch "https://msolve.lip6.fr/downloads/v$MSOLVE_VERSION/msolve-$MSOLVE_VERSION.tar.gz" \
        "msolve-$MSOLVE_VERSION.tar.gz" "$MSOLVE_SHA256"
  tar xzf "$SRC/msolve-$MSOLVE_VERSION.tar.gz" -C "$SRC"
  log "building msolve $MSOLVE_VERSION"
  (
    cd "$SRC/msolve-$MSOLVE_VERSION"
    CC="gcc $C_STD" ./configure --prefix="$PREFIX" \
      CPPFLAGS="-I$PREFIX/include" \
      LDFLAGS="-L$PREFIX/lib -Wl,-rpath,$PREFIX/lib"
    make "-j$JOBS"
    make install
  ) > "$BUILD/msolve.log" 2>&1
  note "msolve $MSOLVE_VERSION"
}

# --- Julia + Groebner.jl ---------------------------------------------------------------------
# The generic linux-x86_64 tarball needs no root. JULIA_DEPOT_PATH under the prefix keeps the
# package set out of ~/.julia, so provisioning cannot disturb a user's own Julia install.
provision_julia() {
  if [ -x "$PREFIX/julia-$JULIA_VERSION/bin/julia" ]; then
    skip "Julia $JULIA_VERSION"
  else
    local short="${JULIA_VERSION%.*}"
    fetch "https://julialang-s3.julialang.org/bin/linux/x64/$short/julia-$JULIA_VERSION-linux-x86_64.tar.gz" \
          "julia-$JULIA_VERSION-linux-x86_64.tar.gz" "$JULIA_SHA256"
    log "installing Julia $JULIA_VERSION"
    tar xzf "$SRC/julia-$JULIA_VERSION-linux-x86_64.tar.gz" -C "$PREFIX"
    note "Julia $JULIA_VERSION"
  fi
  ln -sf "$PREFIX/julia-$JULIA_VERSION/bin/julia" "$PREFIX/bin/julia"

  local depot="$PREFIX/julia-depot"
  if [ -f "$depot/environments/v${JULIA_VERSION%.*}/Manifest.toml" ] &&
     grep -q "AbstractAlgebra" "$depot/environments/v${JULIA_VERSION%.*}/Project.toml" 2>/dev/null; then
    skip "Groebner.jl $GROEBNER_JL_VERSION"
    return 0
  fi
  mkdir -p "$depot"
  log "installing Groebner.jl $GROEBNER_JL_VERSION and AbstractAlgebra $ABSTRACTALGEBRA_JL_VERSION"
  # AbstractAlgebra is a direct dependency on purpose: Groebner.jl takes its polynomials from a
  # ring, and does not re-export polynomial_ring, so a script needs it in the environment.
  JULIA_DEPOT_PATH="$depot" "$PREFIX/julia-$JULIA_VERSION/bin/julia" -e "
    using Pkg
    Pkg.add([
      PackageSpec(name=\"Groebner\",         version=\"$GROEBNER_JL_VERSION\"),
      PackageSpec(name=\"AbstractAlgebra\",  version=\"$ABSTRACTALGEBRA_JL_VERSION\"),
    ])
    Pkg.status()
  " > "$BUILD/groebner-jl.log" 2>&1
  note "Groebner.jl $GROEBNER_JL_VERSION + AbstractAlgebra $ABSTRACTALGEBRA_JL_VERSION"
}

# --- Sagebrush -------------------------------------------------------------------------------
# Not on crates.io, so the repository is cloned at a pinned commit. Its Groebner engine
# (engine/mpoly) is a library with no CLI — engine/cli builds a `sagebrush` binary but depends
# only on bigint/modsym/ap/par and exposes no Groebner entry point — so Zeebra's own small
# driver (tools/external/sagebrush-driver, MIT, committed in this repository) calls
# f4::groebner_p. CARGO_TARGET_DIR is pinned inside the prefix so this build can never share
# or invalidate Zeebra's own target directory.
provision_sagebrush() {
  local driver_src repo="$SRC/sagebrush"
  driver_src="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/sagebrush-driver"

  if [ ! -d "$repo/.git" ]; then
    log "cloning Sagebrush at $SAGEBRUSH_COMMIT"
    git clone --quiet https://github.com/sagemathinc/sagebrush.git "$repo"
  fi
  if [ "$(git -C "$repo" rev-parse HEAD)" != "$SAGEBRUSH_COMMIT" ]; then
    git -C "$repo" fetch --quiet origin
    git -C "$repo" checkout --quiet --detach "$SAGEBRUSH_COMMIT"
    note "Sagebrush @ ${SAGEBRUSH_COMMIT:0:8}"
  else
    skip "Sagebrush @ ${SAGEBRUSH_COMMIT:0:8}"
  fi

  # The driver is copied rather than built in place so the repository stays clean and the
  # pinned path dependency below resolves to the prefix.
  mkdir -p "$PREFIX/sagebrush-driver/src"
  cp "$driver_src/Cargo.toml" "$PREFIX/sagebrush-driver/Cargo.toml"
  cp "$driver_src/src/main.rs" "$PREFIX/sagebrush-driver/src/main.rs"

  log "building the Sagebrush Groebner driver"
  # RUSTC_WRAPPER="" defeats a globally configured sccache, which keys on CARGO_TARGET_DIR and
  # would otherwise produce a stale rlib here.
  (
    cd "$PREFIX/sagebrush-driver"
    RUSTC_WRAPPER="" \
    CARGO_TARGET_DIR="$PREFIX/cargo-target" \
    RUSTUP_TOOLCHAIN="${ZEEBRA_EXT_RUST_TOOLCHAIN:-stable}" \
      cargo build --release
  ) > "$BUILD/sagebrush-driver.log" 2>&1
  ln -sf "$PREFIX/cargo-target/release/sagebrush-gb-driver" "$PREFIX/bin/sagebrush-gb-driver"
  note "sagebrush-gb-driver"
}

# --- Singular --------------------------------------------------------------------------------
# Not provisioned: it is a system package here and building it would duplicate a working
# install. Reported so the summary says what the smoke test can actually run.
check_singular() {
  if command -v Singular > /dev/null 2>&1; then
    skip "Singular (system: $(Singular --version 2>&1 | head -1 | sed 's/^Singular *//'))"
  else
    log "WARNING: Singular is not on PATH; its smoke test will be skipped"
  fi
}

provision_gmp
provision_mpfr
provision_flint
provision_msolve
provision_julia
provision_sagebrush
check_singular

echo
echo "prefix: $PREFIX"
if [ "${#INSTALLED[@]}" -gt 0 ]; then
  echo "installed:"
  printf '  + %s\n' "${INSTALLED[@]}"
fi
if [ "${#SKIPPED[@]}" -gt 0 ]; then
  echo "already present:"
  printf '  = %s\n' "${SKIPPED[@]}"
fi
echo
echo "next: source tools/external/env.sh, then run tools/external/smoke/smoke.sh"
