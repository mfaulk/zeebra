#!/usr/bin/env bash
# Build the authors' M5GB reference (#1165) at a pinned commit, with its pinned Mathic and
# Memtailor, and print the path of the binary.
#
#   tools/external/provision-m5gb-paper.sh                  # the unmodified reference
#   tools/external/provision-m5gb-paper.sh hash-probe       # + key-collision counters, no repair
#   tools/external/provision-m5gb-paper.sh hash-narrow      # + reducer-map keys forced to collide
#   tools/external/provision-m5gb-paper.sh repair-interreduce  # + zero-input repair (a correctness fix)
#
# The reference is a MathicGB fork whose files assert GPL-2.0-or-later; it runs only as a
# subprocess and nothing from it is vendored or committed (docs/research/m5gb-paper-reference.md).
# Sources are fetched to $ZEEBRA_M5GB_PREFIX (default ~/.cache/zeebra-external/m5gb-paper).
#
# Upstream builds with `make` and g++ against installed libmathic/libmemtailor, which come with
# autotools. Neither host needs those: the three trees are compiled directly into one binary. Every
# change to upstream source is a patch file in $M5GB_PATCH_DIR (default
# ~/.cache/zeebra-external/m5gb-paper/patches):
#   *-build-clang.patch  build-only: what clang rejects and g++ accepted; no behaviour change
#   m5gb-<variant>.patch a diagnostic variant, built as its own binary and never the reference
# The patches are derived from GPL-2.0-or-later code, so they are kept outside this repository.
# The repository holds only their SHA-256 digests (m5gb-paper/patches.sha256); each patch is
# described in prose in docs/research/m5gb-paper-reference.md §2 so it can be recreated.
# Each binary carries a .build sidecar naming the revisions, compiler, flags and patches.
#
# Exit status: 0 built, 1 fetch or build failure, 2 usage, 3 a patch is missing or its digest
# does not match patches.sha256.
set -euo pipefail

readonly M5GB_REV=16ef968db7f3c2d1899e915e0904034672b8afee
readonly M5GB_REPO=https://extgit.isec.tugraz.at/krypto/m5gb.git
readonly MATHIC_REV=66b5d74f8417459414cbf3753cfa9a0128483cbd
readonly MATHIC_REPO=https://github.com/broune/mathic.git
readonly MEMTAILOR_REV=722a30ce258eb38bee0a834406aed60a06f32d1d
readonly MEMTAILOR_REPO=https://github.com/broune/memtailor.git

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PATCHES="${M5GB_PATCH_DIR:-$HOME/.cache/zeebra-external/m5gb-paper/patches}"
DIGESTS="$HERE/m5gb-paper/patches.sha256"
PREFIX="${ZEEBRA_M5GB_PREFIX:-$HOME/.cache/zeebra-external/m5gb-paper}"
JOBS="${ZEEBRA_M5GB_JOBS:-4}"
VARIANT="${1:-upstream}"

case "$VARIANT" in
  upstream) EXTRA_PATCH="" ;;
  hash-probe | hash-narrow | repair-interreduce) EXTRA_PATCH="$PATCHES/m5gb-$VARIANT.patch" ;;
  *)
    echo "usage: $0 [upstream|hash-probe|hash-narrow|repair-interreduce]" >&2
    exit 2
    ;;
esac

if [ -z "${CXX:-}" ]; then
  if [ "$(uname -s)" = Darwin ]; then CXX=clang++; else CXX=c++; fi
fi
# Upstream's Makefile flags, less -ggdb (gdb-specific; -g stays). No -DNDEBUG: upstream builds
# with assert() live, and so does this.
FLAGS="-std=c++14 -O3 -g -DMATHICGB_NO_TBB"
LIBFLAGS="-std=c++14 -O3 -g"

# fetch <repo> <rev> <dir>: a clean checkout of <rev>; local changes there are discarded.
fetch() {
  if [ ! -d "$3/.git" ]; then
    git clone --quiet "$1" "$3"
  fi
  if ! git -C "$3" cat-file -e "$2^{commit}" 2>/dev/null; then
    git -C "$3" fetch --quiet origin
  fi
  git -C "$3" checkout --quiet --force --detach "$2"
  git -C "$3" clean --quiet -fdx
  if [ "$(git -C "$3" rev-parse HEAD)" != "$2" ]; then
    echo "provision-m5gb-paper: $3 is not at $2" >&2
    exit 1
  fi
}

# check_patch <name>: the patch exists in $PATCHES and matches its committed digest, or exit 3.
check_patch() {
  local want got
  want="$(awk -v f="$1" '$2 == f {print $1}' "$DIGESTS")"
  if [ -z "$want" ]; then
    echo "provision-m5gb-paper: $1 has no digest in $DIGESTS" >&2
    exit 3
  fi
  if [ ! -f "$PATCHES/$1" ]; then
    echo "provision-m5gb-paper: patch $PATCHES/$1 is missing. The patches are kept outside the" >&2
    echo "  repository (GPL-derived); recreate them from docs/research/m5gb-paper-reference.md §2" >&2
    echo "  or point M5GB_PATCH_DIR at a copy." >&2
    exit 3
  fi
  got="$(shasum -a 256 "$PATCHES/$1" | cut -d' ' -f1)"
  if [ "$got" != "$want" ]; then
    echo "provision-m5gb-paper: $PATCHES/$1 has sha256 $got, expected $want" >&2
    exit 3
  fi
}

check_patch mathic-build-clang.patch
check_patch m5gb-build-clang.patch
if [ -n "$EXTRA_PATCH" ]; then check_patch "$(basename "$EXTRA_PATCH")"; fi

SRC="$PREFIX/src"
mkdir -p "$SRC" "$PREFIX/bin"
fetch "$M5GB_REPO" "$M5GB_REV" "$SRC/m5gb"
fetch "$MATHIC_REPO" "$MATHIC_REV" "$SRC/mathic"
fetch "$MEMTAILOR_REPO" "$MEMTAILOR_REV" "$SRC/memtailor"

git -C "$SRC/mathic" apply "$PATCHES/mathic-build-clang.patch"
git -C "$SRC/m5gb" apply "$PATCHES/m5gb-build-clang.patch"
patches="mathic-build-clang.patch m5gb-build-clang.patch"
if [ -n "$EXTRA_PATCH" ]; then
  git -C "$SRC/m5gb" apply "$EXTRA_PATCH"
  patches="$patches $(basename "$EXTRA_PATCH")"
fi

out="$PREFIX/bin/runm5gb-$VARIANT"
patch_digest="$(cat "$PATCHES/mathic-build-clang.patch" "$PATCHES/m5gb-build-clang.patch" \
  ${EXTRA_PATCH:+"$EXTRA_PATCH"} | shasum -a 256 | cut -c1-16)"
sidecar="m5gb=$M5GB_REV
mathic=$MATHIC_REV
memtailor=$MEMTAILOR_REV
variant=$VARIANT
patches=$patches
patch_sha256=$patch_digest
cxx=$("$CXX" --version | head -n 1)
flags=$FLAGS
libflags=$LIBFLAGS
host=$(uname -s) $(uname -m)"
if [ -x "$out" ] && [ "$(cat "$out.build" 2>/dev/null)" = "$sidecar" ]; then
  echo "$out"
  exit 0
fi

OBJ="$PREFIX/obj-$VARIANT"
rm -rf "$OBJ"
mkdir -p "$OBJ/memtailor" "$OBJ/mathic" "$OBJ/m5gb"
INC="-I$SRC/m5gb/code/project/m5gb -I$SRC/mathic/src -I$SRC/memtailor/src"

# compile <flags> <objdir> <sources...>, JOBS at a time.
compile() {
  local flags="$1" dir="$2"
  shift 2
  printf '%s\n' "$@" | xargs -P "$JOBS" -I{} sh -c \
    'f="$1"; o="$2/$(basename "$f" .cpp).o"; '"$CXX"' $3 -w -c "$f" -o "$o"' _ {} "$dir" "$flags"
}

compile "$LIBFLAGS $INC" "$OBJ/memtailor" \
  "$SRC"/memtailor/src/memtailor/{BufferPool,Arena,MemoryBlocks}.cpp "$SRC/memtailor/src/memtailor.cpp"
compile "$LIBFLAGS $INC" "$OBJ/mathic" \
  "$SRC"/mathic/src/mathic/{Timer,ColumnPrinter,DivMask,Action,BoolParameter,CliParameter,CliParser,error,HelpAction,IntegerParameter,StringParameter,display,BitTriangle}.cpp \
  "$SRC/mathic/src/mathic.cpp"
compile "$FLAGS $INC" "$OBJ/m5gb" "$SRC"/m5gb/code/project/m5gb/*.cpp

# Upstream links -lmemtailor -lmathic -Bdynamic; the libraries are linked as objects here.
"$CXX" -o "$out" "$OBJ"/m5gb/*.o "$OBJ"/mathic/*.o "$OBJ"/memtailor/*.o
printf '%s\n' "$sidecar" > "$out.build"
echo "$out"
