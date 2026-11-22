#!/usr/bin/env bash
# Builds one commit from `git archive` in two different directories and checks that the artifact is
# byte-identical, so a measured binary can be matched to a rebuild by hash (#1021).
#
#   tools/check-archive-reproducible.sh [--repo DIR] [--workdir DIR] <commit> <artifact> -- <cargo build args>
#   tools/check-archive-reproducible.sh 9d6f16e4 release/examples/sig_f4_study \
#       -- --release --locked --features research-sigf4 --example sig_f4_study
#
# <artifact> is relative to the target directory. The two builds run concurrently, each with its own
# source and target directory at a different depth. rc 0 = identical; 1 = they differ, and every
# string naming either build's directory is listed with the directory replaced by <src> or
# <target>; 2 = usage error or a failed build. --workdir defaults to a fresh directory under
# $TMPDIR and is removed afterwards; a given one is kept.
set -euo pipefail

usage() {
  sed -n '5,7p' "$0" >&2
  exit 2
}

repo=. workdir=
while [[ $# -gt 0 ]]; do
  case $1 in
    --repo) repo=${2:?}; shift 2 ;;
    --workdir) workdir=${2:?}; shift 2 ;;
    *) break ;;
  esac
done
[[ $# -ge 3 && $3 == -- ]] || usage
commit=$1 artifact=$2
shift 3

sha256() { if command -v sha256sum >/dev/null; then sha256sum "$1"; else shasum -a 256 "$1"; fi | cut -c1-64; }

if [[ -z $workdir ]]; then
  workdir="$(mktemp -d "${TMPDIR:-/tmp}/archive-repro.XXXXXX")"
  trap 'rm -rf "$workdir"' EXIT
fi
mkdir -p "$workdir"
workdir="$(cd "$workdir" && pwd -P)"

# Different names and depths, so neither a path's length nor its text can coincide.
srcs=("$workdir/one/src" "$workdir/second/build/tree/src")
targets=("$workdir/one/target" "$workdir/target-of-the-second")

archive="$workdir/source.tar"
if ! git -C "$repo" archive -o "$archive" "$commit" 2>"$workdir/archive.log"; then
  echo "check-archive-reproducible: cannot archive $commit:" >&2
  cat "$workdir/archive.log" >&2
  exit 2
fi

pids=()
for i in 0 1; do
  mkdir -p "${srcs[$i]}"
  tar -xf "$archive" -C "${srcs[$i]}"
  (cd "${srcs[$i]}" && CARGO_TARGET_DIR="${targets[$i]}" cargo build "$@" >"$workdir/build-$i.log" 2>&1) &
  pids+=($!)
done
for i in 0 1; do
  if ! wait "${pids[$i]}"; then
    echo "check-archive-reproducible: build $i failed; its log ($workdir/build-$i.log) ends:" >&2
    tail -20 "$workdir/build-$i.log" >&2
    exit 2
  fi
done

hashes=()
for i in 0 1; do
  binary="${targets[$i]}/$artifact"
  [[ -f $binary ]] || { echo "check-archive-reproducible: no $artifact in build $i" >&2; exit 2; }
  hashes+=("$(sha256 "$binary")")
done

if [[ ${hashes[0]} == "${hashes[1]}" ]]; then
  echo "reproducible: $artifact ${hashes[0]} from $commit in two directories"
  exit 0
fi

echo "NOT reproducible: $artifact from $commit differs between two directories"
echo "  ${hashes[0]}  ${srcs[0]}"
echo "  ${hashes[1]}  ${srcs[1]}"
echo "strings naming a build directory:"
found=0
for i in 0 1; do
  while IFS= read -r line; do
    found=1
    line=${line//"${srcs[$i]}"/<src>}
    echo "  build $i: ${line//"${targets[$i]}"/<target>}"
  done < <(LC_ALL=C strings -a "${targets[$i]}/$artifact" | grep -F -e "${srcs[$i]}" -e "${targets[$i]}" | sort -u)
done
[[ $found -eq 1 ]] || echo "  none; the difference is not a plain path string (compare the binaries' sections)"
exit 1
