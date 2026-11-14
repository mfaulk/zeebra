#!/usr/bin/env bash
# Factors two hand-checked polynomials with flint-factor-driver and compares the monic factors
# with multiplicity against the expected files: (x-1)^2 (x^2+1) scaled by 3 over GF(7) on the
# nmod_poly path, and 5 (x-1)^2 (x-2) over BN254 Fr on the fmpz_mod_poly path. Both inputs are
# non-monic, so the leading coefficient is exercised too. A missing driver is reported absent and
# fails, never passes as agreement.

set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PREFIX="${ZEEBRA_EXT_PREFIX:-$HOME/.local/opt/zeebra-ext}"
export ZEEBRA_EXT_PREFIX="$PREFIX"
# shellcheck source=../env.sh
. "$HERE/../env.sh"

if ! command -v flint-factor-driver > /dev/null 2>&1; then
  echo "absent: flint-factor-driver is not on PATH (run tools/external/provision-flint-factor.sh)"
  exit 1
fi

OUT="${TMPDIR:-/tmp}/zeebra-flint-smoke-$$"
mkdir -p "$OUT"
trap 'rm -rf "$OUT"' EXIT

flint-factor-driver --version
status=0
for case in gf7 bn254fr; do
  for alg in default cz ks berlekamp; do
    if ! flint-factor-driver --algorithm "$alg" "$HERE/flint-factor/$case.poly" "$OUT/$case.$alg" > /dev/null; then
      printf '  %-8s %-10s driver failed\n' "$case" "$alg"
      status=1
      continue
    fi
    LC_ALL=C sort "$OUT/$case.$alg" > "$OUT/$case.$alg.sorted"
    if cmp -s "$OUT/$case.$alg.sorted" "$HERE/flint-factor/$case.expected"; then
      printf '  %-8s %-10s == expected\n' "$case" "$alg"
    else
      printf '  %-8s %-10s != expected  <-- DISAGREEMENT\n' "$case" "$alg"
      diff "$HERE/flint-factor/$case.expected" "$OUT/$case.$alg.sorted" | sed 's/^/      /'
      status=1
    fi
  done
done
exit "$status"
