#!/usr/bin/env bash
# Same-machine univariate factoring, Zeebra against FLINT, on identical inputs (#784).
#
#   tools/external/flint-factor-compare.sh <zeebra-example-binary> <inputs-dir> [reps]
#
# <zeebra-example-binary> is the built `modular_composition` example; <inputs-dir> is what its
# `export` mode wrote. Each side is a separate process that times its own factorization call, so
# process start-up and file parsing are outside both figures. Per input the script first checks
# that every arm returns the same multiset of monic factors with multiplicity (and stops on a
# disagreement), then runs the arms once per repetition, rotating their order, and prints the
# median and minimum in milliseconds.
#
# FLINT arms: `default` is nmod_poly_factor / fmpz_mod_poly_factor; `cz` and `ks` force
# Cantor–Zassenhaus and Kaltofen–Shoup, so the default's choice can be read off the timings.
# Pin and serialize the caller, not this script:
#
#   tools/benchlock.sh <tag> taskset -c 8 tools/external/flint-factor-compare.sh ...

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=env.sh
. "$HERE/env.sh"

if [ "$#" -lt 2 ] || [ "$#" -gt 3 ]; then
  echo "usage: $0 <zeebra-example-binary> <inputs-dir> [reps]" >&2
  exit 2
fi
ZEEBRA_BIN="$1"
INPUTS="$2"
REPS="${3:-5}"
FLINT_BIN="$(command -v flint-factor-driver)" || {
  echo "flint-factor-driver is not on PATH; run tools/external/provision-flint-factor.sh" >&2
  exit 1
}
INPUT_NAMES="${ZEEBRA_FLINT_INPUTS:-koalabear-random-81 koalabear-random-729 goldilocks-random-81 bn254fr-random-81 koalabear-linquad-729 koalabear-linquad-6561}"
ARMS=(zeebra flint-default flint-cz flint-ks)

OUT="$(mktemp -d "${TMPDIR:-/tmp}/zeebra-flint-compare.XXXXXX")"
trap 'rm -rf "$OUT"' EXIT

# run_arm <arm> <input> [<out>] -> prints the arm's time_ns
run_arm() {
  local arm="$1" input="$2" out="${3:-}" line
  case "$arm" in
    zeebra)
      if [ -n "$out" ]; then
        line="$("$ZEEBRA_BIN" factor-file "path=$input" "out=$out")"
      else
        line="$("$ZEEBRA_BIN" factor-file "path=$input")"
      fi ;;
    flint-*)
      local args=(--algorithm "${arm#flint-}" "$input")
      if [ -n "$out" ]; then args+=("$out"); fi
      line="$("$FLINT_BIN" "${args[@]}")" ;;
  esac
  case "$line" in
    "time_ns "*) echo "${line#time_ns }" ;;
    *) echo "$arm printed no time_ns for $input" >&2; return 1 ;;
  esac
}

# median and minimum of the integers in a file, in milliseconds
summary() {
  sort -n "$1" | awk '{ v[NR] = $1 } END { printf "%.3f (%.3f)", v[int((NR + 1) / 2)] / 1e6, v[1] / 1e6 }'
}
median_ns() {
  sort -n "$1" | awk '{ v[NR] = $1 } END { print v[int((NR + 1) / 2)] }'
}

echo "zeebra binary: $ZEEBRA_BIN"
"$FLINT_BIN" --version | sed 's/^/flint driver: /'
echo "affinity: $(taskset -pc $$ 2>/dev/null | sed 's/.*: //')"
echo

for name in $INPUT_NAMES; do
  input="$INPUTS/$name.poly"
  [ -f "$input" ] || { echo "missing $input" >&2; exit 1; }
  for arm in "${ARMS[@]}"; do
    run_arm "$arm" "$input" "$OUT/$name.$arm.raw" > /dev/null
    LC_ALL=C sort "$OUT/$name.$arm.raw" > "$OUT/$name.$arm.factors"
    if ! cmp -s "$OUT/$name.zeebra.factors" "$OUT/$name.$arm.factors"; then
      echo "DISAGREEMENT on $name: $arm differs from zeebra" >&2
      diff "$OUT/$name.zeebra.factors" "$OUT/$name.$arm.factors" | head -20 >&2
      exit 1
    fi
  done
  distinct="$(wc -l < "$OUT/$name.zeebra.factors")"
  largest="$(awk '{ if (NF - 2 > m) m = NF - 2 } END { print m }' "$OUT/$name.zeebra.factors")"
  echo "agree: $name ($distinct distinct monic factors, largest degree $largest, all ${#ARMS[@]} arms identical)"
  echo "$name $distinct $largest" >> "$OUT/shape"
done
echo

echo "| input | distinct factors | largest factor degree | reps | Zeebra | FLINT default | FLINT CZ | FLINT KS | Zeebra / FLINT default |"
echo "|---|---:|---:|---:|---:|---:|---:|---:|---:|"
for name in $INPUT_NAMES; do
  input="$INPUTS/$name.poly"
  reps="$REPS"
  case "$name" in *-6561) reps=$(( REPS < 3 ? REPS : 3 )) ;; esac
  for arm in "${ARMS[@]}"; do : > "$OUT/$name.$arm.times"; done
  for (( rep = 0; rep < reps; rep++ )); do
    for (( k = 0; k < ${#ARMS[@]}; k++ )); do
      arm="${ARMS[$(( (rep + k) % ${#ARMS[@]} ))]}"
      run_arm "$arm" "$input" >> "$OUT/$name.$arm.times"
    done
  done
  read -r _ distinct largest < <(grep "^$name " "$OUT/shape")
  ratio="$(awk -v z="$(median_ns "$OUT/$name.zeebra.times")" -v f="$(median_ns "$OUT/$name.flint-default.times")" \
    'BEGIN { printf "%.2fx", z / f }')"
  echo "| $name | $distinct | $largest | $reps | $(summary "$OUT/$name.zeebra.times") | $(summary "$OUT/$name.flint-default.times") | $(summary "$OUT/$name.flint-cz.times") | $(summary "$OUT/$name.flint-ks.times") | $ratio |"
done
