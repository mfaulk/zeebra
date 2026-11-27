#!/usr/bin/env bash
# Same-machine per-primitive univariate comparison: Zeebra against FLINT and NTL (#1206).
#
#   tools/external/univariate-primitives-compare.sh <zeebra-example-binary> <work-dir>
#
# <zeebra-example-binary> is the built `univariate_primitives` example. Each side is a separate
# process that times its own call, so process start-up and parsing are outside every figure.
# Per (field, primitive, size) the script exports one job, runs every arm once and requires that
# its output matches Zeebra's byte for byte (stopping on a disagreement), then runs ROUNDS rounds
# with the arm order rotated, each process timing REPS calls. The figure per arm is the median of
# its per-process medians. A (field, primitive) stops growing once Zeebra or FLINT takes longer
# than CAP_S seconds a call; NTL is dropped from a row once it does. Jobs are deleted after use,
# because they reach hundreds of megabytes at 2^20 over BN254.
#
# Environment: FIELDS, PRIMITIVES, MIN_LOG (8), MAX_LOG (20), ROUNDS (3), CAP_S (2),
# FLINT_DRIVER and NTL_DRIVER (default: on PATH). NTL_DRIVER=none skips NTL. Pin and serialize
# the caller, not this script:
#
#   tools/benchlock.sh <tag> taskset -c 8 tools/external/univariate-primitives-compare.sh ...
#
# Bash 3.2 compatible (macOS): no associative arrays, no mapfile.

set -euo pipefail

if [ "$#" -ne 2 ]; then
  echo "usage: $0 <zeebra-example-binary> <work-dir>" >&2
  exit 2
fi
ZEEBRA_BIN="$1"
WORK="$2"
FIELDS="${FIELDS:-koalabear goldilocks p64m59 bn254fr}"
PRIMITIVES="${PRIMITIVES:-mul divrem gcd xgcd powmod roots multieval interpolate compose resultant}"
MIN_LOG="${MIN_LOG:-8}"
MAX_LOG="${MAX_LOG:-20}"
ROUNDS="${ROUNDS:-3}"
CAP_S="${CAP_S:-2}"
FLINT_BIN="${FLINT_DRIVER:-$(command -v flint-primitives-driver || true)}"
NTL_BIN="${NTL_DRIVER:-$(command -v ntl-primitives-driver || echo none)}"
[ -x "$FLINT_BIN" ] || { echo "no FLINT driver; set FLINT_DRIVER or see README.md" >&2; exit 1; }
CAP_NS=$(( CAP_S * 1000000000 ))
mkdir -p "$WORK"

# arm_cmd <arm> <job> <reps> [<out>] -> runs the arm, printing its stdout
arm_cmd() {
  local arm="$1" job="$2" reps="$3" out="${4:-}"
  case "$arm" in
    zeebra)
      if [ -n "$out" ]; then
        "$ZEEBRA_BIN" run "path=$job" "reps=$reps" "out=$out"
      else
        "$ZEEBRA_BIN" run "path=$job" "reps=$reps"
      fi ;;
    flint) "$FLINT_BIN" "$job" "$reps" ${out:+"$out"} ;;
    ntl) "$NTL_BIN" "$job" "$reps" ${out:+"$out"} ;;
  esac
}

# time_of <stdout> -> the time_ns value, or nothing
time_of() { printf '%s\n' "$1" | awk '$1 == "time_ns" { print $2 }'; }

# normalized <file> <primitive>: roots come back in any order, everything else is ordered
normalized() {
  if [ "$2" = roots ]; then LC_ALL=C sort "$1"; else cat "$1"; fi
}

median() { sort -n | awk '{ v[NR] = $1 } END { if (NR) print v[int((NR + 1) / 2)] }'; }

ms() { awk -v t="$1" 'BEGIN { if (t == "") print "—"; else printf "%.3f", t / 1e6 }'; }
ratio() {
  awk -v z="$1" -v o="$2" 'BEGIN { if (z == "" || o == "" || o == 0) print "—"; else printf "%.2f", z / o }'
}

echo "zeebra binary: $ZEEBRA_BIN"
"$FLINT_BIN" --version | sed 's/^/flint driver: /'
if [ "$NTL_BIN" != none ]; then "$NTL_BIN" --version | sed 's/^/ntl driver: /'; fi
echo "affinity: $(taskset -pc $$ 2>/dev/null | sed 's/.*: //' || echo unpinned)"
echo "rounds: $ROUNDS, cap: ${CAP_S}s a call"
echo
echo "| field | primitive | n | Zeebra (ms) | FLINT (ms) | NTL (ms) | Zeebra / FLINT | Zeebra / NTL |"
echo "|---|---|--:|--:|--:|--:|--:|--:|"

for field in $FIELDS; do
  for primitive in $PRIMITIVES; do
    ntl_live=1
    [ "$NTL_BIN" = none ] && ntl_live=0
    for (( log = MIN_LOG; log <= MAX_LOG; log++ )); do
      n=$(( 1 << log ))
      job="$("$ZEEBRA_BIN" export "dir=$WORK" "field=$field" "primitive=$primitive" "n=$n")"
      arms="zeebra flint"
      [ "$ntl_live" = 1 ] && arms="$arms ntl"

      # Correctness, and a first time per arm that sets how many calls a process makes.
      live=""
      slowest=0
      for arm in $arms; do
        status=0
        line="$(arm_cmd "$arm" "$job" 1 "$WORK/out.$arm")" || status=$?
        if [ "$status" = 3 ]; then continue; fi   # the library has no entry point for this
        [ "$status" = 0 ] || { echo "$arm failed on $job (status $status)" >&2; exit 1; }
        if [ "$arm" != zeebra ] && ! cmp -s <(normalized "$WORK/out.zeebra" "$primitive") \
            <(normalized "$WORK/out.$arm" "$primitive"); then
          echo "DISAGREEMENT on $field $primitive n=$n: $arm differs from zeebra" >&2
          diff <(normalized "$WORK/out.zeebra" "$primitive") \
            <(normalized "$WORK/out.$arm" "$primitive") | head -c 2000 >&2
          exit 1
        fi
        live="$live $arm"
        t="$(time_of "$line")"
        [ "$t" -gt "$slowest" ] && slowest="$t"
      done
      # Calls per process: enough for ~0.3 s, between 1 and 7.
      reps=$(( slowest > 0 ? 300000000 / slowest : 7 ))
      (( reps < 1 )) && reps=1
      (( reps > 7 )) && reps=7

      # shellcheck disable=SC2086 # $live is a deliberate word list of arm names
      set -- $live
      count=$#
      for arm in $live; do : > "$WORK/times.$arm"; done
      for (( round = 0; round < ROUNDS; round++ )); do
        for (( k = 0; k < count; k++ )); do
          index=$(( (round + k) % count + 1 ))
          arm="${!index}"
          time_of "$(arm_cmd "$arm" "$job" "$reps")" >> "$WORK/times.$arm"
        done
      done
      z="$(median < "$WORK/times.zeebra")"
      f=""
      if [[ " $live " == *" flint "* ]]; then f="$(median < "$WORK/times.flint")"; fi
      t_ntl=""
      if [[ " $live " == *" ntl "* ]]; then t_ntl="$(median < "$WORK/times.ntl")"; fi
      echo "| $field | $primitive | $n | $(ms "$z") | $(ms "$f") | $(ms "$t_ntl") | $(ratio "$z" "$f") | $(ratio "$z" "$t_ntl") |"
      rm -f "$job" "$WORK"/out.* "$WORK"/times.*

      if [ -n "$t_ntl" ] && [ "$t_ntl" -gt "$CAP_NS" ]; then ntl_live=0; fi
      if [ "$z" -gt "$CAP_NS" ] || { [ -n "$f" ] && [ "$f" -gt "$CAP_NS" ]; }; then break; fi
    done
  done
done
