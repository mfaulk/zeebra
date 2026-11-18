#!/usr/bin/env bash
# #86 runs. Binaries: BIN/stock (default features) and BIN/work (--features research-work), both
# built from the commit recorded in each output file's header line. Timings go through
# tools/benchlock.sh; the census and residual counts are exact and need no lock.
#
#   research/gpu-kernels/run.sh ceilings|stages|census|residual
set -euo pipefail
BIN=${BIN:-/buildcache/cargo-target/zeebra-86/bin}
OUT=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$OUT/../.." && pwd)
ONE=${ONE:-40}
SIXTEEN=${SIXTEEN:-40-55}
REPS=${REPS:-5}
COMMIT=${COMMIT:?set COMMIT to the commit the binaries were built from}
# system/field pairs; every one is public and generated in-crate.
CASES=(katsura-9/goldilocks katsura-9/bn254
       cyclic-7/goldilocks cyclic-7/bn254 cyclic-7/gf256
       mq-10/m31 mq-10/gf256)

one() { # <binary> <cpus> <workers> <system/field> [extra]
    local bin=$1 cpus=$2 workers=$3 case=$4
    shift 4
    taskset -c "$cpus" "$bin" f4 --system "${case%/*}" --field "${case#*/}" --workers "$workers" "$@"
}

case ${1:-} in
ceilings)
    tools_lock="$ROOT/tools/benchlock.sh"
    "$tools_lock" zb-86 taskset -c "$ONE" "$BIN/stock/gpu_kernel_census" ceilings --reps "$REPS" \
        > "$OUT/ceilings-$COMMIT.json"
    ;;
stages)
    out="$OUT/f4-stages-$COMMIT.jsonl"
    : > "$out"
    inner=$(mktemp)
    cat > "$inner" <<EOF
set -euo pipefail
$(declare -f one)
for rep in \$(seq 1 $REPS); do
  for c in ${CASES[*]}; do
    for w in 1 16; do
      cpus=$ONE; [ \$w = 16 ] && cpus=$SIXTEEN
      line=\$(one "$BIN/stock/gpu_kernel_census" \$cpus \$w \$c)
      echo "\${line%\}},\"rep\":\$rep,\"load1\":\$(cut -d' ' -f1 /proc/loadavg)}" >> "$out"
    done
  done
done
EOF
    "$ROOT/tools/benchlock.sh" zb-86 bash "$inner"
    rm -f "$inner"
    ;;
census)
    out="$OUT/f4-census-$COMMIT.jsonl"
    : > "$out"
    for c in "${CASES[@]}"; do one "$BIN/work/gpu_kernel_census" "$ONE" 1 "$c" --work >> "$out"; done
    ;;
residual)
    taskset -c "$ONE" "$BIN/work/block_density" residual-work mq-random > "$OUT/residual-work-$COMMIT.md"
    taskset -c "$ONE" "$BIN/work/block_density" residual-work-large mq-random-14 \
        >> "$OUT/residual-work-$COMMIT.md"
    ;;
*) echo "usage: $0 ceilings|stages|census|residual" >&2; exit 64 ;;
esac
