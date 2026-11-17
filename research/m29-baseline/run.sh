#!/usr/bin/env bash
# #834: the M29 frozen baseline, one suite per benchlock acquisition.
#
#   T=/buildcache/cargo-target/zeebra-834
#   CARGO_TARGET_DIR=$T OUT=$T/m29 tools/benchlock.sh zb-834 \
#     timeout --signal=INT --kill-after=60s 3600 bash research/m29-baseline/run.sh SUITE
#
# SUITE is one of:
#   identities   executable paths, versions and SHA-256s (no timing; no lock needed)
#   mq10         comparand-scaling.py: Zeebra, msolve, grobx, groebner-rs on MQ10 at 32003 and
#                2^31-1, workers 1/4/8/16, five repetitions, answers checked against #739's references
#   wide         wide-corpus.py: grobx and groebner-rs on Eco-12/2^64-353 and MQ11/Goldilocks, one
#                worker, three passes (the controller takes one attempt per cell)
#   walls|stages|ab831|census
#                costmodel.py over m29_cost_model on all four targets (see that file)
#   fl|flstages  #828 cross-check: FL_BIN (m29_cost_model built on the #843 library), forward
#                against Faugère–Lachartre on Eco-12 and MQ11 at 16 workers; `flstages` adds stage clocks
#
# REPS sets the repetitions (wide passes included); 3 by default, 5 for `fl`. MQ10_REPS sets
# `mq10`'s repeats (5 by default) and MQ10_WALL its campaign wall in seconds (1800).
#
# Needs a clean committed tree (both controllers refuse otherwise) and, in $CARGO_TARGET_DIR/bin,
# m29_cost_model, m29_cost_model_work (built with research-work), zeebra_driver, wide_corpus,
# grobx-driver and groebner-rs-driver, plus the debug competitive_sweep input exporter.
set -u
: "${CARGO_TARGET_DIR:?}" "${OUT:?output directory}"
suite="${1:?suite}"
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
cd "$root" || exit 2
# shellcheck source=../../tools/external/env.sh
. tools/external/env.sh
bin="$CARGO_TARGET_DIR/bin"
export PATH="$bin:$PATH" TMPDIR="$CARGO_TARGET_DIR/tmp" ZEEBRA_MACHINE=5995wx
export ZEEBRA_GROEBNER_RS_DRIVER="$bin/groebner-rs-driver" ZEEBRA_GROBX_DRIVER="$bin/grobx-driver"
export ZEEBRA_DRIVER="$bin/zeebra_driver"
mkdir -p "$OUT" "$TMPDIR"

# Settle: wait (bounded, 10 min) for the 1-minute load to fall under 8, then record what the suite
# actually started at, compiler count included. Inside the lock, because a pre-lock reading is
# stale. Compilers are logged rather than awaited: another worktree's fat-LTO `rustc` runs for 10+
# minutes on one core. comparand-scaling.py refuses on its own while any compiler runs, so the
# caller waits for zero compilers before taking the lock for that suite.
settle() {
  local waited=0
  while :; do
    ctx="$(bash tools/cpu-context.sh 8-23)" || return 2
    load="$(printf '%s' "$ctx" | python3 -c 'import json,sys; print(json.load(sys.stdin)["load1"])')"
    busy="$(printf '%s' "$ctx" | python3 -c 'import json,sys; print(json.load(sys.stdin)["compilers"])')"
    python3 -c "import sys; sys.exit(0 if float('$load') < 8 else 1)" && break
    [ "$waited" -ge 600 ] && break
    sleep 15
    waited=$((waited + 15))
  done
  printf '%s\n' "{\"suite\":\"$suite\",\"settle_waited_s\":$waited,\"context\":$ctx}" >>"$OUT/suite-starts.jsonl"
  echo "suite $suite: settled after ${waited}s at load $load, compilers $busy"
}

case "$suite" in
identities)
  python3 "$here/identities.py" --bin "$bin" --exporter "$CARGO_TARGET_DIR/debug/examples/competitive_sweep" \
    >"$OUT/identities.json"
  ;;
mq10)
  settle
  references=research/comparand-scaling
  python3 tools/external/comparand-scaling.py \
    --binary "$CARGO_TARGET_DIR/debug/examples/competitive_sweep" --input-source "$(git rev-parse HEAD)" \
    --scratch "$OUT/mq10-scratch-${MQ10_TRY:-1}" --output "$OUT/mq10-try${MQ10_TRY:-1}.json.gz" --engines zeebra,msolve,grobx,groebner-rs \
    --fields 32003,2147483647 --rows mq-random-10 --workers 1,4,8,16 --repeats "${MQ10_REPS:-5}" --campaign-wall "${MQ10_WALL:-1800}" \
    --references "$references/references-v1.json.gz" "$references/singular-references-v1.json.gz" \
    "$references/singular-reference31-v1.json.gz"
  ;;
wide)
  settle
  status=0
  for pass in $(seq 1 "${REPS:-3}"); do
    for cell in "wide64 eco-12" "goldilocks mq-random-11"; do
      set -- $cell
      out="$OUT/wide-$1-$2-pass$pass.json.gz"
      ZEEBRA_AFFINITY=8 taskset -c 8 python3 tools/external/wide-corpus.py --binary "$bin/wide_corpus" \
        --scratch "$OUT/wide-scratch-$1-$2-$pass" --output "$out" --fields "$1" --rows "$2" \
        --engines grobx,groebner-rs || status=$?
      # The controller regenerates the published #738 board from this cohort; restore it.
      git checkout -- research/wide-corpus/BOARD.md
    done
  done
  exit "$status"
  ;;
walls | stages | ab831)
  settle
  python3 "$here/costmodel.py" --binary "$bin/m29_cost_model" --suite "$suite" --reps "${REPS:-3}" \
    --output "$OUT/$suite.jsonl"
  ;;
fl)
  # #828 cross-check: FL_BIN is m29_cost_model built against the parallel-FL branch's library.
  : "${FL_BIN:?m29_cost_model built at the #843 head}"
  settle
  python3 "$here/costmodel.py" --binary "$FL_BIN" --suite fl --reps "${REPS:-5}" \
    --output "$OUT/fl.jsonl"
  ;;
flstages)
  : "${FL_BIN:?m29_cost_model built at the #843 head}"
  settle
  python3 "$here/costmodel.py" --binary "$FL_BIN" --suite flstages --reps "${REPS:-3}" \
    --output "$OUT/flstages.jsonl"
  ;;
census)
  settle
  python3 "$here/costmodel.py" --binary "$bin/m29_cost_model_work" --suite census --reps 1 \
    --output "$OUT/census.jsonl"
  ;;
*)
  echo "unknown suite $suite" >&2
  exit 64
  ;;
esac
