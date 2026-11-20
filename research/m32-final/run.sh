#!/usr/bin/env bash
# One #942 measurement session: reserve CCDs 1-2 only if nobody holds them, run each named suite
# under its own `bench-reserve run` (benchlock, CPUs 8-23), and release on any exit if this session
# reserved. Inside another session's reservation the suites queue behind its benchlock.
#
#   setsid -w research/m32-final/run.sh OUTDIR dev small held certify
#   setsid -w research/m32-final/run.sh OUTDIR rs wide mq10 certified
#   CAMPAIGN_ARGS="--reps 12 --first-rep 9 --rows R... --arms A..." run.sh OUTDIR dev   # §10.3 extension
#
# dev|small|held|certify are campaign.py suites over $BINS/{f3,m31}/sig_f4_study. The comparand
# suites reuse earlier controllers unchanged, with $T/bin holding F3's wide_corpus and zeebra_driver,
# M30-0's grobx-driver and groebner-rs-driver, and $T/debug/examples/competitive_sweep:
#   rs         groebner-rs at its best measured worker count (8, #935) on the four wide rows,
#              through the wide controller, REPS passes (default 9); #939's `rs` sweep at w = 8 only
#   wide       research/m29-baseline/run.sh wide: grobx raw randomized and groebner-rs, one worker
#   mq10       research/m29-baseline/run.sh mq10: msolve exact, grobx raw, groebner-rs and Zeebra's
#              driver on MQ10 at 1/4/8/16 workers; stops with 75 while any compiler runs
#   certified  research/m31-final/campaign.py --suite certified: grobx certified, one worker, n = 9
set -euo pipefail
out="${1:?output directory}"
shift
cd "$(dirname "$0")/../.."
B="${B:-/buildcache/cargo-target/zeebra-942}"
BINS="${BINS:-$B/bin}"
T="${T:-$B/target-f3}"
export TMPDIR="${TMPDIR:-$B/tmp}"
TAG=zb-942

rc=0
tools/bench-reserve.sh status >/dev/null || rc=$?
case $rc in
  0) owned=0; echo "reservation already held by another session; not releasing it" >&2 ;;
  1) tools/bench-reserve.sh reserve 1,2; owned=1 ;;
  *) echo "bench-reserve status failed (rc=$rc)" >&2; exit 2 ;;
esac
release() { if [ "$owned" = 1 ]; then tools/bench-reserve.sh release || tools/bench-reserve.sh release --force; fi; }
trap release EXIT

rs_sweep() {
  local pass cell cpus
  cpus=$(seq -s, 8 15)
  for pass in $(seq 1 "${REPS:-9}"); do
    for cell in wide64:eco-12 goldilocks:mq-random-11 wide64:katsura-11 wide64:cyclic-7; do
      set -- ${cell/:/ }
      ZEEBRA_AFFINITY=$cpus ZEEBRA_GROEBNER_RS_DRIVER="$T/bin/groebner-rs-driver" \
        taskset -c "$cpus" python3 tools/external/wide-corpus.py --binary "$T/bin/wide_corpus" \
        --scratch "$out/rs-scratch-$1-$2-w8-$pass" --output "$out/rs-$1-$2-w8-pass$pass.json.gz" \
        --fields "$1" --rows "$2" --engines groebner-rs --workers 8
      # The controller regenerates the published #738 board from each cohort; restore it.
      git checkout -- research/wide-corpus/BOARD.md
    done
  done
}

mkdir -p "$out"
status=0
for suite in "$@"; do
  echo "== $suite $(date -Is) load=$(cut -d' ' -f1 /proc/loadavg)" | tee -a "$out/session.log"
  bash tools/cpu-context.sh 8-23 | sed "s/^/{\"suite\":\"$suite\",\"context\":/; s/$/}/" >>"$out/suite-starts.jsonl" || true
  case "$suite" in
  dev | small | held | certify)
    # shellcheck disable=SC2086
    tools/bench-reserve.sh run "$TAG" 8-23 python3 -u research/m32-final/campaign.py \
      --suite "$suite" --bins "$BINS" --output "$out/$suite.jsonl" ${CAMPAIGN_ARGS:-} 2>&1 | tee -a "$out/session.log" || status=$?
    ;;
  rs)
    export -f rs_sweep
    export out T
    tools/bench-reserve.sh run "$TAG" 8-23 bash -c rs_sweep 2>&1 | tee -a "$out/session.log" || status=$?
    ;;
  wide)
    tools/bench-reserve.sh run "$TAG" 8-23 env CARGO_TARGET_DIR="$T" OUT="$out" REPS=9 \
      WIDE_CELLS="wide64:eco-12 goldilocks:mq-random-11 wide64:katsura-11 wide64:cyclic-7" \
      timeout --signal=INT --kill-after=60s 7200 bash research/m29-baseline/run.sh wide \
      2>&1 | tee -a "$out/session.log" || status=$?
    ;;
  mq10)
    tools/bench-reserve.sh run "$TAG" 8-23 env CARGO_TARGET_DIR="$T" OUT="$out" MQ10_REPS=9 MQ10_WALL=3600 \
      MQ10_TRY="${MQ10_TRY:-1}" timeout --signal=INT --kill-after=60s 5400 bash research/m29-baseline/run.sh mq10 \
      2>&1 | tee -a "$out/session.log" || status=$?
    ;;
  certified)
    tools/bench-reserve.sh run "$TAG" 8-23 python3 -u research/m31-final/campaign.py \
      --suite certified --bins "$T/bin" --output "$out/certified.jsonl" 2>&1 | tee -a "$out/session.log" || status=$?
    ;;
  *) echo "unknown suite $suite" >&2; exit 64 ;;
  esac
done
exit "$status"
