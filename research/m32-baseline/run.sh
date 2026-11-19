#!/usr/bin/env bash
# One #939 measurement session: reserve CCDs 1-2 (unless another session already holds them), run
# each named suite under its own `bench-reserve run` (benchlock, CPUs 8-23), release on any exit.
#
#   setsid -w research/m32-baseline/run.sh OUTDIR admission|walls|split|small|rs ...
#
# Every suite but `rs` is a campaign.py suite. `rs` (#935) runs groebner-rs through the wide
# controller at 1/4/8/16 workers on the four wide rows, REPS passes (default 9), the worker order
# rotated per pass, with the driver reporting per-thread CPU ticks.
set -euo pipefail
out="${1:?output directory}"
shift
cd "$(dirname "$0")/../.."
BINS="${BINS:-/buildcache/cargo-target/zeebra-939/bin}"
TAG=zb-939

rc=0
tools/bench-reserve.sh status >/dev/null || rc=$?
case $rc in
  0) owned=0; echo "reservation already held by another session; not releasing it" >&2 ;;
  1) tools/bench-reserve.sh reserve; owned=1 ;;
  *) echo "bench-reserve status failed (rc=$rc)" >&2; exit 2 ;;
esac
release() { if [ "$owned" = 1 ]; then tools/bench-reserve.sh release || tools/bench-reserve.sh release --force; fi; }
trap release EXIT

rs_sweep() {
  local ws=(1 4 8 16) pass k w cell cpus
  for pass in $(seq 1 "${REPS:-9}"); do
    for k in 0 1 2 3; do
      w=${ws[$(((k + pass) % 4))]}
      cpus=$(seq -s, 8 $((7 + w)))
      for cell in wide64:eco-12 goldilocks:mq-random-11 wide64:katsura-11 wide64:cyclic-7; do
        set -- ${cell/:/ }
        ZEEBRA_AFFINITY=$cpus ZEEBRA_RESEARCH_THREAD_TICKS=1 ZEEBRA_GROEBNER_RS_DRIVER="$BINS/groebner-rs-driver" \
          taskset -c "$cpus" python3 tools/external/wide-corpus.py --binary "$BINS/base/wide_corpus" \
          --scratch "$out/rs-scratch-$1-$2-w$w-$pass" --output "$out/rs-$1-$2-w$w-pass$pass.json.gz" \
          --fields "$1" --rows "$2" --engines groebner-rs --workers "$w"
        # The controller regenerates the published #738 board from each cohort; restore it.
        git checkout -- research/wide-corpus/BOARD.md
      done
    done
  done
}

mkdir -p "$out"
status=0
for suite in "$@"; do
  echo "== $suite $(date -Is) load=$(cut -d' ' -f1 /proc/loadavg)" | tee -a "$out/session.log"
  if [ "$suite" = rs ]; then
    export -f rs_sweep
    export out BINS
    tools/bench-reserve.sh run "$TAG" 8-23 bash -c rs_sweep 2>&1 | tee -a "$out/session.log" || status=$?
    continue
  fi
  tools/bench-reserve.sh run "$TAG" 8-23 python3 -u research/m32-baseline/campaign.py \
    --suite "$suite" --bins "$BINS" --output "$out/$suite.jsonl" 2>&1 | tee -a "$out/session.log" || status=$?
done
exit "$status"
