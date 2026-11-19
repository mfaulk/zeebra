#!/usr/bin/env bash
# One #906 measurement session: reserve CCDs 1-2 (unless another session already holds them), run
# each named suite under its own `bench-reserve run` (benchlock, CPUs 8-23), release on any exit.
#
#   setsid -w research/m31-final/run.sh OUTDIR walls certify census certified wide mq10
#
# walls|certify|census|certified are campaign.py suites over $T/bin (README: Build). `wide` and
# `mq10` are #834's comparand suites (`research/m29-baseline/run.sh`), unchanged: grobx raw and
# groebner-rs on the four wide rows M30 ran, nine passes; msolve, grobx, groebner-rs and Zeebra's
# driver on MQ10 at 1/4/8/16 workers, nine repeats. `mq10` stops with 75 while any compiler runs
# anywhere on the machine; it waits (bounded) for none first and keeps every window.
set -euo pipefail
out="${1:?output directory}"
shift
cd "$(dirname "$0")/../.."
T="${T:-/buildcache/cargo-target/zeebra-906/target}"
TAG=zb-906

rc=0
tools/bench-reserve.sh status >/dev/null || rc=$?
case $rc in
  0) owned=0; echo "reservation already held by another session; not releasing it" >&2 ;;
  1) tools/bench-reserve.sh reserve; owned=1 ;;
  *) echo "bench-reserve status failed (rc=$rc)" >&2; exit 2 ;;
esac
release() { if [ "$owned" = 1 ]; then tools/bench-reserve.sh release || tools/bench-reserve.sh release --force; fi; }
trap release EXIT

no_compilers() {
  local waited=0
  while pgrep -x 'cargo|rustc|clippy-driver|cc1|rust-lld|mold' >/dev/null; do
    [ "$waited" -ge "${COMPILER_WAIT:-1800}" ] && return 1
    sleep 20
    waited=$((waited + 20))
  done
}

mkdir -p "$out"
status=0
for suite in "$@"; do
  echo "== $suite $(date -Is) load=$(cut -d' ' -f1 /proc/loadavg)" | tee -a "$out/session.log"
  case "$suite" in
  walls | certify | census | certified)
    tools/bench-reserve.sh run "$TAG" 8-23 python3 -u research/m31-final/campaign.py \
      --suite "$suite" --bins "$T/bin" --output "$out/$suite.jsonl" 2>&1 | tee -a "$out/session.log" || status=$?
    ;;
  wide)
    tools/bench-reserve.sh run "$TAG" 8-23 env CARGO_TARGET_DIR="$T" OUT="$out" REPS=9 \
      WIDE_CELLS="wide64:eco-12 goldilocks:mq-random-11 wide64:katsura-11 wide64:cyclic-7" \
      timeout --signal=INT --kill-after=60s 7200 bash research/m29-baseline/run.sh wide \
      2>&1 | tee -a "$out/session.log" || status=$?
    ;;
  mq10)
    try="${MQ10_TRY:-1}"
    no_compilers || echo "compilers still running after the wait; the window will likely stop" | tee -a "$out/session.log"
    tools/bench-reserve.sh run "$TAG" 8-23 env CARGO_TARGET_DIR="$T" OUT="$out" MQ10_REPS=9 MQ10_WALL=3600 \
      MQ10_TRY="$try" timeout --signal=INT --kill-after=60s 5400 bash research/m29-baseline/run.sh mq10 \
      2>&1 | tee -a "$out/session.log" || status=$?
    ;;
  *) echo "unknown suite $suite" >&2; exit 64 ;;
  esac
done
exit "$status"
