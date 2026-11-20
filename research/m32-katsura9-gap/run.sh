#!/usr/bin/env bash
# One #958/#964 session: reserve CCDs 1-2 only if nobody holds them, run #958's katsura-9 suite
# (`gap`) and then #964's quiet re-read of #939's `ab` suite, each under its own `bench-reserve run`
# (benchlock, CPUs 8-23), and release on any exit if this session reserved.
#
#   setsid -w research/m32-katsura9-gap/run.sh OUTDIR gap ab
#   setsid -w research/m32-katsura9-gap/run.sh OUTDIR alloc
#
# BINS/<build>/sig_f4_study and ABBINS/{m32,split}/sig_f4_study: see README.md, "Reproduce".
set -euo pipefail
out="${1:?output directory}"
shift
cd "$(dirname "$0")/../.."
BINS="${BINS:-/buildcache/cargo-target/zeebra-958/bins}"
ABBINS="${ABBINS:-/buildcache/cargo-target/zeebra-958/bins-ab}"

rc=0
tools/bench-reserve.sh status >/dev/null || rc=$?
case $rc in
  0) owned=0; echo "reservation already held by another session; not releasing it" >&2 ;;
  1) tools/bench-reserve.sh reserve 1,2; owned=1 ;;
  *) echo "bench-reserve status failed (rc=$rc)" >&2; exit 2 ;;
esac
release() { if [ "$owned" = 1 ]; then tools/bench-reserve.sh release || tools/bench-reserve.sh release --force; fi; }
trap release EXIT

mkdir -p "$out"
status=0
for suite in "$@"; do
  echo "== $suite $(date -Is) load=$(cut -d' ' -f1 /proc/loadavg)" | tee -a "$out/session.log"
  case $suite in
    gap) tools/bench-reserve.sh run zb-958 8-23 python3 -u research/m32-katsura9-gap/campaign.py \
           --bins "$BINS" --output "$out/gap.jsonl" 2>&1 | tee -a "$out/session.log" || status=$? ;;
    alloc) tools/bench-reserve.sh run zb-958 8-23 python3 -u research/m32-katsura9-gap/campaign.py \
           --suite alloc --reps 11 --bins "$BINS" --output "$out/alloc.jsonl" 2>&1 | tee -a "$out/session.log" || status=$? ;;
    ab) tools/bench-reserve.sh run zb-964 8-23 python3 -u research/m32-baseline/campaign.py \
          --suite ab --bins "$ABBINS" --output "$out/ab.jsonl" 2>&1 | tee -a "$out/session.log" || status=$? ;;
    *) echo "unknown suite $suite" >&2; status=64 ;;
  esac
done
exit "$status"
