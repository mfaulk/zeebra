#!/usr/bin/env bash
# One #941 Gate Q session: reserve CCDs 1-2 only if nobody holds them, run each named suite under
# its own `bench-reserve run` (benchlock, CPUs 8-23), and release on any exit if this session
# reserved. Inside another session's reservation the suites queue behind its benchlock.
#
#   setsid -w research/m32-qualification/run.sh OUTDIR dev small
#   CAMPAIGN_ARGS="--reps 12 --first-rep 9 --rows R... --arms A..." run.sh OUTDIR dev   # §10.3 extension
#
# BINS/{head,m31}/sig_f4_study are built from `git archive`s of the head and reference commits into
# separate CARGO_TARGET_DIRs (release, fat LTO, one codegen unit, x86-64-v3, --features research-sigf4).
# The `check` suite's groebner-rs arm runs $GROEBNER_RS (M30-0's driver, 81dc5c4c) and its Singular
# arm the system Singular.
set -euo pipefail
out="${1:?output directory}"
shift
cd "$(dirname "$0")/../.."
BINS="${BINS:-/buildcache/cargo-target/zeebra-941/bin}"
export ZEEBRA_GROEBNER_RS_DRIVER="${GROEBNER_RS:-$BINS/groebner-rs-driver}"
export TMPDIR="${TMPDIR:-/buildcache/cargo-target/zeebra-941/tmp}"
TAG=zb-941

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
  tools/bench-reserve.sh run "$TAG" 8-23 python3 -u research/m32-qualification/campaign.py \
    --suite "$suite" --bins "$BINS" --output "$out/$suite.jsonl" ${CAMPAIGN_ARGS:-} 2>&1 | tee -a "$out/session.log" || status=$?
done
exit "$status"
