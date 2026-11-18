#!/usr/bin/env bash
# One #905 Gate C session: reserve CCDs 1-2 (unless another session holds them), run the named
# suites under `bench-reserve run` (benchlock, CPUs 8-23), and release on any exit.
#
#   setsid research/m31-sigf4-dispatch/run.sh OUTDIR BIN w16 w1 certify
#
# BIN is sig_f4_study built from a `git archive` of the evaluated commit into its own
# CARGO_TARGET_DIR (release, fat LTO, one codegen unit, x86-64-v3, --features research-sigf4).
set -euo pipefail
out="${1:?output directory}"; bin="${2:?binary}"
shift 2
cd "$(dirname "$0")/../.."

rc=0
tools/bench-reserve.sh status >/dev/null || rc=$?
case $rc in
  0) owned=0; echo "reservation already held by another session; not releasing it" >&2 ;;
  1) tools/bench-reserve.sh reserve; owned=1 ;;
  *) echo "bench-reserve status failed (rc=$rc)" >&2; exit 2 ;;
esac
release() { if [ "$owned" = 1 ]; then tools/bench-reserve.sh release || tools/bench-reserve.sh release --force; fi; }
trap release EXIT

mkdir -p "$out"
for suite in "$@"; do
  tools/bench-reserve.sh run zb-905 8-23 python3 -u research/m31-sigf4-dispatch/campaign.py \
    --suite "$suite" --bin "$bin" --output "$out/$suite.jsonl"
done
