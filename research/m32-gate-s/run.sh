#!/usr/bin/env bash
# One #940 Gate S session: reserve CCDs 1-2 (unless another session already holds them), run each
# named campaign.py suite under its own `bench-reserve run` (benchlock, CPUs 8-23), release on any
# exit.
#
#   BINS=/buildcache/cargo-target/zeebra-940/bin setsid -w research/m32-gate-s/run.sh OUTDIR gate mq10 small curve
set -euo pipefail
out="${1:?output directory}"
shift
cd "$(dirname "$0")/../.."
BINS="${BINS:-/buildcache/cargo-target/zeebra-940/bin}"
TAG=zb-940

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
# Run every arm from a tmpfs copy. A binary's text counts toward peak RSS, and on XFS how many of
# its pages a run maps depends on the page-cache folios the file happens to have (a freshly linked
# binary measured 2 MB above a copy of itself), so arms staged alike are compared alike.
stage="$(mktemp -d /dev/shm/zb-940-bins.XXXXXX)"
trap 'release; rm -rf "$stage"' EXIT
cp -r "$BINS"/. "$stage"/
(cd "$stage" && sha256sum ./*/sig_f4_study ./*/m29_cost_model) | tee "$out/bins.sha256"
BINS="$stage"
status=0
for suite in "$@"; do
  echo "== $suite $(date -Is) load=$(cut -d' ' -f1 /proc/loadavg)" | tee -a "$out/session.log"
  tools/bench-reserve.sh run "$TAG" 8-23 python3 -u research/m32-gate-s/campaign.py \
    --suite "$suite" --bins "$BINS" --output "$out/$suite.jsonl" 2>&1 | tee -a "$out/session.log" || status=$?
done
exit "$status"
