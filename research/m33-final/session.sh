#!/usr/bin/env bash
# One #975 publication session: reserve CCDs 1-2, run the named bench-jobs in order, take the thread
# census for the first job's manifest, release. The reservation is released on every exit path.
#
#   research/m33-final/session.sh <track-label> <job-id> [<job-id>...]
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
: "${ZEEBRA_BENCH_JOBS:?set ZEEBRA_BENCH_JOBS}"
label=$1
shift
"$ROOT/tools/bench-reserve.sh" reserve || exit 2
trap '"$ROOT/tools/bench-reserve.sh" release' EXIT
for job in "$@"; do
  echo "$(date -u +%FT%TZ) run $job"
  "$ROOT/tools/bench-job" run "$job"
  echo "$(date -u +%FT%TZ) $job rc=$?"
done
[ "${ZB975_THREADS:-1}" = 1 ] || exit 0
echo "$(date -u +%FT%TZ) threads"
"$ROOT/tools/bench-reserve.sh" run "zb-975-threads-$label" 8-23 python3 "$ROOT/research/m33-final/campaign.py" \
  threads --manifest "$ZEEBRA_BENCH_JOBS/$1/manifest.json" --output "$ZEEBRA_BENCH_JOBS/threads-$label.jsonl"
echo "$(date -u +%FT%TZ) threads rc=$?"
