#!/bin/bash
# #1033's deciding read: run the submitted jobs in order inside one CCD reservation, releasing it on
# any exit. `bench-job run` execs `bench-reserve run` itself (exclusive lock in publication mode),
# so it must not be wrapped again; a job that has already started is resumed instead.
#   ZEEBRA_BENCH_JOBS=... research/1033-dense-rebaseline/run-jobs.sh JOB...
set -u
cd "$(dirname "$0")/../.." || exit 2
: "${ZEEBRA_BENCH_JOBS:?set ZEEBRA_BENCH_JOBS}"
tools/bench-reserve.sh reserve || exit 2
trap 'tools/bench-reserve.sh release' EXIT
for job in "$@"; do
    echo "== $job $(date -u +%FT%TZ)"
    if [ -e "$ZEEBRA_BENCH_JOBS/$job/started" ]; then
        tools/bench-job resume "$job" --force-uncancel
    else
        tools/bench-job run "$job"
    fi
    rc=$?
    echo "== $job rc=$rc $(date -u +%FT%TZ)"
    [ "$rc" -eq 0 ] || exit "$rc"
done
