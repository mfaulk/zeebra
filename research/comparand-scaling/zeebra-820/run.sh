#!/usr/bin/env bash
# #820: Zeebra's fresh-process cohort on the #739 grid, on the comparands' process-wall boundary.
#
#   OUT=/buildcache/cargo-target/zeebra-820/cohort \
#     tools/benchlock.sh zeebra-820 bash research/comparand-scaling/zeebra-820/run.sh [extra args]
#
# Needs: a clean committed tree; ZEEBRA_DRIVER (release `zeebra_driver` built at HEAD, copied out of
# the target dir); CARGO_TARGET_DIR holding the debug `competitive_sweep` input exporter from HEAD.
# Extra arguments are appended, so a smoke run can narrow --rows/--fields/--workers/--repeats.
set -eu
: "${ZEEBRA_DRIVER:?release zeebra_driver path}" "${CARGO_TARGET_DIR:?}" "${OUT:?output stem}"
. tools/external/env.sh
export ZEEBRA_MACHINE=5995wx TMPDIR="$CARGO_TARGET_DIR/tmp"
head="$(git rev-parse HEAD)"
references=research/comparand-scaling
exec python3 tools/external/comparand-scaling.py \
    --binary "$CARGO_TARGET_DIR/debug/examples/competitive_sweep" --input-source "$head" \
    --scratch "$OUT" --output "$OUT.json.gz" --engines zeebra \
    --fields 32003,2147483647,wide64,goldilocks \
    --rows katsura-4,mq-random-10,katsura-11,cyclic-7,katsura-9 \
    --workers 1,2,4,8,16,32 --repeats 3 --campaign-wall 2400 \
    --references "$references/references-v1.json.gz" "$references/singular-references-v1.json.gz" \
    "$references/singular-reference31-v1.json.gz" "$@"
