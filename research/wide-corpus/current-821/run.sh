#!/usr/bin/env bash
# #821: Zeebra's hard wide-field ladder at current main, as a serial and a 16-worker cohort.
#
#   tools/benchlock.sh wide-821 bash research/wide-corpus/current-821/run.sh
#
# Needs a clean committed tree and CARGO_TARGET_DIR holding the release `wide_corpus` built at HEAD.
# Zeebra only: the comparand rows are the retained #738 cohort, unchanged binaries, not re-run.
set -u
: "${CARGO_TARGET_DIR:?}"
. tools/external/env.sh
ZEEBRA_MACHINE="$(hostname)"
export ZEEBRA_MACHINE TMPDIR="$CARGO_TARGET_DIR/tmp"
binary="$CARGO_TARGET_DIR/bin/wide_corpus"
status=0
for cohort in "1 2" "16 2-17"; do
    set -- $cohort
    affinity="$(python3 -c "import sys; a, b = (sys.argv[1] + '-' + sys.argv[1]).split('-')[:2]; print(','.join(map(str, range(int(a), int(b) + 1))))" "$2")"
    out="$CARGO_TARGET_DIR/workers-$1.json.gz"
    ZEEBRA_AFFINITY="$affinity" timeout --signal=INT --kill-after=60s 7200 \
        taskset -c "$2" python3 tools/external/wide-corpus.py --binary "$binary" \
        --scratch "$CARGO_TARGET_DIR/campaign-$1" --output "$out" \
        --engines zeebra --workers "$1" || status=$?
    python3 tools/external/wide-corpus.py --pack "$out" --output "$out" || status=$?
    # The controller rewrites the published #738 BOARD.md from this cohort when it finishes; restore
    # it, or the next cohort refuses the dirty tree (as the first launch's 16-worker cohort did).
    git checkout -- research/wide-corpus/BOARD.md
done
exit "$status"
