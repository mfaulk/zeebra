#!/usr/bin/env bash
# The second cohort of research/wide-corpus/current-821/run.sh, relaunched alone with its exact
# command line after the first cohort's end-of-run BOARD.md regeneration dirtied the tree.
set -u
cd /home/mfaulk/projects/zeebra/.claude/worktrees/curious-scribbling-lovelace || exit # `|| exit` added after the run
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-821
. tools/external/env.sh
ZEEBRA_MACHINE="$(hostname)"
export ZEEBRA_MACHINE TMPDIR="$CARGO_TARGET_DIR/tmp"
out="$CARGO_TARGET_DIR/workers-16.json.gz"
ZEEBRA_AFFINITY=2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17 timeout --signal=INT --kill-after=60s 7200 \
    taskset -c 2-17 python3 tools/external/wide-corpus.py --binary "$CARGO_TARGET_DIR/bin/wide_corpus" \
    --scratch "$CARGO_TARGET_DIR/campaign-16" --output "$out" --engines zeebra --workers 16
status=$?
python3 tools/external/wide-corpus.py --pack "$out" --output "$out"
exit "$status"
