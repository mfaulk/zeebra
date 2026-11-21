#!/usr/bin/env bash
set -euo pipefail
cd /home/mfaulk/projects/zeebra/.claude/worktrees/agent-aa1286a847fd091a8
B=/buildcache/cargo-target/zeebra-961
export TMPDIR=$B/tmp
tools/bench-reserve.sh reserve 1,2
trap 'tools/bench-reserve.sh release || tools/bench-reserve.sh release --force' EXIT
tools/bench-reserve.sh run zb-962 8-23 python3 -u $B/ab/variants.py 21 $B/ab/variants.jsonl
echo AB-DONE
