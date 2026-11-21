#!/usr/bin/env bash
# #962 1-worker A/B: head (bins/f3) vs main 31e334bd (bins/m31), m32-final campaign.py protocol.
set -euo pipefail
cd /home/mfaulk/projects/zeebra/.claude/worktrees/agent-aa1286a847fd091a8
B=/buildcache/cargo-target/zeebra-961
export TMPDIR=$B/tmp ZEEBRA_MACHINE=5995wx
tools/bench-reserve.sh reserve 1,2
trap 'tools/bench-reserve.sh release || tools/bench-reserve.sh release --force' EXIT
tools/bench-reserve.sh run zb-962 8-23 python3 -u research/m32-final/campaign.py \
  --suite dev --bins $B/bin --arms en:1 men:1 sg:1 msg:1 --output $B/ab/dev.jsonl
tools/bench-reserve.sh run zb-962 8-23 python3 -u research/m32-final/campaign.py \
  --suite small --bins $B/bin --rows wide64/katsura-9 --arms en:1 men:1 --output $B/ab/small.jsonl
echo AB-DONE
