#!/usr/bin/env bash
# #962 A/B session 2: dev extension (n = 9 + 21) on the imprecise rows plus a shipping-route
# control, and katsura-9 under --calls 20 with the shared #958 harness on both arms.
set -euo pipefail
cd /home/mfaulk/projects/zeebra/.claude/worktrees/agent-aa1286a847fd091a8
B=/buildcache/cargo-target/zeebra-961
export TMPDIR=$B/tmp ZEEBRA_MACHINE=5995wx
tools/bench-reserve.sh reserve 1,2
trap 'tools/bench-reserve.sh release || tools/bench-reserve.sh release --force' EXIT
tools/bench-reserve.sh run zb-962 8-23 python3 -u research/m32-final/campaign.py \
  --suite dev --bins $B/bin --reps 21 --first-rep 9 \
  --rows gf32003/mq-random-10 m31/mq-random-10 goldilocks/katsura-11 wide64/katsura-11 wide64/cyclic-7 \
  --arms en:1 men:1 --output $B/ab/dev.jsonl
tools/bench-reserve.sh run zb-962 8-23 python3 -u research/m32-final/campaign.py \
  --suite small --bins $B/binh --rows wide64/katsura-9 --arms en:1 men:1 --output $B/ab/small.jsonl
echo AB-DONE
