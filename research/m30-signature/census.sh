#!/usr/bin/env bash
# One serial --discovery record per target from one cost-model binary: the C1 zero-row census and
# #223's pair-row fraction, read from the same run (plan §6.1 reconciliation).
#   tools/bench-reserve.sh run zb-716 8 research/m30-signature/census.sh <binary> <out.jsonl>
set -euo pipefail
binary=$1
out=$2
: > "$out"
for target in katsura5-m31 cyclic5-m31 eco12-wide64 mq11-goldilocks; do
  timeout --signal=INT --kill-after=60s 900s \
    "$binary" --target "$target" --workers 1 --discovery --wall-s 900 >> "$out"
done
