#!/usr/bin/env bash
#
# #1193 development figures: one JSON line per process, the 1-minute load average beside each.
#
#   research/1193-blocked-dense/run.sh <blocked_dense_study binary> <capture dir> <out.jsonl> [reps]
#
# Unpinned, on whatever machine runs it: these are development figures and decide nothing. Each
# rep runs every arm on every capture as its own process, with the arm order rotated per rep.
set -euo pipefail

if [[ $# -lt 3 ]]; then
  echo "usage: $0 <binary> <capture dir> <out.jsonl> [reps]" >&2
  exit 64
fi
bin=$1
dir=$2
out=$3
reps=${4:-3}
crossover=${CROSSOVER:-1024}

load() { uptime | sed -E 's/.*load averages?: ([0-9.]+).*/\1/'; }

emit() {
  local before after line
  before=$(load)
  line=$("$@")
  after=$(load)
  printf '%s\n' "${line%\}},\"load_before\":$before,\"load_after\":$after}" >> "$out"
}

captures=(
  "gf31__mq-dense-18-s18__b3.zmat 18 gf31"
  "gf32003__mq-dense-18-s18__b3.zmat 18 gf32003"
  "gf31__mq-dense-20-s20__b3.zmat 20 gf31"
  "gf32003__mq-dense-20-s20__b3.zmat 20 gf32003"
)

for rep in $(seq 1 "$reps"); do
  for capture in "${captures[@]}"; do
    read -r file vars field <<< "$capture"
    arms=(lane split)
    if (( rep % 2 == 0 )); then arms=(split lane); fi
    for arm in "${arms[@]}"; do
      if [[ $arm == lane ]]; then
        emit "$bin" lane "$dir/$file" "$vars" "$field"
      else
        emit "$bin" split "$dir/$file" "$vars" "$field" --winograd-from "$crossover" --leaf 128 --lane-residual
      fi
    done
  done
done
