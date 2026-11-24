#!/usr/bin/env bash
# #1009's campaign: every catalog record in its own fresh process, one at a time, in catalog order.
# Usage: run.sh <feature_costs binary> <catalog.json> <out.jsonl> [wall-s]
set -euo pipefail
bin=$1
catalog=$2
out=$3
wall=${4:-60}

mapfile -t ids < <(python3 -c 'import json, sys; [print(r["id"]) for r in json.load(open(sys.argv[1]))]' "$catalog")
: >"$out"
for id in "${ids[@]}"; do
    line=$(timeout --signal=INT --kill-after=30s $((4 * wall + 60)) \
        "$bin" --catalog "$catalog" --id "$id" --wall-s "$wall") ||
        line="{\"id\":\"$id\",\"status\":\"failed: exit $?\"}"
    printf '%s\n' "$line" >>"$out"
done
