#!/usr/bin/env bash
# #1136 T1 (README): every development.json record (each eligible M34 development record and its
# homogenization) under the signature engine and F4, one worker, one solve, 60 s wall; one JSON
# line per cell into development.jsonl.gz. A cell that panics or is killed is recorded as such.
#
#   research/1136-hairer2-attribution/run-development.sh [path/to/sig_f4_study]
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
bin="${1:-${CARGO_TARGET_DIR:-target}/release/examples/sig_f4_study}"
catalog="$here/development.json"
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT
ids="$(python3 -c 'import json,sys; print(" ".join(r["id"] for r in json.load(open(sys.argv[1]))))' "$catalog")"
for id in $ids; do
  for engine in sigf4 f4; do
    if ! "$bin" --catalog "$catalog" --field m31 --name "$id" --engine "$engine" \
      --workers 1 --wall-s 60 >>"$tmp" 2>/dev/null; then
      printf '{"name":"%s","engine":"%s","status":"crashed"}\n' "$id" "$engine" >>"$tmp"
    fi
  done
done
gzip -n -9 <"$tmp" >"$here/development.jsonl.gz"
