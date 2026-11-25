#!/usr/bin/env bash
# #1136: every derived record (derive.py) under conventional F4 and the signature engine, one
# worker, five solves per process; one JSON line per cell into results.jsonl.gz.
#
#   cargo build --release --features research-sigf4-usage --example sig_f4_study
#   research/1136-hairer2-attribution/run.sh [path/to/sig_f4_study]
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
bin="${1:-${CARGO_TARGET_DIR:-target}/release/examples/sig_f4_study}"
catalog="$here/derived.json"
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT
ids="$(python3 -c 'import json,sys; print(" ".join(r["id"] for r in json.load(open(sys.argv[1]))))' "$catalog")"
for id in $ids; do
  for engine in f4 sigf4; do
    "$bin" --catalog "$catalog" --field m31 --name "$id" --engine "$engine" \
      --workers 1 --repeat 5 --wall-s 300 >>"$tmp"
  done
done
gzip -n -9 <"$tmp" >"$here/results.jsonl.gz"
