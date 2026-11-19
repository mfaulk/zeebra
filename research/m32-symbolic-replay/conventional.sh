#!/usr/bin/env bash
# #933 deliverable 2: conventional F4's serial symbolic stage, stage clocks on, n per row, interleaved.
set -u
BIN="$1"; OUT="$2"; N="${3:-5}"
: > "$OUT"
for rep in $(seq 1 "$N"); do
  for t in mq10-32003 eco12-wide64; do
    timeout --signal=INT --kill-after=60s 300 taskset --cpu-list 8 "$BIN" --target "$t" --workers 1 --stages \
      | sed "s/^{/{\"rep\":$rep,\"target\":\"$t\",/" >> "$OUT" || echo "{\"rep\":$rep,\"target\":\"$t\",\"failed\":true}" >> "$OUT"
  done
done
