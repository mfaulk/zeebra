#!/usr/bin/env bash
# #933 exploratory symbolic replay: n fresh processes per row, interleaved, inside the reservation.
set -u
BIN="$1"; OUT="$2"; N="${3:-5}"
: > "$OUT"
for rep in $(seq 1 "$N"); do
  for row in "wide64 eco-12" "gf32003 mq-random-10"; do
    set -- $row
    for w in 16 1; do
      extra=""; [ "$w" -gt 1 ] && extra="--claim"
      timeout --signal=INT --kill-after=60s 900 "$BIN" --field "$1" --name "$2" --engine sigf4 \
        --workers "$w" $extra --symbolic-replay \
        | sed "s/^{/{\"rep\":$rep,/" >> "$OUT" || echo "{\"rep\":$rep,\"field\":\"$1\",\"failed\":true}" >> "$OUT"
    done
  done
done
