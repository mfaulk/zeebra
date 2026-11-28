#!/bin/bash
# #1240 laptop-stage paired campaign: the signature engine with default basis terms against
# `--id-terms`, one worker, the arms alternating which runs first. macOS: peak RSS from
# `/usr/bin/time -l` (bytes), since `peak_resident_bytes` reports nothing there.
#
#   BIN=target/release/examples/sig_f4_study campaign.sh OUT.jsonl REPS "label|args" ...
set -u
BIN=${BIN:?set BIN to a sig_f4_study binary}
OUT=$1
REPS=$2
shift 2
err=$(mktemp)
trap 'rm -f "$err"' EXIT
for row in "$@"; do
  label=${row%%|*}
  args=${row#*|}
  rep=1
  while [ "$rep" -le "$REPS" ]; do
    if [ $((rep % 2)) -eq 1 ]; then arms="off on"; else arms="on off"; fi
    for arm in $arms; do
      extra=""
      if [ "$arm" = on ]; then extra="--id-terms"; fi
      # shellcheck disable=SC2086
      json=$(/usr/bin/time -l "$BIN" $args --engine sigf4 --workers 1 --digest-only $extra 2>"$err")
      rss=$(awk '/maximum resident set size/ {print $1}' "$err")
      echo "{\"label\":\"$label\",\"arm\":\"$arm\",\"rep\":$rep,\"max_rss\":$rss,\"run\":$json}" >>"$OUT"
      echo "$label $arm $rep rss=$rss"
    done
    rep=$((rep + 1))
  done
done
