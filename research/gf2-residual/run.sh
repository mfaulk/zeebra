#!/usr/bin/env bash
# #1077's replay: batches and solves, development and held-out sets, one process each.
#
#   research/gf2-residual/run.sh <binary> <out-dir> [reps]
#
# Records the commit, host and load before and after each run beside the output.
set -euo pipefail

binary="$1"
out="$2"
reps="${3:-5}"
mkdir -p "$out"
commit="$(git -C "$(dirname "${BASH_SOURCE[0]}")" rev-parse --short=8 HEAD)"
log="$out/provenance.txt"
{
  echo "commit=$commit"
  echo "host=$(uname -sm)"
  echo "reps=$reps"
} >"$log"
for mode in batches solve; do
  for set in dev heldout; do
    echo "START $mode $set $(date -u +%FT%TZ) load=$(uptime | sed 's/.*averages*: //')" >>"$log"
    "$binary" "$mode" "$set" "$reps" >"$out/$mode-$set.tsv"
    echo "END   $mode $set $(date -u +%FT%TZ) load=$(uptime | sed 's/.*averages*: //')" >>"$log"
  done
done
