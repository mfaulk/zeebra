#!/usr/bin/env bash
# #1194: the five rows under each module and rewrite order the engine can switch, one worker, one
# solve per process; one JSON line per cell into runs.jsonl.gz. Counts are deterministic, so one
# solve is the record; the clocks are for scale only.
#
#   cargo build --release --features research-sigf4-variants --example sig_f4_study
#   research/1194-signature-variants/run.sh [path/to/sig_f4_study] [wall seconds]
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
bin="${1:-${CARGO_TARGET_DIR:-target}/release/examples/sig_f4_study}"
wall="${2:-600}"
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

rows=(
  "--field wide64 --name eco-12"
  "--field wide64 --name katsura-11"
  "--field wide64 --name mq-random-11"
  "--field wide64 --name cyclic-7"
  "--field m31 --catalog $root/research/m34-public-corpus/catalog.json --name sd-hairer-2@p31"
)
cells=(
  "--module schreyer --rewrite ratio"
  "--module schreyer --rewrite newest"
  "--module dpot --rewrite ratio"
  "--module dpot --rewrite newest"
  "--module pot --rewrite ratio"
  "--module pot --rewrite newest"
  "--module pot --rewrite ratio --reverse"
)
for row in "${rows[@]}"; do
  # shellcheck disable=SC2086 # each entry is a list of flags
  "$bin" $row --engine f4 --workers 1 --wall-s "$wall" --digest-only >>"$tmp" || true
  for cell in "${cells[@]}"; do
    # shellcheck disable=SC2086
    "$bin" $row --engine sigf4 $cell --workers 1 --wall-s "$wall" --digest-only >>"$tmp" ||
      printf '{"row":"%s","cell":"%s","status":"process-failed"}\n' "$row" "$cell" >>"$tmp"
  done
done
gzip -n -9 <"$tmp" >"$here/runs.jsonl.gz"
