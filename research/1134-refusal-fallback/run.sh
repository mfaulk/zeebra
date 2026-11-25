#!/usr/bin/env bash
# #1134: adaptive, fallback and sig at 1 and 8 workers, 120 s wall, on the development rows and the
# out-of-sample candidates (README); one JSON line per cell into cells.jsonl, with its row set.
#
#   research/1134-refusal-fallback/run.sh [path/to/m34_matrix]
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
bin="${1:-${CARGO_TARGET_DIR:-target}/release/examples/m34_matrix}"
out="$here/cells.jsonl"
: >"$out"

cell() { # set catalog id
  local set="$1" catalog="$2" id="$3" engine workers line
  for workers in 1 8; do
    for engine in adaptive fallback sig; do
      if line="$("$bin" --catalog "$catalog" --id "$id" --engine "$engine" \
        --workers "$workers" --wall-s 120 2>/dev/null)"; then
        printf '{"set":"%s",%s\n' "$set" "${line#\{}" >>"$out"
      else
        printf '{"set":"%s","id":"%s","engine":"%s","workers":%s,"status":"crashed"}\n' \
          "$set" "$id" "$engine" "$workers" >>"$out"
      fi
    done
  done
}

for id in sd-ellipsoid-m2 gen-chandrasekhar-h-13; do
  for field in p31 p64; do cell development "$root/research/m34-public-corpus/catalog.json" "$id@$field"; done
done
for field in p31 p64; do
  cell development "$root/research/m34-structural-corpus/catalog.json" "zb-col-grid-5x5@$field"
done
ids="$(python3 -c 'import json,sys; print(" ".join(r["id"] for r in json.load(open(sys.argv[1]))))' \
  "$here/candidates.json")"
for id in $ids; do cell out-of-sample "$here/candidates.json" "$id"; done
