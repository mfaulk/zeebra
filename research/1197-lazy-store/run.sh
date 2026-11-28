#!/usr/bin/env bash
# #1197's census runs: one fresh process per (row, engine), one worker, untimed (counts only).
#
#   CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16 \
#     cargo build --release --features research-reuse --example reuse_census
#   research/1197-lazy-store/run.sh <binary> <out-dir>
#
# The counts are deterministic, so the build profile does not change them.
set -euo pipefail
bin="$1"
out="$2"
mkdir -p "$out"
rows=(
  dmq-n14-m25-gf31-s1 dmq-n14-m25-gf31-s2 dmq-n14-m25-gf32003-s1
  dmq-n16-m29-gf31-s1 dmq-n18-m32-gf31-s1
)
for row in "${rows[@]}"; do
  for engine in f4 sigf4; do
    "$bin" --row "$row" --engine "$engine" --census --wall-s 20000 >"$out/$row-$engine.json"
  done
done
cat "$out"/*.json | gzip -9 >"$out/runs.jsonl.gz"
