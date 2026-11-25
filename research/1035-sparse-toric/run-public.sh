#!/usr/bin/env bash
# #1035: conventional F4 (shipping options, 1 worker) on the zero-dimensional eligible problems of
# the #1006 panel (public.json), all development records. One line of sig_f4_study output each.
#
#   cargo build --release --features research-sigf4 --example sig_f4_study
#   research/1035-sparse-toric/run-public.sh > research/1035-sparse-toric/public-f4.jsonl
set -euo pipefail
root="$(cd "$(dirname "$0")/../.." && pwd)"
bin="${CARGO_TARGET_DIR:-target}/release/examples/sig_f4_study"
for id in gen-phosphorylation-5 gen-phosphorylation-6 gen-phosphorylation-7 \
  gen-phosphorylation-2-nonzero gen-phosphorylation-4-nonzero gen-phosphorylation-6-nonzero; do
  "$bin" --catalog "$root/research/m34-public-corpus/catalog.json" --field m31 \
    --name "$id@p31" --engine f4 --workers 1 --wall-s "${ZB_WALL_S:-300}"
done
