#!/usr/bin/env bash
# Interleaved fresh-process A/B: #777 before/after on #777's instances, main/branch on #794's sweep set.
set -euo pipefail
T=/buildcache/cargo-target/zeebra-794
OUT=$1
: > "$OUT"
for round in 1 2 3 4 5; do
  if (( round % 2 )); then pair1=(before after); pair2=(main branch); else pair1=(after before); pair2=(branch main); fi
  for arm in "${pair1[@]}"; do
    "$T/ab-target-$arm/release/examples/gf2_ab" 3 | sed "s/^/$round\t$arm\t/" >> "$OUT"
  done
  for arm in "${pair2[@]}"; do
    "$T/ab-target-$arm/release/examples/gf2_ab" 3 sweep | sed "s/^/$round\t$arm\t/" >> "$OUT"
  done
done
