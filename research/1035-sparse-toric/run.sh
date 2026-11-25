#!/usr/bin/env bash
# #1035: conventional F4's largest matrix on every paper.json shape the example instantiates, seeds
# 1–2, as given and perturbed (one added y-block product per generator). Four runs at a time:
# every figure is a count, so the outcome does not depend on contention.
#
#   cargo build --release --example sparse_toric_counts
#   research/1035-sparse-toric/run.sh > research/1035-sparse-toric/f4.jsonl
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
bin="${CARGO_TARGET_DIR:-target}/release/examples/sparse_toric_counts"
wall="${ZB_WALL_S:-120}"
python3 - "$here/paper.json" <<'EOF' |
import json, sys
supported = {6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 25, 27, 31}
for r in json.load(open(sys.argv[1])):
    if r["nx"] + r["ny"] in supported:
        for seed in (1, 2):
            for perturb in (0, 1):
                print(r["nx"], r["ny"], r["m"], r["dx"], perturb, seed)
EOF
  xargs -P4 -L1 sh -c '"$0" --nx "$1" --ny "$2" --m "$3" --dx "$4" --perturb "$5" --seed "$6" --wall-s '"$wall" "$bin"
