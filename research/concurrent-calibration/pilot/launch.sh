#!/usr/bin/env bash
# Run the #1106 pilot once both binaries exist at C.
# Usage: launch.sh <repo> <workdir> <out> [build-done-marker]
set -uo pipefail
REPO="$1" W="$2" OUT="$3" MARK="${4:-}"
if [ -n "$MARK" ]; then until [ -s "$MARK" ]; do sleep 15; done; fi
for b in sig_f4_study m29_cost_model; do
  [ -x "$W/target/release/examples/$b" ] || { echo "launch: $b missing" >&2; exit 2; }
done
mkdir -p "$W/jobs" "$W/tmp"
python3 -I "$REPO/research/concurrent-calibration/pilot/pilot.py" "$REPO" "$W" "$OUT"
