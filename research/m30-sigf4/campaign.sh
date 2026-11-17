#!/usr/bin/env bash
# #857's measured campaign. Build both binaries first; run each suite under tools/benchlock.sh.
#   BIN=.../sig_f4_study WORK_BIN=.../sig_f4_study_work OUT=dir \
#     tools/benchlock.sh zb-857 bash research/m30-sigf4/campaign.sh gate|controls|census
set -euo pipefail
: "${BIN:?}" "${OUT:?}"
here="$(dirname "$0")"
first="${FIRST:-24}"
case "${1:?suite}" in
  gate)
    python3 "$here/run.py" --bin "$BIN" --out "$OUT/gate.jsonl" --reps "${REPS:-9}" --first "$first" \
      --cap 900 --rows wide64/eco-12 goldilocks/katsura-11 --arms sigf4:1 f4:1 f4:16 ;;
  controls)
    python3 "$here/run.py" --bin "$BIN" --out "$OUT/controls.jsonl" --reps "${REPS:-5}" --first "$first" \
      --cap 900 --rows goldilocks/katsura-4 wide64/katsura-4 goldilocks/noon-7 goldilocks/cyclic-7 \
      goldilocks/mq-random-11 --arms sigf4:1 f4:1 f4:16 ;;
  census)
    : "${WORK_BIN:?}"
    for row in "wide64 eco-12" "goldilocks katsura-11" "goldilocks mq-random-11"; do
      set -- $row
      timeout --signal=INT --kill-after=60s 1800 taskset -c "$first" "$WORK_BIN" --field "$1" --name "$2" \
        --engine f4 --workers 1 --discovery --wall-s 1800 >> "$OUT/census.jsonl"
    done ;;
  *) echo "unknown suite $1" >&2; exit 2 ;;
esac
