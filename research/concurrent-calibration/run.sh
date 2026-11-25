#!/usr/bin/env bash
# One (cohort, workload) job plus its background load (protocol §8.6). A whole session is
# `session.py session <label>`. Needs the CCD 1-2 reservation to be up (bench-job runs inside it).
set -euo pipefail
[ $# -eq 3 ] || { echo "usage: run.sh <calibration|held-out> <W0|W1|...|W5> <session-label>" >&2; exit 64; }
exec python3 -I "$(dirname "$0")/session.py" one "$1" "$2" "$3"
