#!/usr/bin/env bash
# One #1012 timed session: wait until no reservation is up, reserve CCDs 1-2, drive one pass of the
# matrix (and the feature costs after pass 1), release. The reservation is released on every exit.
#
#   research/m34-gate-h/session.sh <pass> <m34_matrix binary> [<feature_costs binary>]
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
pass=$1 matrix=$2 features=${3:-}
deadline=$((SECONDS + ${ZB1012_WAIT_S:-14400}))
while :; do
  rc=0; "$ROOT/tools/bench-reserve.sh" status >/dev/null 2>&1 || rc=$?
  if [ "$rc" -eq 1 ] && "$ROOT/tools/bench-reserve.sh" reserve; then
    break
  fi
  [ "$SECONDS" -lt "$deadline" ] || { echo "$(date -u +%FT%TZ) reservation never freed" >&2; exit 3; }
  sleep 60
done
trap '"$ROOT/tools/bench-reserve.sh" release' EXIT
echo "$(date -u +%FT%TZ) reserved; pass $pass"
python3 "$ROOT/research/m34-gate-h/campaign.py" drive --pass "$pass" --binary "$matrix"
echo "$(date -u +%FT%TZ) drive rc=$?"
if [ -n "$features" ]; then
  "$ROOT/tools/bench-reserve.sh" run zb-1012-features 8 \
    python3 "$ROOT/research/m34-gate-h/campaign.py" features --binary "$features"
  echo "$(date -u +%FT%TZ) features rc=$?"
fi
