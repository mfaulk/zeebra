#!/usr/bin/env bash
# Run a later session unattended: wait for the previous session to finish cleanly and for the start
# time, announce the heavy windows on #1107, run the session, then (optionally) the §8.3 throughput.
# Usage: chain.sh <prev-label> <label> <seed YYYYMMDD> <start "YYYY-MM-DD HH:MM"> [throughput]
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
PREV="$1" LABEL="$2" SEED="$3" START="$4" TP="${5:-}"
S=/buildcache/cargo-target/zeebra-1107/sessions
mkdir -p "$S/$LABEL"
log() { printf '%s %s\n' "$(date +%Y-%m-%dT%H:%M:%S%z)" "$*" >>"$S/$LABEL/events.log"; }
until grep -q "session $PREV complete" "$S/$PREV/events.log" 2>/dev/null; do
  if grep -qE 'STOP' "$S/$PREV/events.log" 2>/dev/null && ! pgrep -f "session.py session $PREV" >/dev/null; then
    log "chain: $PREV stopped without completing; $LABEL not started"; exit 2
  fi
  sleep 60
done
now=$(date +%s); at=$(date -d "$START" +%s)
[ "$at" -le "$now" ] || sleep $((at - now))
order="$(python3 -I -c "import sys; sys.path.insert(0, '$HERE'); import calib; print(', '.join(calib.session_order($SEED)))")"
gh issue comment 1107 --body "**Session ${LABEL} starting now** ($(date '+%Y-%m-%d %H:%M %Z'); ~7.3 h of reserved CCDs 1–2). Order (seed ${SEED}): ${order}. Heavy windows (W5, W4-32, W2) are six jobs, each ≤ 45 min. None starts while another agent's bench job is queued or holds a benchlock. Load runs on \`0-7,24-71,88-127\` only. Posted by the session chain, \`research/concurrent-calibration/chain.sh\`." >/dev/null \
  && log "chain: announced on #1107" || log "chain: announcement FAILED (gh); continuing"
python3 -I "$HERE/session.py" session "$LABEL" --seed "$SEED" >>"$S/$LABEL/driver.log" 2>&1
rc=$?
log "chain: session rc=$rc"
if [ "$rc" = 0 ] && [ -n "$TP" ]; then
  python3 -I "$HERE/throughput.py" "throughput-$LABEL" >>"$S/$LABEL/driver.log" 2>&1
  log "chain: throughput rc=$?"
fi
