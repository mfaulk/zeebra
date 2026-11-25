#!/usr/bin/env bash
# #1105 telemetry-overhead A/A session: waits for the machine to be released, takes CCDs 1-2,
# runs aa.py under bench-reserve run (announced in benchlock.log), and releases.
# Usage: run.sh <repo> <sig_f4_study> <outdir> [pairs]
set -uo pipefail
REPO="$1" BIN="$2" OUT="$3" PAIRS="${4:-9}"
R="$REPO/tools/bench-reserve.sh"
mkdir -p "$OUT"
log() { printf '%s %s\n' "$(date --iso-8601=seconds)" "$*" | tee -a "$OUT/events.log"; }
Z="/sys/fs/cgroup/user.slice/user-$(id -u).slice/user@$(id -u).service/zbbench.slice"
until "$R" status >/dev/null; [ $? -eq 1 ] && [ "$(cat "$Z"/*/cgroup.procs 2>/dev/null | wc -l)" -eq 0 ]; do sleep 20; done
log "released; reserving load=$(cut -d' ' -f1 /proc/loadavg)"
"$R" reserve 1,2 >>"$OUT/events.log" 2>&1 || { log "reserve failed"; exit 2; }
sha256sum "$BIN" >"$OUT/binary.sha256"
TMPDIR=/buildcache/cargo-target/zeebra-1105/tmp "$R" run "#1105-telemetry-aa" 8-23 \
  python3 -I "$REPO/research/bench-telemetry-overhead/aa.py" "$REPO" "$BIN" "$OUT/attempts.jsonl" "$PAIRS" \
  >"$OUT/aa.log" 2>&1
log "aa rc=$?"
"$R" release >>"$OUT/events.log" 2>&1; log "release rc=$?"
