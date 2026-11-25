#!/usr/bin/env bash
# #1104 reservation window 1: transitions, H-A1 inventories, H-A2 sibling sample under a build loop.
# Usage: window1.sh <repo> <outdir> <hbusy>
set -uo pipefail
REPO="$1" OUT="$2" HB="$3"
A="$REPO/tools/bench-isolation-audit.sh" R="$REPO/tools/bench-reserve.sh"
HOLD_S=1110 SAMPLE_S=1020
mkdir -p "$OUT"
log() { printf '%s %s\n' "$(date --iso-8601=seconds)" "$*" | tee -a "$OUT/events.log"; }
aff() { # label pid...
  local label="$1" p
  shift
  for p in "$@"; do
    printf '%s pid=%s allowed=%s last_cpu=%s cgroup=%s\n' "$label" "$p" \
      "$(awk '/^Cpus_allowed_list/{print $2}' /proc/"$p"/status 2>/dev/null)" \
      "$(awk '{print $39}' /proc/"$p"/stat 2>/dev/null)" "$(cut -c4- /proc/"$p"/cgroup 2>/dev/null)"
  done
}
snapshot_all() { # file-suffix
  {
    aff P_WIDE "$P_WIDE"; aff P_DISJ8 "$P_DISJ"; aff P_BUSY8 "$P_BUSY8"; aff P_PLAIN "$P_PLAIN"; aff P_SCOPE8 "$P_SCOPE8"
    "$R" status
    for s in app.slice background.slice session.slice zbbench.slice app.slice/zb1104-pin8.scope; do
      d="/sys/fs/cgroup/user.slice/user-$(id -u).slice/user@$(id -u).service/$s"
      printf '%s cpuset.cpus=%s effective=%s\n' "$s" "$(cat "$d/cpuset.cpus" 2>/dev/null)" "$(cat "$d/cpuset.cpus.effective" 2>/dev/null)"
    done
    systemctl --user show app.slice zbbench.slice zb1104-pin8.scope -p Id -p AllowedCPUs -p EffectiveCPUs 2>&1
    grep -E '^(se\.nr_migrations|nr_switches|nr_involuntary)' /proc/"$P_BUSY8"/sched 2>/dev/null | sed 's/^/P_BUSY8 /'
    awk '{print "P_BUSY8 utime+stime=" $14+$15}' /proc/"$P_BUSY8"/stat 2>/dev/null
  } >"$OUT/transition-$1.txt" 2>&1
}

log "window1 start load=$(cut -d' ' -f1 /proc/loadavg)"
"$R" status >"$OUT/status-before.txt" 2>&1
"$A" inventory 8-23,72-87 >"$OUT/inventory-unreserved.json"

# Transition subjects, started before the reservation, in this shell's app.slice scope.
taskset -c 0-127 sleep 1500 & P_WIDE=$!
taskset -c 8 sleep 1500 & P_DISJ=$!
taskset -c 8 "$HB" 1 1500 & P_BUSY8=$!
sleep 1500 & P_PLAIN=$!
systemd-run --user --scope --quiet --unit=zb1104-pin8 -p AllowedCPUs=8 -- sleep 1500 & P_SCOPE8=$!
sleep 2
snapshot_all 0-pre

log reserve
"$R" reserve 1,2 >"$OUT/reserve.txt" 2>&1 || { log "reserve failed rc=$?"; cat "$OUT/reserve.txt"; kill "$P_WIDE" "$P_DISJ" "$P_BUSY8" "$P_PLAIN" "$P_SCOPE8"; exit 2; }
sleep 3
snapshot_all 1-reserved

{
  echo "## taskset -c 8 true (new process onto a reserved CPU)"; taskset -c 8 true; echo "rc=$?"
  echo "## taskset -cp 8 <running app.slice pid>"; taskset -cp 8 "$P_PLAIN"; echo "rc=$?"
  echo "## taskset -cp 0-127 <running pid> (wider than cpuset)"; taskset -cp 0-127 "$P_PLAIN"; echo "rc=$?"; aff P_PLAIN "$P_PLAIN"
  echo "## taskset -cp 0,8 <running pid> (straddling)"; taskset -cp 0,8 "$P_PLAIN"; echo "rc=$?"; aff P_PLAIN "$P_PLAIN"
  echo "## new scope with AllowedCPUs=8 while reserved"
  systemd-run --user --scope --quiet -p AllowedCPUs=8 -- sh -c 'grep Cpus_allowed_list /proc/self/status; cut -c4- /proc/self/cgroup'; echo "rc=$?"
  echo "## systemd-run --user --slice=zb1104-escape.slice (a non-fenced user slice)"
  systemd-run --user --scope --quiet --slice=zb1104-escape.slice -- sh -c 'grep Cpus_allowed_list /proc/self/status; cut -c4- /proc/self/cgroup'; echo "rc=$?"
} >"$OUT/transition-taskset.txt" 2>&1
log "taskset probes done"

# The announced hold: a CCD-scoped benchlock over every reserved CPU, which also checks the zbbench path.
"$R" run "#1104-isolation-audit-window1" 8-23,72-87 bash -c \
  "cut -c4- /proc/self/cgroup; grep Cpus_allowed_list /proc/self/status; exec sleep $HOLD_S" >"$OUT/hold.txt" 2>&1 &
HOLD=$!
sleep 3

# Build loop on the rest CPUs (this shell is fenced to them), as #985's W2.
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-1104-w1 RUSTC_WRAPPER="" TMPDIR=/buildcache/cargo-target/zeebra-1104/tmp
setsid bash -c "cd '$REPO' && i=0; while :; do i=\$((i+1)); echo \"build \$i \$(date --iso-8601=seconds)\"; cargo clean >/dev/null 2>&1; cargo build -j48 --tests >/dev/null 2>&1; echo \"rc=\$?\"; done" >"$OUT/build-loop.log" 2>&1 &
BUILD=$!
log "build loop pgid=$BUILD"

"$A" sample 8-23,72-87 "$SAMPLE_S" 1 >"$OUT/sample-8-23,72-87.json" &
SAMPLER=$!
sleep 45
"$A" inventory 8-23,72-87 >"$OUT/inventory-reserved-1.json"; log "inventory 1"
sleep 440
"$A" inventory 8-23,72-87 >"$OUT/inventory-reserved-2.json"; log "inventory 2"
snapshot_all 2-reserved-mid
sleep 440
"$A" inventory 8-23,72-87 >"$OUT/inventory-reserved-3.json"; log "inventory 3"
wait "$SAMPLER"; log "sample done"
kill -- -"$BUILD" 2>/dev/null; log "build loop stopped"
snapshot_all 3-reserved-end
wait "$HOLD"; log "hold ended rc=$?"
"$R" release >"$OUT/release.txt" 2>&1; log "release rc=$?"
sleep 3
snapshot_all 4-released
kill "$P_WIDE" "$P_DISJ" "$P_BUSY8" "$P_PLAIN" "$P_SCOPE8" 2>/dev/null
"$R" status >"$OUT/status-after.txt" 2>&1
log "window1 end"
