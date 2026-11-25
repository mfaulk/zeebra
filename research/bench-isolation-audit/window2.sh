#!/usr/bin/env bash
# #1104 reservation window 2: what `release` gives back to tasks whose masks `reserve` narrowed.
# Usage: window2.sh <repo> <outdir>     (needs `bench-reserve.sh status` = released)
set -uo pipefail
REPO="$1" OUT="$2"
R="$REPO/tools/bench-reserve.sh"
mkdir -p "$OUT"
log() { printf '%s %s\n' "$(date --iso-8601=seconds)" "$*" | tee -a "$OUT/events.log"; }
aff() { # label pid
  printf '%s allowed=%s\n' "$1" "$(awk '/^Cpus_allowed_list/{print $2}' /proc/"$2"/status 2>/dev/null)"
}
snap() {
  {
    aff P_WIDE "$P_WIDE"; aff P_DISJ8 "$P_DISJ"; aff P_STRADDLE "$P_STRADDLE"; aff P_PLAIN "$P_PLAIN"
    aff P_SCOPE8 "$P_SCOPE8"; aff P_SETDURING "$P_SETDURING"
    "$R" status
  } >"$OUT/transition-$1.txt" 2>&1
}

"$R" status >/dev/null; [ $? -eq 1 ] || { echo "window2: not released; refusing" >&2; exit 2; }
log "window2 start load=$(cut -d' ' -f1 /proc/loadavg)"
taskset -c 0-127 sleep 600 & P_WIDE=$!
taskset -c 8 sleep 600 & P_DISJ=$!
taskset -c 0,8 sleep 600 & P_STRADDLE=$!
sleep 600 & P_PLAIN=$!
systemd-run --user --scope --quiet --unit=zb1104-w2-pin8 -p AllowedCPUs=8 -- sleep 600 & P_SCOPE8=$!
sleep 600 & P_SETDURING=$!
sleep 2
snap 0-pre
log reserve
"$R" reserve 1,2 >"$OUT/reserve.txt" 2>&1 || { log "reserve failed"; kill "$P_WIDE" "$P_DISJ" "$P_STRADDLE" "$P_PLAIN" "$P_SCOPE8" "$P_SETDURING"; exit 2; }
sleep 2
# A mask set while reserved: does the request survive the release, or the narrowed result?
taskset -cp 0-127 "$P_SETDURING" >"$OUT/setduring.txt" 2>&1
snap 1-reserved
log release
"$R" release >"$OUT/release.txt" 2>&1; log "release rc=$?"
sleep 2
snap 2-released
kill "$P_WIDE" "$P_DISJ" "$P_STRADDLE" "$P_PLAIN" "$P_SCOPE8" "$P_SETDURING" 2>/dev/null
log "window2 end"
