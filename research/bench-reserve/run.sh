#!/usr/bin/env bash
# #848 calibration (walls). Needs `tools/bench-reserve.sh reserve` (CCDs 1-2) and m29_cost_model in
# $CARGO_TARGET_DIR/bin; the build loads use their own target dirs under /buildcache.
#
#   OUT=/buildcache/cargo-target/zeebra-848/cal tools/benchlock.sh zb-848-cal \
#     timeout --signal=INT --kill-after=60s 3600 bash research/bench-reserve/run.sh
# #848 calibration: one exclusive benchlock window; arms A1 (reserved, idle), B (reserved, builds),
# D (reserved, DRAM hogs), C (builds, fence released), A2 (reserved, idle again).
set -uo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
HERE="$REPO/research/bench-reserve"
BIN="${BIN:-${CARGO_TARGET_DIR:?}/bin/m29_cost_model}"
S="${OUT:?output directory}"
mkdir -p "$S"
OUT=$S/walls.jsonl
REPS=${REPS:-7}
cd "$REPO" || exit 2
PIDS=()

note() { echo "$(date +%T) $*" | tee -a "$S/events.log"; }
drv() {
  note "arm $1 start load=$(cut -d' ' -f1 /proc/loadavg)"
  systemd-run --user --scope --quiet --collect --slice=zbbench.slice -p AllowedCPUs=8-23,72-87 -- \
    python3 -I "$HERE/driver.py" "$REPO" "$BIN" "$1" "$REPS" "$OUT"
  local rc=$?
  note "arm $1 end load=$(cut -d' ' -f1 /proc/loadavg) rc=$rc"
  [ "$rc" -eq 0 ] || exit 2
}
start_builds() {
  local i
  for i in 1 2 3; do
    setsid bash -c "L=/buildcache/cargo-target/zeebra-848-load$i; mkdir -p \$L/tmp
      export RUSTC_WRAPPER='' CARGO_TARGET_DIR=\$L TMPDIR=\$L/tmp CARGO_INCREMENTAL=0
      while :; do cargo clean -q >/dev/null 2>&1
        cargo build -q -j32 --features external-runners --examples --tests >/dev/null 2>&1; done" &
    PIDS+=($!)
  done
}
start_hogs() {
  local i
  for i in $(seq 16); do setsid python3 -I "$HERE/memhog.py" 900 & PIDS+=($!); done
}
stop_load() {
  local p
  for p in "${PIDS[@]}"; do kill -TERM -- "-$p" 2>/dev/null; done
  wait 2>/dev/null
  PIDS=()
}
trap stop_load EXIT
settle() { # wait until no compiler is running and load has decayed below 4, at most 600 s
  local i
  for i in $(seq 120); do
    if ! pgrep -x -u "$(id -u)" 'rustc|cargo|ld|rust-lld' >/dev/null && awk '{exit !($1 < 4)}' /proc/loadavg; then return 0; fi
    sleep 5
  done
}

tools/bench-reserve.sh status || tools/bench-reserve.sh reserve || exit 2
drv A1

start_builds; note "builds started"; sleep 90
drv B

stop_load; settle
start_hogs; note "hogs started"; sleep 10
drv D
stop_load; settle

start_builds; sleep 30
tools/bench-reserve.sh release; note "fence released"
sleep 60
drv C

stop_load; settle
tools/bench-reserve.sh reserve
drv A2
note "done"
