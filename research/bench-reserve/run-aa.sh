#!/usr/bin/env bash
# #848 calibration (aa). Needs `tools/bench-reserve.sh reserve` (CCDs 1-2) and m29_cost_model in
# $CARGO_TARGET_DIR/bin; the build loads use their own target dirs under /buildcache.
#
#   OUT=/buildcache/cargo-target/zeebra-848/cal tools/benchlock.sh zb-848-aa \
#     timeout --signal=INT --kill-after=60s 3600 bash research/bench-reserve/run-aa.sh
set -uo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
HERE="$REPO/research/bench-reserve"
BIN="${BIN:-${CARGO_TARGET_DIR:?}/bin/m29_cost_model}"
S="${OUT:?output directory}"
mkdir -p "$S"
cd "$REPO" || exit 2
PIDS=()
note() { echo "$(date +%T) $*" | tee -a "$S/events-aa.log"; }
aa() {
  note "aa $1 start load=$(cut -d' ' -f1 /proc/loadavg)"
  systemd-run --user --scope --quiet --collect --slice=zbbench.slice -p AllowedCPUs=8-23,72-87 -- \
    python3 -I "$HERE/aa.py" "$BIN" "$1" 9 "$S/aa.jsonl" || exit 2
  note "aa $1 end load=$(cut -d' ' -f1 /proc/loadavg)"
}
stop_load() { local p; for p in "${PIDS[@]}"; do kill -TERM -- "-$p" 2>/dev/null; done; wait 2>/dev/null; PIDS=(); }
trap stop_load EXIT
tools/bench-reserve.sh status || exit 2
aa idle
for i in 1 2 3; do
  setsid bash -c "L=/buildcache/cargo-target/zeebra-848-load$i; mkdir -p \$L/tmp
    export RUSTC_WRAPPER='' CARGO_TARGET_DIR=\$L TMPDIR=\$L/tmp CARGO_INCREMENTAL=0
    while :; do cargo clean -q >/dev/null 2>&1
      cargo build -q -j32 --features external-runners --examples --tests >/dev/null 2>&1; done" &
  PIDS+=($!)
done
sleep 60
aa loaded
note "done"
