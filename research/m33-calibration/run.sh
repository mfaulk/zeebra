#!/usr/bin/env bash
#
# One calibration session (#968): a dev-mode bench-job over Eco-12/wide64 and MQ10/gf32003 at 1 and
# 16 workers, arms `a` and `a2` (the same F0 binary: A/A) and `s5` (the same binary plus a sleep of
# 5% of its own wall: a known slowdown), under one background-load condition on the non-bench CPUs.
#
#   research/m33-calibration/run.sh idle|build|stream
#
# The load starts only once the job holds its benchlock, so a queued session never loads the
# machine under someone else's measurement, and it is killed when the job ends. Everything lives
# under $W (/buildcache, never $HOME).

set -uo pipefail

COND="${1:?usage: run.sh idle|build|stream}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
W=/buildcache/cargo-target/zeebra-968
C=31e334bda226d896686c64495867729119e52b0f
B="$W/target/release/examples/sig_f4_study"
REST=0-7,24-71,88-127
REPS="${REPS:-9}"
export ZEEBRA_BENCH_JOBS="$W/jobs" RUSTC_WRAPPER="" TMPDIR="$W/tmp"

sha() { sha256sum "$1" | cut -c1-64; }

# The slow arm: the A binary, then a sleep of 5% of its measured wall. No hash check inside: it
# would be timed. The A binary sits in this private target dir and its hash is in the manifest.
mkdir -p "$W/slow5"
S="$W/slow5/sig_f4_study"
printf '#!/bin/sh\nt0=$(date +%%s%%N); "%s" "$@"; rc=$?; t1=$(date +%%s%%N)\nsleep "$(awk -v d=$((t1 - t0)) '"'"'BEGIN { printf "%%.6f", d * 0.05 / 1e9 }'"'"')"\nexit $rc\n' "$B" >"$S"
chmod 755 "$S"

arm() { # <name> <binary> <recipe-suffix>
  printf '{"name":"%s","commit":"%s","binary":"%s","sha256":"%s","build":{"profile":"release","flags":".cargo/config.toml (x86-64-v3, fat LTO, 1 CGU)","recipe":"git archive %s | tar -x; cargo build --release --locked --features research-sigf4 --example sig_f4_study%s"},"argv":["--field","{field}","--name","{name}","--engine","entry","--workers","{workers}","--wall-s","600"]}' \
    "$1" "$C" "$2" "$(sha "$2")" "$C" "$3"
}
M="$W/manifest-$COND-$(date +%Y%m%dT%H%M%S).json"
printf '{"schema":"bench-job-manifest-v1","mode":"dev","context":{"issue":968,"agent":"%s","condition":"%s","session":"%s","bin_sha256":"%s"},"arms":[%s,%s,%s],"instances":[{"name":"wide64/eco-12","params":{"field":"wide64","name":"eco-12"}},{"name":"gf32003/mq-random-10","params":{"field":"gf32003","name":"mq-random-10"}}],"run":{"workers":[1,16],"cpus":"8-23","repetitions":%s,"interleave":"rotate","seeds":[0],"retries":0,"limits":{"wall_seconds":600,"kill_after_seconds":60,"rss_bytes":17179869184,"live_bytes":null}}}\n' \
  "$("$REPO/scripts/agent/zb-claim.sh" id)" "$COND" "$(date --iso-8601=seconds)" "$(sha "$B")" \
  "$(arm a "$B" "")" "$(arm a2 "$B" "")" "$(arm s5 "$S" "; slow5 wrapper sleeps 5% of the wall")" "$REPS" >"$M"
JOB="$("$REPO/tools/bench-job" submit "$M")" || exit 2
echo "condition=$COND job=$JOB manifest=$M"

"$REPO/tools/bench-job" run "$JOB" >"$W/run-$JOB.log" 2>&1 &
RUNNER=$!
LOAD=""
cleanup() { [ -z "$LOAD" ] || kill -- -"$LOAD" 2>/dev/null; }
trap cleanup EXIT
trap 'cleanup; kill "$RUNNER" 2>/dev/null; exit 130' INT TERM

until [ "$("$REPO/tools/bench-job" status "$JOB" --json | python3 -c 'import json,sys; print(json.load(sys.stdin)["state"])')" = running ]; do
  kill -0 "$RUNNER" 2>/dev/null || { echo "runner exited before starting" >&2; exit 2; }
  sleep 5
done
echo "running at $(date --iso-8601=seconds)"
case "$COND" in
  idle) ;;
  build)
    mkdir -p "$W/load-target"
    setsid taskset -c "$REST" bash -c "cd '$W/src-${C:0:8}' && while :; do CARGO_TARGET_DIR='$W/load-target' cargo clean -q; CARGO_TARGET_DIR='$W/load-target' cargo build -q -j48 --tests >/dev/null 2>&1; done" &
    LOAD=$!
    ;;
  stream)
    setsid taskset -c "$REST" "$W/stream" 32 &
    LOAD=$!
    ;;
  *) echo "unknown condition $COND" >&2; exit 64 ;;
esac
wait "$RUNNER"
rc=$?
echo "job=$JOB rc=$rc ended $(date --iso-8601=seconds)"
exit "$rc"
