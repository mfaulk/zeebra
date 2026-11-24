#!/usr/bin/env bash
# #945's gate reads: interleaved A/B pairs, alternating arm order, each attempt its own process inside
# a CCD reservation (tools/bench-reserve.sh run, which also takes the CCD lock).
#
#   research/945-lane-kernel/run.sh <out.jsonl> <study-binary> <gate-binary> <captures-dir> [phase...]
#
# Phases: complete (dense n = 18/20 at GF(31), n = 18 at GF(32003), 16 workers), controls (sparse
# controls, 16 workers), matrix (serial forward pass on the n = 20 b3 capture). Default: all three.
# Both arms of a phase run the same binary; the lane arm adds `--lane` or selects `lane`.
set -euo pipefail
out=$1 study=$2 gate=$3 captures=$4
shift 4
phases=("$@")
((${#phases[@]})) || phases=(complete controls matrix)
here=$(cd "$(dirname "$0")/../.." && pwd)
reserve=$here/tools/bench-reserve.sh

# Reserve if nobody has, and release on exit; ride an existing reservation otherwise. The first
# deciding run (2026-11-23) rode another agent's reservation, lost it after five attempts and
# recorded 151 instant refusals as rc 2, so a lost reservation now stops the run instead.
status_rc=0
"$reserve" status > /dev/null || status_rc=$?
case $status_rc in
  0) ;;
  1) "$reserve" reserve; trap '"$reserve" release' EXIT ;;
  *) echo "bench-reserve status failed; refusing to measure" >&2; exit 2 ;;
esac

attempt() { # <label> <arm> <cpus> <cap-s> <command...>
  local label=$1 arm=$2 cpus=$3 cap=$4
  shift 4
  local log
  log=$(mktemp "${TMPDIR:?}/945-attempt.XXXXXX")
  local rc=0
  "$reserve" run zb-945 "$cpus" env RUSTC_WRAPPER="" /usr/bin/time -f 'TIME %e %M' \
    timeout --signal=INT --kill-after=30s "$cap" "$@" > "$log" 2>&1 || rc=$?
  python3 - "$label" "$arm" "$rc" "$log" >> "$out" <<'EOF'
import json, sys
label, arm, rc, path = sys.argv[1:]
lines = open(path).read().splitlines()
time = [l for l in lines if l.startswith("TIME ")]
text = "\n".join(l for l in lines if not l.startswith("TIME "))
start = text.find("{")
record = json.JSONDecoder().raw_decode(text[start:])[0] if start >= 0 else {}
wall, rss_kib = (time[-1].split()[1:3] if time else (None, None))
keep = ("status", "call_ns", "basis_m33", "peak_rss_bytes", "forward_seconds", "output_digest",
        "row_operations", "peak_rss", "peak_nonzeros")
statistics = record.get("statistics") or {}
record.update({k: statistics[k] for k in ("elimination_ns", "claim_peak_live_bytes")
               if k in statistics})
keep += ("elimination_ns", "claim_peak_live_bytes")
print(json.dumps({"label": label, "arm": arm, "rc": int(rc),
                  "wall_s": float(wall) if wall else None,
                  "max_rss_kib": int(rss_kib) if rss_kib else None,
                  **{k: record[k] for k in keep if k in record}}))
EOF
  if ((rc != 0)); then
    cp "$log" "$out.failed-$(date +%s%N)"
    if ! "$reserve" status > /dev/null; then
      echo "reservation lost after a failed attempt ($label $arm, rc $rc); stopping" >&2
      rm -f "$log"
      exit 3
    fi
  fi
  rm -f "$log"
}

pairs() { # <label> <n> <cpus> <cap-s> <command...>: n pairs, order alternating, lane via --lane
  local label=$1 n=$2 cpus=$3 cap=$4
  shift 4
  for ((i = 0; i < n; i++)); do
    if ((i % 2 == 0)); then
      attempt "$label" field "$cpus" "$cap" "$@"
      attempt "$label" lane "$cpus" "$cap" "$@" --lane
    else
      attempt "$label" lane "$cpus" "$cap" "$@" --lane
      attempt "$label" field "$cpus" "$cap" "$@"
    fi
  done
}

for phase in "${phases[@]}"; do
  case $phase in
    complete)
      # The shipping dispatcher, to tie the `sigf4 --claim` mirror to #1033's `entry` baseline.
      for ((i = 0; i < 3; i++)); do
        attempt gf31-dense-18-w16 entry 8-23 180 "$study" --field gf31 --name mq-dense-18-s18 \
          --generate --engine entry --workers 16 --digest-only
      done
      attempt gf31-dense-20-w16 entry 8-23 900 "$study" --field gf31 --name mq-dense-20-s20 \
        --generate --engine entry --workers 16 --live-gib 8 --digest-only
      pairs gf31-dense-18-w16 9 8-23 180 "$study" --field gf31 --name mq-dense-18-s18 --generate \
        --engine sigf4 --claim --workers 16 --digest-only
      pairs gf32003-dense-18-w16 5 8-23 180 "$study" --field gf32003 --name mq-dense-18-s18 \
        --generate --engine sigf4 --claim --workers 16 --digest-only
      pairs gf31-dense-20-w16 5 8-23 900 "$study" --field gf31 --name mq-dense-20-s20 --generate \
        --engine sigf4 --claim --workers 16 --live-gib 8 --digest-only
      ;;
    controls)
      for row in katsura-8 cyclic-6 mq-random-10-s10; do
        for field in gf31 gf32003; do
          pairs "$field-$row-w16" 9 8-23 180 "$study" --field "$field" --name "$row" --generate \
            --engine sigf4 --claim --workers 16 --digest-only
        done
      done
      ;;
    matrix)
      z=$captures/gf31__mq-dense-20-s20__b3.zmat
      for ((i = 0; i < 3; i++)); do
        if ((i % 2 == 0)); then order=(accumulator lane); else order=(lane accumulator); fi
        for arm in "${order[@]}"; do
          attempt gf31-dense-20-b3-forward "$arm" 8 3600 "$gate" "$z" 20 gf31 "$arm"
        done
      done
      ;;
    *) echo "unknown phase $phase" >&2; exit 64 ;;
  esac
done
