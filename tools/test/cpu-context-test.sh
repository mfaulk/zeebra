#!/usr/bin/env bash
# Unit tests for tools/cpu-context.sh, over a synthetic /sys and /proc.
set -uo pipefail

SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/cpu-context.sh"
# shellcheck source=../cpu-context.sh
. "$SCRIPT"

pass=0 fail=0

check() { # <label> <expected> <actual>
  if [ "$2" = "$3" ]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    printf 'FAIL  %s\n  expected: %q\n  actual:   %q\n' "$1" "$2" "$3" >&2
  fi
}

ROOT="$(mktemp -d)"
trap 'rm -rf "$ROOT"' EXIT
SYS="$ROOT/sys" PROC="$ROOT/proc" CLASS="$ROOT/class"
export ZEEBRA_CPU_CONTEXT_SYS="$SYS" ZEEBRA_CPU_CONTEXT_PROC="$PROC" \
  ZEEBRA_CPU_CONTEXT_CLASS="$CLASS" ZEEBRA_BENCHLOCK_DIR="$ROOT/benchlock"

fake_cpu() { # <cpu> <l3-list> <khz or -> [sibling]
  mkdir -p "$SYS/cpu$1/cache/index3" "$SYS/cpu$1/topology" "$SYS/cpu$1/cpufreq"
  printf '%s\n' "$2" >"$SYS/cpu$1/cache/index3/shared_cpu_list"
  printf '%s\n' "$1" >"$SYS/cpu$1/topology/core_id"
  printf '%s\n' "$1${4:+,$4}" >"$SYS/cpu$1/topology/thread_siblings_list"
  printf 'performance\n' >"$SYS/cpu$1/cpufreq/scaling_governor"
  printf '400000\n' >"$SYS/cpu$1/cpufreq/scaling_min_freq"
  printf '4575000\n' >"$SYS/cpu$1/cpufreq/scaling_max_freq"
  [ "$3" = - ] || printf '%s\n' "$3" >"$SYS/cpu$1/cpufreq/scaling_cur_freq"
}
fake_process() { mkdir -p "$PROC/$1"; printf '%s\n' "$2" >"$PROC/$1/comm"; }

fake_cpu 7 "0-7,64-71" 3990000 71
fake_cpu 8 "8-15,72-79" 4540000 72
fake_cpu 9 "8-15,72-79" - 73
printf '0-9,71-73\n' >"$SYS/online"
mkdir -p "$PROC/sys/kernel" && printf '7.3.3-test\n' >"$PROC/sys/kernel/osrelease"
# user nice system idle iowait irq softirq steal: busy = user+nice+system+irq+softirq+steal.
{
  printf 'cpu  1 1 1 1 1 1 1 1 0 0\n'
  for c in 0 1 2 3 4 5 6 7 8 9 71 72 73; do printf 'cpu%s 100 0 50 800 50 0 0 0 0 0\n' "$c"; done
  printf 'intr 1\n'
} >"$PROC/stat"
mkdir -p "$CLASS/powercap/intel-rapl:0" "$CLASS/hwmon/hwmon0" "$CLASS/hwmon/hwmon1"
printf '123456\n' >"$CLASS/powercap/intel-rapl:0/energy_uj"
printf '65532610987\n' >"$CLASS/powercap/intel-rapl:0/max_energy_range_uj"
printf 'nvme\n' >"$CLASS/hwmon/hwmon0/name"
printf '39850\n' >"$CLASS/hwmon/hwmon0/temp1_input"
printf 'k10temp\n' >"$CLASS/hwmon/hwmon1/name"
printf '70125\n' >"$CLASS/hwmon/hwmon1/temp1_input"
mkdir -p "$ROOT/benchlock"
cat >"$ROOT/benchlock/benchlock.log" <<'LOG'
2026-11-20T22:00:00-05:00  START    zb-1            pid=20       waited=0s load=1.0 lock=exclusive x
2026-11-20T22:00:00-05:00  START    zb-2            pid=21       waited=0s load=1.0 lock=exclusive y
2026-11-20T22:01:00-05:00  END      zb-2            pid=21       status=0 end=exited elapsed=60s y
2026-11-20T22:02:00-05:00  QUEUED   zb-3            pid=22       z
2026-11-20T22:02:00-05:00  START    zb-4            pid=23       waited=0s load=1.0 lock=ccd:1 dead
LOG
fake_process 20 bash
fake_process 21 bash
fake_process 22 bash
fake_process 30 Runner.Listener
fake_process 31 Runner.Listener
fake_process 32 Runner.Worker
mkdir -p "$SYS/cpufreq" && printf '1\n' >"$SYS/cpufreq/boost"
mkdir -p "$PROC" && printf '1.50 2.25 3.00 2/900 4242\n' >"$PROC/loadavg"
fake_process 10 rustc
fake_process 11 rustc
fake_process 12 ld.lld
fake_process 13 bash
fake_process 14 m29_cost_model

# A CPU list expands ranges and singletons in order, and a malformed one is a usage error.
check "cpulist: ranges and singletons" "2 3 4 9" "$(ctx_expand_cpulist 2-4,9)"
ctx_expand_cpulist 5-3 >/dev/null; check "cpulist: reversed range refused" 64 $?
ctx_expand_cpulist 'a' >/dev/null; check "cpulist: non-numeric refused" 64 $?

# Only compiler and linker processes count as compiler activity, not the measured binary or a shell.
check "compilers: rustc twice and the linker" 3 "$(ctx_compiler_count)"

# A snapshot records load, each CPU's L3 domain and clock, and how many domains the list spans.
out="$(ctx_snapshot 7-9)"
check "snapshot: exit 0" 0 $?
case "$out" in *'"load1":1.50,"load5":2.25,"load15":3.00,'*) r=ok ;; *) r="$out" ;; esac
check "snapshot: load triple" ok "$r"
case "$out" in *'"l3_domains":2,'*) r=ok ;; *) r="$out" ;; esac
check "snapshot: two L3 domains across CPUs 7-9" ok "$r"
case "$out" in *'{"cpu":8,"l3":"8-15,72-79","core":8,"khz":4540000,'*) r=ok ;; *) r="$out" ;; esac
check "snapshot: per-CPU entry" ok "$r"
case "$out" in *'"compilers":3,'*'"boost":"1"'* | *'"boost":"1"'*'"compilers":3,'*) r=ok ;; *) r="$out" ;; esac
check "snapshot: compilers and boost" ok "$r"

# A CPU without a readable frequency is recorded as null rather than failing the snapshot.
case "$out" in *'{"cpu":9,"l3":"8-15,72-79","core":9,"khz":null,'*) r=ok ;; *) r="$out" ;; esac
check "snapshot: missing frequency is null" ok "$r"

# The output is one valid JSON object, when a JSON parser is available to say so.
if command -v python3 >/dev/null; then
  printf '%s' "$out" | python3 -c 'import json,sys; json.load(sys.stdin)'
  check "snapshot: parses as JSON" 0 $?
fi

# SMT siblings are the bench CPUs' thread siblings outside the bench list itself.
check "siblings: of 8-9" "72 73" "$(ctx_siblings 8 9)"
check "siblings: a listed sibling is bench, not sibling" "73" "$(ctx_siblings 8 9 72)"

# /proc/stat counters reduce to busy and total jiffies per CPU, for the listed CPUs only.
check "stat: tokens" "8:150:1000 72:150:1000" "$(ctx_stat_tokens 8 72)"
check "stat: sum over a set" "300:2000:2" "$(ctx_stat_sum 8 72)"

# Busy percent over an interval is the busy delta over the total delta, per CPU.
check "busy: deltas" '[{"cpu":8,"pct":50.0},{"cpu":72,"pct":5.0}]' \
  "$(ctx_busy_pct "8:100:1000 72:0:1000" "8:150:1100 72:5:1100")"

# The clock mode is boost when boost is on, fixed@MHz when off with one max across the list.
check "clock: boost" boost "$(ctx_clock_mode 1 4540000 4540000)"
check "clock: fixed" fixed@3000 "$(ctx_clock_mode 0 3000000 3000000)"
check "clock: mixed caps are unknown" unknown "$(ctx_clock_mode 0 3000000 2900000)"

# Runner processes are counted by class, separately from compilers.
check "counts: runner listeners" 2 "$(ctx_count_comm Runner.Listener)"
check "counts: runner workers" 1 "$(ctx_count_comm Runner.Worker)"

# Open benchlock owners are STARTs with no END whose process is still alive.
check "benchlock: open and alive" '[{"owner":"zb-1","pid":20}]' "$(ctx_benchlock_open)"

# The snapshot carries the new fields, each with the value the synthetic tree implies.
if command -v python3 >/dev/null; then
  fields="$(printf '%s' "$out" | python3 -c '
import json,sys
d=json.load(sys.stdin)
print(d["kernel"], d["clock"], d["siblings"], d["rapl_uj"], d["rapl_max_uj"], d["temp_mc"],
      d["runner_listeners"], d["runner_workers"], len(d["benchlock_open"]),
      d["cpus"][1]["min_khz"], d["cpus"][1]["max_khz"],
      [(s["cpu"], s["role"], s["busy"], s["total"]) for s in d["stat"]], d["rest_stat"])')"
  check "snapshot: new fields" "7.3.3-test boost 71-73 123456 65532610987 70125 2 1 1 400000 4575000 \
[(7, 'bench', 150, 1000), (8, 'bench', 150, 1000), (9, 'bench', 150, 1000), \
(71, 'sibling', 150, 1000), (72, 'sibling', 150, 1000), (73, 'sibling', 150, 1000)] \
{'busy': 1050, 'total': 7000, 'cpus': 7}" "$fields"
fi

# An interval snapshot adds busy percent per bench CPU and sibling over the window.
out3="$(bash "$SCRIPT" --interval 0 8)"
case "$out3" in *'"interval_busy_pct":[{"cpu":8,"pct":0.0},{"cpu":72,"pct":0.0}]'*) r=ok ;; *) r="$out3" ;; esac
check "interval: busy percent per CPU" ok "$r"

# Unreadable RAPL and temperature are null, not failures: RAPL energy is root-only by default.
rm "$CLASS/powercap/intel-rapl:0/energy_uj"
rm -r "$CLASS/hwmon/hwmon1"
out2="$(ctx_snapshot 8)"
check "snapshot: exit 0 without RAPL" 0 $?
case "$out2" in *'"rapl_uj":null,'*'"temp_mc":null,'*) r=ok ;; *) r="$out2" ;; esac
check "snapshot: RAPL and temperature null" ok "$r"

# A CPU whose topology cannot be read fails the snapshot rather than printing a partial context.
ctx_snapshot 7,42 >/dev/null 2>&1; check "snapshot: unknown CPU is a read failure" 2 $?

# An unreadable load average is a read failure, never a load of zero.
rm "$PROC/loadavg"
ctx_snapshot 7 >/dev/null 2>&1; check "snapshot: missing loadavg is a read failure" 2 $?

# The command line takes exactly one CPU list.
bash "$SCRIPT" >/dev/null 2>&1; check "main: no argument is usage" 64 $?

printf 'cpu-context: %d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
