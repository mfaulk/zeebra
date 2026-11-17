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
SYS="$ROOT/sys" PROC="$ROOT/proc"
export ZEEBRA_CPU_CONTEXT_SYS="$SYS" ZEEBRA_CPU_CONTEXT_PROC="$PROC"

fake_cpu() { # <cpu> <l3-list> <khz or ->
  mkdir -p "$SYS/cpu$1/cache/index3" "$SYS/cpu$1/topology" "$SYS/cpu$1/cpufreq"
  printf '%s\n' "$2" >"$SYS/cpu$1/cache/index3/shared_cpu_list"
  printf '%s\n' "$1" >"$SYS/cpu$1/topology/core_id"
  printf 'performance\n' >"$SYS/cpu$1/cpufreq/scaling_governor"
  [ "$3" = - ] || printf '%s\n' "$3" >"$SYS/cpu$1/cpufreq/scaling_cur_freq"
}
fake_process() { mkdir -p "$PROC/$1"; printf '%s\n' "$2" >"$PROC/$1/comm"; }

fake_cpu 7 "0-7,64-71" 3990000
fake_cpu 8 "8-15,72-79" 4540000
fake_cpu 9 "8-15,72-79" -
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
case "$out" in *'{"cpu":8,"l3":"8-15,72-79","core":8,"khz":4540000}'*) r=ok ;; *) r="$out" ;; esac
check "snapshot: per-CPU entry" ok "$r"
case "$out" in *'"compilers":3,'*'"boost":"1"'* | *'"boost":"1"'*'"compilers":3,'*) r=ok ;; *) r="$out" ;; esac
check "snapshot: compilers and boost" ok "$r"

# A CPU without a readable frequency is recorded as null rather than failing the snapshot.
case "$out" in *'{"cpu":9,"l3":"8-15,72-79","core":9,"khz":null}'*) r=ok ;; *) r="$out" ;; esac
check "snapshot: missing frequency is null" ok "$r"

# The output is one valid JSON object, when a JSON parser is available to say so.
if command -v python3 >/dev/null; then
  printf '%s' "$out" | python3 -c 'import json,sys; json.load(sys.stdin)'
  check "snapshot: parses as JSON" 0 $?
fi

# A CPU whose topology cannot be read fails the snapshot rather than printing a partial context.
ctx_snapshot 7,42 >/dev/null 2>&1; check "snapshot: unknown CPU is a read failure" 2 $?

# An unreadable load average is a read failure, never a load of zero.
rm "$PROC/loadavg"
ctx_snapshot 7 >/dev/null 2>&1; check "snapshot: missing loadavg is a read failure" 2 $?

# The command line takes exactly one CPU list.
bash "$SCRIPT" >/dev/null 2>&1; check "main: no argument is usage" 64 $?

printf 'cpu-context: %d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
