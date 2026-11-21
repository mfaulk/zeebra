#!/usr/bin/env bash
# Unit tests for tools/bench-clock.sh, over a synthetic /sys/devices/system/cpu.
set -uo pipefail

SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/bench-clock.sh"
# shellcheck source=../bench-clock.sh
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
SYS="$ROOT/sys"
export ZEEBRA_BENCH_CLOCK_SYS="$SYS" ZEEBRA_BENCH_CLOCK_STATE="$ROOT/state"

fake_cpu() { # <cpu>
  local d="$SYS/cpu$1/cpufreq"
  mkdir -p "$d"
  printf '413419\n' >"$d/cpuinfo_min_freq"
  printf '4575164\n' >"$d/cpuinfo_max_freq"
  printf '1433184\n' >"$d/scaling_min_freq"
  printf '4575164\n' >"$d/scaling_max_freq"
}
fake_cpu 8
fake_cpu 72
mkdir -p "$SYS/cpufreq" && printf '1\n' >"$SYS/cpufreq/boost"
freqs() { cat "$SYS/cpu$1/cpufreq/scaling_min_freq" "$SYS/cpu$1/cpufreq/scaling_max_freq" | tr '\n' ' '; }

# Status before any fix reports boost and exits 1, as bench-reserve's released state does.
out="$(bc_status 8,72)"
check "status: boost rc" 1 $?
case "$out" in *"clock=boost"*) r=ok ;; *) r="$out" ;; esac
check "status: boost line" ok "$r"

# A frequency outside the CPUs' hardware range, or not a number, is a usage error and writes nothing.
bc_fix 9000 8,72 >/dev/null 2>&1; check "fix: above cpuinfo_max refused" 64 $?
bc_fix 3.5 8,72 >/dev/null 2>&1; check "fix: non-integer refused" 64 $?
check "fix: refused fix wrote nothing" "1433184 4575164 " "$(freqs 8)"

# Fixing disables boost and pins min = max = the target on every listed CPU, recording the old state.
bc_fix 3000 8,72 >/dev/null; check "fix: rc" 0 $?
check "fix: boost off" 0 "$(cat "$SYS/cpufreq/boost")"
check "fix: cpu 8 pinned" "3000000 3000000 " "$(freqs 8)"
check "fix: cpu 72 pinned" "3000000 3000000 " "$(freqs 72)"
out="$(bc_status)"
check "status: fixed rc" 0 $?
case "$out" in *"clock=fixed@3000"*"cpus=8,72"*) r=ok ;; *) r="$out" ;; esac
check "status: fixed line" ok "$r"

# A second fix while one is recorded is refused, so the saved original state is never overwritten.
bc_fix 2800 8,72 >/dev/null 2>&1; check "fix: second fix refused" 1 $?

# A recorded fix that sysfs no longer shows is inconsistent, not fixed.
printf '4575164\n' >"$SYS/cpu72/cpufreq/scaling_max_freq"
bc_status >/dev/null; check "status: drifted fix is inconsistent" 2 $?
printf '3000000\n' >"$SYS/cpu72/cpufreq/scaling_max_freq"

# Restore puts back boost and each CPU's own min and max, and clears the record.
bc_restore >/dev/null; check "restore: rc" 0 $?
check "restore: boost on" 1 "$(cat "$SYS/cpufreq/boost")"
check "restore: cpu 8" "1433184 4575164 " "$(freqs 8)"
check "restore: cpu 72" "1433184 4575164 " "$(freqs 72)"
check "restore: state removed" no "$([ -e "$ROOT/state" ] && echo yes || echo no)"
bc_restore >/dev/null 2>&1; check "restore: nothing to restore" 1 $?

# A write that fails part-way rolls every CPU back rather than leaving a half-fixed clock.
if [ "$(id -u)" -ne 0 ]; then
  chmod 444 "$SYS/cpu72/cpufreq/scaling_max_freq"
  bc_fix 3000 8,72 >/dev/null 2>&1; check "fix: partial failure rc" 2 $?
  check "fix: partial failure rolled back cpu 8" "1433184 4575164 " "$(freqs 8)"
  check "fix: partial failure rolled back boost" 1 "$(cat "$SYS/cpufreq/boost")"
  check "fix: partial failure leaves no record" no "$([ -e "$ROOT/state" ] && echo yes || echo no)"
  chmod 644 "$SYS/cpu72/cpufreq/scaling_max_freq"

  # Without the test seam, fix and restore need root and refuse before touching anything.
  env -u ZEEBRA_BENCH_CLOCK_SYS bash "$SCRIPT" fix 3000 >/dev/null 2>&1
  check "gate: fix needs root" 77 $?
  env -u ZEEBRA_BENCH_CLOCK_SYS bash "$SCRIPT" restore >/dev/null 2>&1
  check "gate: restore needs root" 77 $?
fi

# No subcommand is usage; the script does nothing unless a subcommand is named.
bash "$SCRIPT" >/dev/null 2>&1; check "main: no subcommand is usage" 64 $?

printf 'bench-clock: %d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
