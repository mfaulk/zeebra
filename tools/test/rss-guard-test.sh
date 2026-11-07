#!/usr/bin/env bash
# Unit tests for tools/rss-guard.sh, over a synthetic /proc.
#
# The guard's whole job is to observe the right process, so the tests supply the
# process table (`ZEEBRA_RSS_GUARD_PIDS`) and the `/proc` it reads
# (`ZEEBRA_RSS_GUARD_PROC`) rather than spawning real binaries: the failure this
# script exists to prevent is a guard that watches the wrong pid, and that is
# only visible if the test controls which pids exist.
set -uo pipefail

GUARD="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/rss-guard.sh"
# shellcheck source=../rss-guard.sh
. "$GUARD"

pass=0 fail=0

check() { # <label> <expected> <actual>
  if [ "$2" = "$3" ]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    printf 'FAIL  %s\n  expected: %q\n  actual:   %q\n' "$1" "$2" "$3" >&2
  fi
}

check_rc() { # <label> <expected-rc> <actual-rc>
  if [ "$2" -eq "$3" ]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    printf 'FAIL  %s\n  expected rc: %s\n  actual rc:   %s\n' "$1" "$2" "$3" >&2
  fi
}

PROC="$(mktemp -d)"
trap 'rm -rf "$PROC"' EXIT

fake_process() { # <pid> <comm> <cmdline> <vmhwm-kb>
  mkdir -p "$PROC/$1"
  printf '%s\n' "$2" >"$PROC/$1/comm"
  # A real cmdline is NUL-separated, which is what makes `grep -a` the right reader.
  printf '%s\0' $3 >"$PROC/$1/cmdline"
  printf 'Name:\t%s\nVmHWM:\t%s kB\nVmRSS:\t12 kB\n' "$2" "$4" >"$PROC/$1/status"
}

export ZEEBRA_RSS_GUARD_PROC="$PROC"

# The binary under measurement, plus the two bash wrappers whose cmdline carries
# the whole script text — the arrangement from #328.
fake_process 100 anemoi_ladder "./target/release/examples/anemoi_ladder row anemoi17-cico-n6-fcico" 7340032
fake_process 200 bash "bash -c for_p_in_pgrep_-f_examples/anemoi_ladder_row_anemoi17-cico-n6-fcico" 3992
fake_process 300 bash "bash -c anemoi17-cico-n6-fcico" 2492

# --- guard_comm_key --------------------------------------------------------

# /proc/<pid>/comm is truncated to 15 characters, so the key compared against it
# must be truncated the same way or a longer binary name never matches.
check "comm key: short name is unchanged" anemoi_ladder "$(guard_comm_key anemoi_ladder)"
check "comm key: 16 characters truncate to 15" "sixteen_charact" "$(guard_comm_key sixteen_characters)"

# --- guard_is_wrapper_name -------------------------------------------------

# Watching a wrapper is the defect, so wrapper names are rejected at the door
# rather than matched and then found to have a 4 MB high-water mark.
for wrapper in bash sh timeout env taskset flock; do
  guard_is_wrapper_name "$wrapper"
  check_rc "wrapper name rejected: $wrapper" 0 $?
done
guard_is_wrapper_name anemoi_ladder
check_rc "a binary name is not a wrapper name" 1 $?

# --- guard_confirms_id -----------------------------------------------------

# A comm match is necessary but not sufficient: the row identity must be
# confirmed from the cmdline, so a second run of the same binary is not watched.
guard_confirms_id 100 anemoi17-cico-n6-fcico
check_rc "cmdline confirms the row id" 0 $?
guard_confirms_id 100 anemoi17-cico-n6-pcico
check_rc "cmdline rejects a different row id" 1 $?
guard_confirms_id 999 anemoi17-cico-n6-fcico
check_rc "a pid that has exited does not confirm" 1 $?

# --- guard_hwm_kb ----------------------------------------------------------

# VmHWM, the high-water mark, not VmRSS: a peak that has already been released
# still breached the ceiling and must still be seen.
check "hwm: read from VmHWM" 7340032 "$(guard_hwm_kb 100)"
check "hwm: the wrapper's own footprint" 3992 "$(guard_hwm_kb 200)"
guard_hwm_kb 999 >/dev/null 2>&1
check_rc "hwm: a vanished pid is a read failure, not 0 kB" 2 $?

# --- guard_scan ------------------------------------------------------------

# The scan picks the binary by comm and ignores both wrappers, even though each
# wrapper's cmdline contains the id being searched for.
check "scan: matches the binary, not the wrappers" "100" \
  "$(ZEEBRA_RSS_GUARD_PIDS="100 200 300" guard_matching_pids anemoi_ladder anemoi17-cico-n6-fcico)"

# Above the ceiling, the guard fires and reports the pid it signalled.
out="$(ZEEBRA_RSS_GUARD_PIDS="100 200 300" guard_scan anemoi_ladder anemoi17-cico-n6-fcico 6291456 --dry-run)"
rc=$?
check_rc "scan: over the ceiling exits 3" 3 "$rc"
check "scan: over the ceiling names the pid and the mark" "OVER pid=100 hwm_kb=7340032 ceiling_kb=6291456" "$out"

# At or below the ceiling it does not fire: the ceiling is a limit, not a target.
ZEEBRA_RSS_GUARD_PIDS="100 200 300" guard_scan anemoi_ladder anemoi17-cico-n6-fcico 7340032 --dry-run >/dev/null
check_rc "scan: exactly at the ceiling does not fire" 0 $?
ZEEBRA_RSS_GUARD_PIDS="100 200 300" guard_scan anemoi_ladder anemoi17-cico-n6-fcico 8388608 --dry-run >/dev/null
check_rc "scan: under the ceiling does not fire" 0 $?

# The case that made #328 worth filing: nothing matched. A guard that observed
# no process must say so, because "watched nothing" and "watched and it was
# fine" are the same output otherwise — and the first is not a guarded run.
ZEEBRA_RSS_GUARD_PIDS="200 300" guard_scan anemoi_ladder anemoi17-cico-n6-fcico 1024 --dry-run >/dev/null 2>&1
check_rc "scan: no process matched exits 1, distinct from a clean pass" 1 $?

# --- the invariant the script is for --------------------------------------

# `pgrep -f` is what put a wrapper's pid where a binary's belonged. The guard
# must not reintroduce it, and a grep over its own text is the only check that
# survives a later edit.
# Comment lines are excluded: the header explains the hazard by name, deliberately.
if grep -vE '^[[:space:]]*#' "$GUARD" | grep -qE 'pgrep[[:space:]]+-[a-z]*f'; then
  fail=$((fail + 1))
  printf 'FAIL  the guard uses pgrep -f, which is the defect it exists to avoid\n' >&2
else
  pass=$((pass + 1))
fi

# ---------------------------------------------------------------------------

printf '\n%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
