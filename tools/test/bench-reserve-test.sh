#!/usr/bin/env bash
# Unit tests for tools/bench-reserve.sh, over a synthetic /sys and cgroup tree.
#
# The systemctl calls are not exercised: they are thin wrappers whose failure modes are systemd's.
# What is tested is the arithmetic that decides which CPUs are fenced, and the reading of state that
# decides whether a reservation is real — a status that reported "reserved" over an unfenced CCD
# would publish contaminated figures as clean ones.
set -uo pipefail

SCRIPT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/bench-reserve.sh"
# shellcheck source=../bench-reserve.sh
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

check_rc() { # <label> <expected-rc> <actual-rc>
  if [ "$2" -eq "$3" ]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    printf 'FAIL  %s\n  expected rc: %s\n  actual rc:   %s\n' "$1" "$2" "$3" >&2
  fi
}

ROOT="$(mktemp -d)"
trap 'rm -rf "$ROOT"' EXIT
SYS="$ROOT/sys"
export ZEEBRA_BENCH_RESERVE_SYS="$SYS"

# Three CCDs of two cores each, SMT siblings offset by 6: CCD n = cores 2n,2n+1 and 2n+6,2n+7.
printf '0-11\n' >"$ROOT/online"
mkdir -p "$SYS" && cp "$ROOT/online" "$SYS/online"
for c in $(seq 0 11); do
  mkdir -p "$SYS/cpu$c/cache/index3"
  echo $(((c % 6) / 2)) >"$SYS/cpu$c/cache/index3/id"
done

# --- br_compress -----------------------------------------------------------

# Consecutive ids collapse to ranges, singletons stay single.
check "compress: ranges and singletons" "0-2,5,7-8" "$(br_compress 0 1 2 5 7 8)"
# Input order and duplicates do not matter.
check "compress: unsorted with duplicates" "3-4,9" "$(br_compress 9 4 3 4)"

# --- br_plan ---------------------------------------------------------------

# Reserving one CCD fences its cores and their SMT siblings, and leaves everything else.
check "plan: one CCD takes its siblings too" "bench=2-3,8-9 rest=0-1,4-7,10-11" "$(br_plan 1 | paste -sd' ')"
# Two CCDs given in any order and separator give the same plan.
check "plan: two CCDs, order-independent" "$(br_plan 1,2 | paste -sd' ')" "$(br_plan '2 1' | paste -sd' ')"
# A CCD that does not exist is refused rather than reserving nothing.
br_plan 7 >/dev/null 2>&1
check_rc "plan: an absent CCD is rc 64" 64 $?
# Reserving every CCD would leave the rest of the box nowhere to run.
br_plan 0,1,2 >/dev/null 2>&1
check_rc "plan: reserving every CCD is rc 64" 64 $?
# Unreadable topology is a failed read, not an empty plan.
rm "$SYS/cpu4/cache/index3/id"
br_plan 1 >/dev/null 2>&1
check_rc "plan: unreadable topology is rc 2" 2 $?
echo 2 >"$SYS/cpu4/cache/index3/id"

# --- br_subset -------------------------------------------------------------

# A run's CPUs must lie inside the reservation.
br_subset 2-3 2-3,8-9
check_rc "subset: inside" 0 $?
br_subset 3-4 2-3,8-9
check_rc "subset: straddling the edge is not inside" 1 $?
br_subset 'q' 2-3
check_rc "subset: malformed is rc 64" 64 $?

# --- br_classify -----------------------------------------------------------

# A state file whose rest list matches what app.slice actually gets is a real reservation.
check "classify: state and cgroup agree" reserved "$(br_classify 0-1,4-7,10-11 0-1,4-7,10-11 0-11)"
# The same set spelled differently still agrees.
check "classify: equal sets, different spelling" reserved "$(br_classify 0-1,4-7,10-11 0,1,4-7,10,11 0-11)"
# A state file over an unfenced cgroup is the dangerous case: report it, never "reserved".
check "classify: state but no fence" inconsistent "$(br_classify 0-1,4-7,10-11 0-11 0-11)"
# No state and the full machine available is released.
check "classify: no state, full machine" released "$(br_classify '' 0-11 0-11)"
# No state but a fence nobody recorded is also not a clean release.
check "classify: fence without state" inconsistent "$(br_classify '' 0-5 0-11)"

# --- br_delegated ----------------------------------------------------------

printf 'cpu io memory pids\n' >"$ROOT/controllers"
br_delegated "$ROOT/controllers"
check_rc "delegated: without cpuset" 1 $?
printf 'cpuset cpu io memory pids\n' >"$ROOT/controllers"
br_delegated "$ROOT/controllers"
check_rc "delegated: with cpuset" 0 $?
br_delegated "$ROOT/missing"
check_rc "delegated: unreadable is rc 2" 2 $?

# --- the root step it prints -----------------------------------------------

# setup names the drop-in and the controller it adds; it never runs sudo itself.
case "$(br_setup_text)" in
  *"user@.service.d"*"Delegate=cpu cpuset io memory pids"*) pass=$((pass + 1)) ;;
  *) fail=$((fail + 1)); printf 'FAIL  setup text lost the drop-in\n' >&2 ;;
esac

# --- usage -----------------------------------------------------------------

bash "$SCRIPT" >/dev/null 2>&1
check_rc "usage: no subcommand is rc 64" 64 $?
bash "$SCRIPT" run owner >/dev/null 2>&1
check_rc "usage: run without a CPU list and command is rc 64" 64 $?

printf '\n%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
