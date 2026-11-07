#!/usr/bin/env bash
# Unit tests for tools/benchlock.sh, over the cause of an END rather than over the lock.
#
# The subject is #344: a 1.5-hour measurement was killed when the shell that launched it was
# stopped, and the log recorded `END status=0 elapsed=3177s` — indistinguishable from a run that
# finished. What the lock must now get right is **why** a run ended, so the tests drive the
# classification directly and then confirm the real script writes it.
#
# Every test that runs the script sets ZEEBRA_BENCHLOCK_DIR to a throwaway directory. Taking the
# real lock would block whichever agent is measuring, and appending to the real log would
# contaminate the audit trail these tests exist to defend.
set -uo pipefail

BENCHLOCK="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/benchlock.sh"
# shellcheck source=../benchlock.sh
. "$BENCHLOCK"

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

contains() { # <label> <needle> <haystack>
  case "$3" in
    *"$2"*) pass=$((pass + 1)) ;;
    *) fail=$((fail + 1)); printf 'FAIL  %s\n  expected to contain: %q\n  actual: %q\n' "$1" "$2" "$3" >&2 ;;
  esac
}

lacks() { # <label> <needle> <haystack>
  case "$3" in
    *"$2"*) fail=$((fail + 1)); printf 'FAIL  %s\n  must not contain: %q\n  actual: %q\n' "$1" "$2" "$3" >&2 ;;
    *) pass=$((pass + 1)) ;;
  esac
}

# --- bl_signal_name --------------------------------------------------------

# The fatal signals are named rather than numbered in the log, because the reader of an audit
# trail is looking for "was this killed" and 143 does not say so.
check "signal name: TERM" TERM "$(bl_signal_name 15)"
check "signal name: HUP, which is what an exiting launcher sends" HUP "$(bl_signal_name 1)"
check "signal name: INT, which is also timeout's budget signal" INT "$(bl_signal_name 2)"
check "signal name: KILL" KILL "$(bl_signal_name 9)"
# An unrecognized number still has to render, or the END line loses its cause entirely.
check "signal name: an unknown number renders as itself" "signal 62" "$(bl_signal_name 62)"

# --- bl_end_cause, the classification --------------------------------------

# A clean exit is the only case that may be called one.
check "cause: exit 0 with nothing else wrong" exited "$(bl_end_cause 0 '' same)"

# A nonzero exit is still the command's own answer, and must not be dressed up as a kill.
check "cause: a failing command exited" exited "$(bl_end_cause 1 '' same)"

# GNU timeout's convention. This is the case the §9 resource policy authorizes bounded runs on,
# and it only means anything if it is distinguishable from the two kills below.
check "cause: 124 is the timeout budget" budget "$(bl_end_cause 124 '' same)"

# The command died of a signal: its wait status is 128+n and the log should name the signal.
check "cause: a child killed by TERM" "signalled-child(TERM)" "$(bl_end_cause 143 '' same)"
check "cause: a child killed by KILL, which is timeout --kill-after" "signalled-child(KILL)" "$(bl_end_cause 137 '' same)"

# THE CASE #344 IS ABOUT. The lock itself was signalled, so whatever the child reported, this run
# did not complete — and in the incident the child reported 0, because an intermediate `bash
# run.sh` without `set -e` exited on its own last command after the binary under it died.
check "cause: the lock was signalled, child reported success" \
  "launcher-signal(TERM)" "$(bl_end_cause 0 15 same)"
check "cause: a signal to the lock outranks the child's status" \
  "launcher-signal(HUP)" "$(bl_end_cause 143 1 same)"

# --- bl_end_status, which must never be 0 for a killed run -----------------

# The defect in one assertion: the status recorded for a launcher-killed run was 0.
check "status: a launcher-killed run is NOT 0" 143 "$(bl_end_status 0 15 same)"
check "status: a HUP to the lock is 129" 129 "$(bl_end_status 0 1 same)"

# A run that really did finish keeps its own status, so nothing that reads the log for failures
# starts seeing them where there are none.
check "status: a clean run is still 0" 0 "$(bl_end_status 0 '' same)"
check "status: a failing command keeps its status" 2 "$(bl_end_status 2 '' same)"
check "status: a budget stop keeps 124" 124 "$(bl_end_status 124 '' same)"

# --- the EXIT-trap route ----------------------------------------------------

# An END written from the EXIT trap must never claim the command exited: the script did not reach
# its own last line, so it never observed the command return. Found by sending the lock a signal
# outside the trapped set, which reported `status=0 end=exited` — #344 again by a narrower route.
check "cause: the trap route is aborted, never exited" aborted "$(bl_end_cause 0 '' same trap)"
check "status: an aborted run with \$?=0 is not 0" 128 "$(bl_end_status 0 '' same trap)"
check "fields: the trap route" "status=128 end=aborted" "$(bl_end_fields 0 '' same trap)"

# A status the trap did observe is kept — only the uninformative 0 is replaced.
check "status: an aborted run keeps a nonzero \$?" 2 "$(bl_end_status 2 '' same trap)"
check "fields: an aborted run with a status" "status=2 end=aborted" "$(bl_end_fields 2 '' same trap)"

# A signal the lock did catch still outranks the route: the cause is known, so name it.
check "cause: a trapped signal beats the trap route" "launcher-signal(TERM)" \
  "$(bl_end_cause 0 15 same trap)"

# The default route is the normal one, so every three-argument call above is unaffected.
check "cause: the route defaults to normal" exited "$(bl_end_cause 0 '' same)"

# --- the launcher going away ------------------------------------------------

# "The wrapper went away" is the other half of #344 and the half no exit status can carry: the
# measured subtree can be killed while an intermediate wrapper exits 0, so the lock sees a clean
# completion. Reparenting is the observable: the parent the lock had at START is gone by END.
check "cause: the launcher vanished during the run" "exited" "$(bl_end_cause 0 '' changed)"
contains "fields: a vanished launcher is recorded" "launcher=gone" "$(bl_end_fields 0 '' changed)"
lacks "fields: a surviving launcher is not annotated" "launcher=gone" "$(bl_end_fields 0 '' same)"

# It is a note and not a status override, deliberately. The recommended discipline is to launch
# under `setsid`, which reparents the run to init on purpose, and a race between that reparenting
# and START would otherwise fail a perfectly good 1.5-hour measurement.
check "status: a vanished launcher alone does not fail the run" 0 "$(bl_end_status 0 '' changed)"

# --- bl_end_fields, the line the log actually gets --------------------------

# A completed run reads as one, and says so in a word rather than leaving it to be inferred from
# `status=0` — which is exactly the inference #344 made unsafe.
check "fields: a clean run" "status=0 end=exited" "$(bl_end_fields 0 '' same)"

# A launcher-killed run carries the forced status, the cause, and the child's own status, so
# nothing is lost by the override.
check "fields: a launcher-killed run keeps the child's status visible" \
  "status=143 end=launcher-signal(TERM) child=0" "$(bl_end_fields 0 15 same)"

# The budget stop the resource policy depends on being attributable.
check "fields: a budget stop" "status=124 end=budget" "$(bl_end_fields 124 '' same)"

# --- against the real script ------------------------------------------------

DIR="$(mktemp -d)"
trap 'rm -rf "$DIR"' EXIT

run_benchlock() { # <args...>  -- in an isolated lock directory
  ZEEBRA_BENCHLOCK_DIR="$DIR" bash "$BENCHLOCK" "$@"
}

log_line() { # <record>
  grep -E "  $1 " "$DIR/benchlock.log" | tail -1
}

# A command that succeeds is logged as having succeeded, with a cause.
run_benchlock t-ok true >/dev/null 2>&1
check_rc "real: a successful command exits 0" 0 $?
contains "real: a successful run records end=exited" "status=0 end=exited" "$(log_line END)"

# A failing command's status is passed through, which callers depend on.
run_benchlock t-fail sh -c 'exit 3' >/dev/null 2>&1
check_rc "real: a failing command's status is passed through" 3 $?
contains "real: a failing run records its status" "status=3 end=exited" "$(log_line END)"

# Three lines per invocation, still — the record shape five measurement protocols cite.
run_benchlock t-three true >/dev/null 2>&1
check "real: QUEUED, START and END are all present, once each" "1 1 1" \
  "$(grep -c '  QUEUED  *t-three ' "$DIR/benchlock.log") \
$(grep -c '  START  *t-three ' "$DIR/benchlock.log") \
$(grep -c '  END  *t-three ' "$DIR/benchlock.log")"

# --- the incident, end to end ----------------------------------------------

# The 3177s run reproduced: benchlock in its own session, a measured command whose wrapper
# swallows the kill and exits 0, and a signal to the whole process group — which is what stopping
# the launching shell does.
cat >"$DIR/inner.sh" <<'EOF'
#!/usr/bin/env bash
# Stands in for `bash n6run.sh`: the header is written, the binary under it dies, and the script
# exits 0 on its own last command because it has no `set -e`.
trap 'exit 0' TERM HUP INT
printf 'eleven header lines\n'
sleep 30
printf 'the stage table that never arrived\n'
EOF
chmod +x "$DIR/inner.sh"

rm -f "$DIR/benchlock.log"
setsid bash -c \
  "echo \$\$ >'$DIR/pid'; exec env ZEEBRA_BENCHLOCK_DIR='$DIR' bash '$BENCHLOCK' t-killed bash '$DIR/inner.sh'" \
  >"$DIR/killed.out" 2>&1 &

# Wait for START rather than sleeping a fixed time, so a loaded machine cannot make this flaky.
for _ in $(seq 1 100); do
  [ -s "$DIR/pid" ] && grep -q '  START ' "$DIR/benchlock.log" 2>/dev/null && break
  sleep 0.1
done
KILLED_PID="$(cat "$DIR/pid" 2>/dev/null)"
if [ -n "$KILLED_PID" ]; then
  kill -TERM -- "-$KILLED_PID" 2>/dev/null
  for _ in $(seq 1 100); do
    grep -q '  END ' "$DIR/benchlock.log" 2>/dev/null && break
    sleep 0.1
  done

  end="$(log_line END)"
  # The regression test for #344. Before the fix this line read `status=0`, so the lock reported a
  # completed measurement for a run that was killed 40 % of the way through its budget while
  # holding a serialized mutex three other agents were queued behind.
  lacks "incident: a killed run is not recorded as status=0" "status=0 " "$end"
  contains "incident: the END names the signal that ended it" "launcher-signal(TERM)" "$end"
  contains "incident: the child's own status stays visible" "child=0" "$end"
  # And the output file shows what the status used to be the only clue to.
  contains "incident: the measurement did not produce its table" "eleven header lines" "$(cat "$DIR/killed.out")"
  lacks "incident: ...and never reached the stage table" "the stage table that never arrived" "$(cat "$DIR/killed.out")"
else
  fail=$((fail + 1))
  printf 'FAIL  incident: the reproduction never started\n' >&2
fi

# --- the launcher going away, end to end -----------------------------------

# A launcher that exits while the run continues. Nothing is wrong with this run — it is what
# `setsid nohup ... &` produces on purpose — so the status must stay 0 and the fact must still be
# in the record, because it is the one observable for the half of #344 that no exit status reaches.
setsid bash -c \
  "ZEEBRA_BENCHLOCK_DIR='$DIR' bash '$BENCHLOCK' t-orphan sleep 3 & sleep 1; exit 0" \
  >/dev/null 2>&1
for _ in $(seq 1 100); do
  grep -q '  END  *t-orphan ' "$DIR/benchlock.log" 2>/dev/null && break
  sleep 0.2
done
orphan="$(log_line 'END  *t-orphan')"
contains "orphan: the vanished launcher is recorded" "launcher=gone" "$orphan"
contains "orphan: ...and the run is still a completed one" "status=0 end=exited" "$orphan"

# --- an untrapped signal, end to end ---------------------------------------

# USR1 is now in the trapped set; before it was, it reached the EXIT trap with `$?` of 0 and the
# log read `status=0 end=exited` for a lock that had been killed. Whichever way a later edit moves
# the trap set, this END must not claim the run completed.
setsid bash -c \
  "echo \$\$ >'$DIR/pid2'; exec env ZEEBRA_BENCHLOCK_DIR='$DIR' bash '$BENCHLOCK' t-usr1 sleep 20" \
  >/dev/null 2>&1 &
for _ in $(seq 1 100); do
  [ -s "$DIR/pid2" ] && grep -q '  START  *t-usr1 ' "$DIR/benchlock.log" 2>/dev/null && break
  sleep 0.1
done
USR1_PID="$(cat "$DIR/pid2" 2>/dev/null)"
if [ -n "$USR1_PID" ]; then
  kill -USR1 -- "-$USR1_PID" 2>/dev/null
  for _ in $(seq 1 100); do
    grep -q '  END  *t-usr1 ' "$DIR/benchlock.log" 2>/dev/null && break
    sleep 0.1
  done
  usr1="$(log_line 'END  *t-usr1')"
  lacks "usr1: a signalled lock is not recorded as a clean exit" "status=0 end=exited" "$usr1"
  lacks "usr1: ...and not as status=0 at all" "status=0 " "$usr1"
  contains "usr1: the END names a cause" "end=" "$usr1"
else
  fail=$((fail + 1))
  printf 'FAIL  usr1: the reproduction never started\n' >&2
fi

# --- usage -----------------------------------------------------------------

run_benchlock >/dev/null 2>&1
check_rc "real: no arguments is a usage error" 64 $?
run_benchlock owner-only >/dev/null 2>&1
check_rc "real: an owner with no command is a usage error" 64 $?

# --- the hazards the header must keep naming -------------------------------

# The header is the only place a caller learns the discipline, and each entry was added because it
# cost a re-run. A grep is crude but it is what survives a later edit.
for hazard in CARGO_TARGET_DIR RUSTC_WRAPPER 'pgrep' setsid; do
  if grep -q -- "$hazard" "$BENCHLOCK"; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    printf 'FAIL  the header no longer names the %s hazard\n' "$hazard" >&2
  fi
done

# ---------------------------------------------------------------------------

printf '\n%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
