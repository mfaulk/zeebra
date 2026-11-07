#!/usr/bin/env bash
#
# Serialize benchmark runs on this machine, and record that they were serialized.
#
#   tools/benchlock.sh <owner-tag> <command> [args...]
#
# This workstation runs many agents at once, and its shared L3 and memory bandwidth mean two
# concurrent measurements contaminate each other. Every ratio in `docs/` was taken while nothing
# else ran; the log this script appends to is what makes that claim checkable after the fact, and
# what makes two figures taken weeks apart — the pre- and post-#161 revisions in
# `docs/research/graeffe-root-finding.md` §4.4, say — comparable with each other.
#
# Three lines go to the log per invocation: QUEUED when the caller asks for the lock, START when it
# gets it, END with the exit status and **why the run ended**. Two records whose START..END windows
# overlap were not taken under this protocol, and the log says so. The command's exit status is
# passed through, so a failing measurement fails the caller.
#
#   ZEEBRA_BENCHLOCK_DIR   where the lock and the log live (default `$HOME/.zeebra`). It must be
#                          outside every worktree: a per-checkout lock serializes nothing, and a
#                          log that a branch switch can remove is not an audit trail.
#
# An END that cannot distinguish its own cause (#344). An `END status=0` used to be the only
# evidence that a measurement completed, and it could not carry that weight: a 1.5-hour Anemoi run
# was killed at 3 177 s of a 5 400 s budget when the shell that launched it was stopped, and the log
# recorded `END status=0 elapsed=3177s`. From the lock's side the measurement had simply finished.
# The only way to know otherwise was that the output file held eleven header lines and no stage
# table. That made **every** historical `END status=0` retroactively ambiguous, which matters
# because the §9 resource policy authorizes bounded runs precisely on the grounds that a budget stop
# is observable and attributable — and it cannot be, if a budget stop and an unrelated kill look the
# same in the log.
#
# So END names the cause, and `end=exited` rather than `status=0` is what asserts completion:
#
#   end=exited                   the command ran and returned on its own; status= is its status
#   end=budget                   status 124, GNU timeout's convention — a resource-attributed stop
#   end=signalled-child(NAME)    the command itself died of a signal; status= is 128+n
#   end=launcher-signal(NAME)    THE LOCK ITSELF was signalled. status= is forced to 128+n however
#                                the command exited, and `child=` keeps the command's own status
#                                visible. In the incident above the child reported 0, because an
#                                intermediate `bash run.sh` with no `set -e` exited on its own last
#                                command after the binary beneath it had died
#   launcher=gone                the process that launched this lock is no longer this process's
#                                parent, so the run outlived its launcher. A note and not a status
#                                override, because `setsid` reparents a run to init deliberately
#   route=trap                   the END was written from the EXIT trap rather than from the end of
#                                the script, so the lock did not reach its own last line
#
# A signal that arrives while a caller is still **queued** leaves a QUEUED line and no END, which
# is correct: no START means no window was opened, so nothing later can look like it overlapped.
#
# Companion hazards. The lock does not handle any of these, and each has cost a re-run:
#
#   * `CARGO_TARGET_DIR` per invocation, inside the caller's own worktree. The shared default is
#     keyed by package and profile rather than by checkout, so two worktrees overwrite each other's
#     `libzeebra.rlib` and an example links against a library built from other source. The symptom
#     is a missing export that is plainly present.
#   * `RUSTC_WRAPPER=""`. With sccache in the wrapper slot a stale rlib is served from the cache,
#     which is the same failure by another route.
#   * A private scratch directory per caller. Two callers' `tee run1.txt` collide, and a clobbered
#     `tee` is a silently wrong figure rather than a crash.
#   * `timeout --signal=INT --kill-after=60s` on anything long, and a budget-killed run reported as
#     a resource-limited result rather than as a measurement. A run killed while holding the lock
#     still releases it; one left running past its budget blocks every other agent.
#   * Never `pgrep -f` to find the binary you are watching. A script created and run through a
#     heredoc inside `bash -c` has its entire text in the wrapper's `/proc/<pid>/cmdline`, so
#     `pgrep -f` matches the wrapper on its own payload: it returns `comm=bash` pids for a job that
#     has not started and does not return the measured binary at all. A monitor reading those pids
#     reports queued work as running, and an RSS guard reading them sees a ~4 MB high-water mark
#     and silently never fires. Use `tools/rss-guard.sh`, which matches `comm` and confirms the
#     identity from cmdline, or capture the pid from `$!` when the launcher and the guard are the
#     same script.
#   * **Launch under `setsid`, so the run survives its launcher.** A backgrounded shell takes its
#     whole process tree with it when something stops it — the lock, `timeout`, `taskset` and the
#     measured binary are all its descendants — and an agent harness stopping a background task is
#     enough to do it. That is how 53 minutes of a serialized mutex, with three other agents queued
#     behind it, were spent on a run that then reported success (#344).
#
#         setsid nohup bash run.sh > log 2>&1 < /dev/null &
#
#     Confirm it took by checking that the session id differs from the launching shell's:
#     `ps -o pid=,sid= -p "$!"`. The lock does **not** call `setsid` itself: a detached run that
#     nobody can cancel is its own hazard, and that trade is worse than the one it would fix. What
#     the lock does instead is notice, and record `launcher=gone`.
#   * `.cargo/config.toml` is not inherited by a crate built outside this worktree (#352). A harness
#     crate elsewhere that depends on `zeebra` by path gets neither `-C target-cpu=x86-64-v3` nor
#     `lto = "fat"` nor `codegen-units = 1`, because cargo resolves config from the invocation
#     directory upward and the profile comes from the crate being built. This hazard has **no
#     trigger to avoid**: `RUSTFLAGS` need never be set for it to happen, the build succeeds, the
#     tests pass and the numbers are self-consistent. It was worth 2.80x on an order-1 458
#     determinant. Copy `.cargo/config.toml` and the profile into the harness crate, or pass the
#     settings with `--config` on its invocation; see the README section "Build configuration".
#
# So a real invocation looks like
#
#   tools/benchlock.sh agentD env CARGO_TARGET_DIR="$PWD/target" RUSTC_WRAPPER="" \
#     timeout --signal=INT --kill-after=60s 1200 \
#     taskset --cpu-list 8 ./target/release/examples/univariate_scaling koalabear budget=1.0
#
# Test seam, used by `tools/test/benchlock-test.sh` and not meant for callers:
# `ZEEBRA_BENCHLOCK_PROC` relocates `/proc`.

# Deliberately not `set -e`: the file is sourced by its tests, and the executed path checks the
# commands whose failure matters by hand rather than relying on an option that interacts badly with
# both functions and traps.
set -uo pipefail

# ---------------------------------------------------------------------------------------------
# The pure half: what an END line says, and why.
# ---------------------------------------------------------------------------------------------

# Named rather than numbered in the log, because a reader of an audit trail is asking "was this
# killed", and 143 does not say so.
bl_signal_name() { # <signum>
  case "$1" in
    1) printf 'HUP' ;;
    2) printf 'INT' ;;
    3) printf 'QUIT' ;;
    9) printf 'KILL' ;;
    15) printf 'TERM' ;;
    *) printf 'signal %s' "$1" ;;
  esac
}

# Why the run ended. The only place the classification lives.
#
# A signal to the lock outranks everything the command reported: if this process was signalled then
# the run did not complete, whatever exit status reached it through the wrappers in between.
bl_end_cause() { # <child-status> <signalled-signum-or-empty> <launcher-state>
  if [ -n "$2" ]; then
    printf 'launcher-signal(%s)' "$(bl_signal_name "$2")"
    return 0
  fi
  if [ "$1" = 124 ]; then
    printf 'budget'
    return 0
  fi
  case "$1" in
    '' | *[!0-9]*) printf 'exited'; return 0 ;;
  esac
  if [ "$1" -gt 128 ] && [ "$1" -le 255 ]; then
    printf 'signalled-child(%s)' "$(bl_signal_name "$(($1 - 128))")"
    return 0
  fi
  printf 'exited'
}

# The status to record and to exit with.
#
# The whole of #344 in one rule: a run whose lock was signalled is never recorded as 0. 128+n is the
# conventional encoding, so a reader who knows nothing about this script still sees a kill.
bl_end_status() { # <child-status> <signalled-signum-or-empty> <launcher-state>
  if [ -n "$2" ]; then
    printf '%s' "$((128 + $2))"
    return 0
  fi
  printf '%s' "$1"
}

# The fields an END line carries, in the order a reader greps for them.
bl_end_fields() { # <child-status> <signalled-signum-or-empty> <launcher-state>
  printf 'status=%s end=%s' \
    "$(bl_end_status "$1" "$2" "$3")" "$(bl_end_cause "$1" "$2" "$3")"
  # The command's own status, kept when the override has displaced it so nothing is lost.
  if [ -n "$2" ]; then
    printf ' child=%s' "$1"
  fi
  # The run outlived its launcher. Not a failure: `setsid` causes this on purpose, and using it is
  # the recommended discipline.
  if [ "$3" = changed ]; then
    printf ' launcher=gone'
  fi
  return 0
}

# This process's parent, from `/proc`. Returns 2 on a failed read rather than a plausible number,
# so an unreadable `/proc` cannot be mistaken for a launcher that is still there.
bl_ppid() {
  local stat
  read -r stat <"${ZEEBRA_BENCHLOCK_PROC:-/proc}/$$/stat" 2>/dev/null || return 2
  # Field 2 of `stat` is the command in parentheses and may itself contain spaces and parentheses,
  # so the fields are counted from after the last `)`: state, then ppid.
  stat="${stat##*) }"
  # shellcheck disable=SC2086  # deliberate word splitting, to index the fields
  set -- $stat
  [ "$#" -ge 2 ] || return 2
  printf '%s' "$2"
}

# ---------------------------------------------------------------------------------------------
# The imperative half. State is global rather than local to `bl_main`, because the EXIT trap runs
# after `bl_main` has returned and a local would be gone by then — leaving the trap to write an END
# from variables that no longer exist.
# ---------------------------------------------------------------------------------------------

BL_OWNER=""
BL_COMMAND_LINE=""
BL_LOG_FILE=""
BL_STARTED_AT=0
BL_ENDED=0
BL_SIGNALLED=""
BL_LAUNCH_PPID=""

# One `printf` per line to a file opened `O_APPEND`, so concurrent writers cannot interleave a line.
# The writers are not all holding the lock — a queued caller logs before it has one.
bl_note() { # <record> <detail>
  printf '%s  %-7s  %-14s  pid=%-7d  %s\n' \
    "$(date --iso-8601=seconds)" "$1" "$BL_OWNER" "$$" "$2" >>"$BL_LOG_FILE"
}

# shellcheck disable=SC2329  # invoked from the signal traps in bl_main
bl_on_signal() { # <signum>
  BL_SIGNALLED="$1"
}

# Whether the process that launched this run is still its parent. `unknown` when it cannot be
# determined, which is not the same claim as `same`.
bl_launcher_state() {
  local now
  [ -n "$BL_LAUNCH_PPID" ] || { printf 'unknown'; return 0; }
  now="$(bl_ppid)" || { printf 'unknown'; return 0; }
  if [ "$now" = "$BL_LAUNCH_PPID" ]; then printf 'same'; else printf 'changed'; fi
}

# An invocation that dies holding the lock must still leave an END, or the log would show an
# unterminated window and every later record would look like it overlapped. `route=trap` marks that
# this END came from here rather than from the end of the script, so the two are not the same claim.
# shellcheck disable=SC2329  # invoked from the EXIT trap in bl_main
bl_on_exit() {
  local status=$?
  if [ "$BL_ENDED" -eq 0 ] && [ "$BL_STARTED_AT" -ne 0 ]; then
    bl_note END "$(bl_end_fields "$status" "$BL_SIGNALLED" "$(bl_launcher_state)") route=trap elapsed=$(($(date +%s) - BL_STARTED_AT))s $BL_COMMAND_LINE"
  fi
  return "$status"
}

bl_usage() {
  cat >&2 <<'USAGE'
usage: tools/benchlock.sh <owner-tag> <command> [args...]

Runs <command> under an exclusive machine-wide benchmark lock, logging QUEUED / START / END
against <owner-tag> and exiting with the command's status. The END line names why the run ended;
`end=exited` and not `status=0` is what says a measurement completed.
USAGE
}

bl_main() {
  if [ "$#" -lt 2 ]; then
    bl_usage
    return 64
  fi

  BL_OWNER="$1"
  shift
  BL_COMMAND_LINE="$*"

  local state_dir="${ZEEBRA_BENCHLOCK_DIR:-$HOME/.zeebra}"
  mkdir -p "$state_dir" || {
    printf 'benchlock: cannot create %s\n' "$state_dir" >&2
    return 2
  }
  BL_LOG_FILE="$state_dir/benchlock.log"
  local lock_file="$state_dir/benchlock.lock"

  # Trapped rather than fatal, so a signal to this process leaves an honest END instead of killing
  # the lock before it can write one. Bash defers a trap until the foreground child returns, so the
  # handler runs between the command finishing and the END line being composed — which is exactly
  # where the knowledge that this process was signalled is needed.
  trap 'bl_on_signal 1' HUP
  trap 'bl_on_signal 2' INT
  trap 'bl_on_signal 3' QUIT
  trap 'bl_on_signal 15' TERM
  trap bl_on_exit EXIT

  exec 9>"$lock_file" || {
    printf 'benchlock: cannot open %s\n' "$lock_file" >&2
    return 2
  }

  local queued_at
  queued_at=$(date +%s)
  bl_note QUEUED "$BL_COMMAND_LINE"
  flock 9 || {
    printf 'benchlock: did not acquire the lock\n' >&2
    return 2
  }

  BL_STARTED_AT=$(date +%s)
  # Captured at START and not before: `setsid nohup ... &` reparents the run to init immediately,
  # so a launcher read any earlier would be the one that was always going to go away.
  BL_LAUNCH_PPID="$(bl_ppid)" || BL_LAUNCH_PPID=""
  bl_note START "waited=$((BL_STARTED_AT - queued_at))s $BL_COMMAND_LINE"

  local child_status=0
  "$@" || child_status=$?

  BL_ENDED=1
  bl_note END "$(bl_end_fields "$child_status" "$BL_SIGNALLED" "$(bl_launcher_state)") elapsed=$(($(date +%s) - BL_STARTED_AT))s $BL_COMMAND_LINE"
  return "$(bl_end_status "$child_status" "$BL_SIGNALLED" same)"
}

if [ "${BASH_SOURCE[0]}" = "${0}" ]; then
  bl_main "$@"
  exit $?
fi
