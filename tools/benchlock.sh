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
# gets it, END with the exit status. Two records whose START..END windows overlap were not taken
# under this protocol, and the log says so. The command's exit status is passed through, so a
# failing measurement fails the caller.
#
#   ZEEBRA_BENCHLOCK_DIR   where the lock and the log live (default `$HOME/.zeebra`). It must be
#                          outside every worktree: a per-checkout lock serializes nothing, and a
#                          log that a branch switch can remove is not an audit trail.
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
#
# So a real invocation looks like
#
#   tools/benchlock.sh agentD env CARGO_TARGET_DIR="$PWD/target" RUSTC_WRAPPER="" \
#     timeout --signal=INT --kill-after=60s 1200 \
#     taskset --cpu-list 8 ./target/release/examples/univariate_scaling koalabear budget=1.0

set -euo pipefail

if [ "$#" -lt 2 ]; then
    cat >&2 <<'USAGE'
usage: tools/benchlock.sh <owner-tag> <command> [args...]

Runs <command> under an exclusive machine-wide benchmark lock, logging QUEUED / START / END
against <owner-tag> and exiting with the command's status.
USAGE
    exit 64
fi

OWNER="$1"
shift
COMMAND_LINE="$*"

STATE_DIR="${ZEEBRA_BENCHLOCK_DIR:-$HOME/.zeebra}"
mkdir -p "$STATE_DIR"
LOCK_FILE="$STATE_DIR/benchlock.lock"
LOG_FILE="$STATE_DIR/benchlock.log"

# One `printf` per line to a file opened `O_APPEND`, so concurrent writers cannot interleave a
# line. The writers are not all holding the lock — a queued caller logs before it has one.
note() {
    printf '%s  %-7s  %-14s  pid=%-7d  %s\n' \
        "$(date --iso-8601=seconds)" "$1" "$OWNER" "$$" "$2" >>"$LOG_FILE"
}

STARTED_AT=0
ENDED=0

# An invocation that dies holding the lock must still leave an END, or the log would show an
# unterminated window and every later record would look like it overlapped.
# shellcheck disable=SC2329  # invoked from the EXIT trap below
on_exit() {
    local status=$?
    if [ "$ENDED" -eq 0 ] && [ "$STARTED_AT" -ne 0 ]; then
        note END "status=$status(aborted) elapsed=$(($(date +%s) - STARTED_AT))s $COMMAND_LINE"
    fi
    return "$status"
}
trap on_exit EXIT

exec 9>"$LOCK_FILE"

QUEUED_AT=$(date +%s)
note QUEUED "$COMMAND_LINE"
flock 9

STARTED_AT=$(date +%s)
note START "waited=$((STARTED_AT - QUEUED_AT))s $COMMAND_LINE"

STATUS=0
"$@" || STATUS=$?

ENDED=1
note END "status=$STATUS elapsed=$(($(date +%s) - STARTED_AT))s $COMMAND_LINE"
exit "$STATUS"
