#!/usr/bin/env bash
#
# Terminate a measurement that crosses a memory ceiling, watching the binary rather than a wrapper.
#
#   tools/rss-guard.sh <comm> <id-substring> <ceiling-kb> [--poll <seconds>] [--once]
#                      [--signal <name>] [--kill-pid <pid>] [--dry-run]
#
# `<comm>` is the binary's process name as `/proc/<pid>/comm` spells it — `anemoi_ladder`, not a
# path and not the command line. `<id-substring>` is then confirmed against that pid's cmdline, so
# a second concurrent run of the same binary on a different row is not watched.
#
# Why not `pgrep -f`, which is the obvious thing (#328): when a benchmark script is created and run
# through a heredoc inside `bash -c`, the entire script text lands in the wrapper's
# `/proc/<pid>/cmdline`. `pgrep -f` matches the full command line, so it matches the wrapper on its
# own payload — returning `comm=bash` pids for a job that has not started, and not returning the
# real binary at all. A guard reading those pids sees a ~4 MB high-water mark, never fires however
# large the measured process grows, and looks exactly like a guard that works. Matching on `comm`
# and confirming from cmdline is the minimum that cannot do that; wrapper names are refused
# outright. If the launcher and the guard are in the same script, prefer neither and pass the pid
# you captured from `$!`.
#
# Exit status, which is the point of the three-way split:
#
#   0   watched to completion, the ceiling was never crossed
#   3   the ceiling was crossed and the signal was sent
#   1   NO PROCESS MATCHED — nothing was guarded. Not a pass: a run that proceeded unsupervised
#       is the failure mode #328 describes, and it must not be reported as a clean one
#   2   a read of /proc failed
#   64  usage error
#
# Test seams, used by `tools/test/rss-guard-test.sh` and not meant for callers:
# `ZEEBRA_RSS_GUARD_PROC` relocates `/proc`, `ZEEBRA_RSS_GUARD_PIDS` supplies the candidate pids in
# place of `pgrep`.

set -uo pipefail

# Resolved per call rather than once, so a test can relocate it after sourcing this file.
guard_proc() { printf '%s' "${ZEEBRA_RSS_GUARD_PROC:-/proc}"; }

# Wrappers whose cmdline carries their payload, and whose own footprint says nothing about the
# measurement. Watching one of these is the defect, not a configuration.
GUARD_WRAPPER_NAMES="bash sh dash zsh ksh env timeout taskset flock nice ionice stdbuf sudo"

# `/proc/<pid>/comm` is truncated to 15 characters, so a longer binary name must be truncated the
# same way before it is compared.
guard_comm_key() { # <comm>
  printf '%.15s' "$1"
}

# True if the name belongs to a wrapper rather than to a measured binary.
guard_is_wrapper_name() { # <comm>
  local name
  for name in $GUARD_WRAPPER_NAMES; do
    [ "$1" = "$name" ] && return 0
  done
  return 1
}

# True if <pid>'s command line contains <id-substring>. `grep -a` because a cmdline is
# NUL-separated and would otherwise read as binary.
guard_confirms_id() { # <pid> <id-substring>
  [ -r "$(guard_proc)/$1/cmdline" ] || return 1
  grep -qa -- "$2" "$(guard_proc)/$1/cmdline" 2>/dev/null
}

# <pid>'s peak resident set in kB, from VmHWM. The high-water mark rather than VmRSS: a peak that
# has since been released still breached the ceiling.
guard_hwm_kb() { # <pid>
  local hwm
  hwm="$(awk '/^VmHWM:/{print $2}' "$(guard_proc)/$1/status" 2>/dev/null)"
  [ -n "$hwm" ] || return 2
  printf '%s' "$hwm"
}

# The pids whose comm is <comm> and whose cmdline confirms <id-substring>.
guard_matching_pids() { # <comm> <id-substring>
  local key candidates pid comm
  key="$(guard_comm_key "$1")"
  if [ -n "${ZEEBRA_RSS_GUARD_PIDS:-}" ]; then
    candidates="$ZEEBRA_RSS_GUARD_PIDS"
  else
    candidates="$(pgrep -x "$key" 2>/dev/null)"
  fi
  for pid in $candidates; do
    comm="$(cat "$(guard_proc)/$pid/comm" 2>/dev/null)" || continue
    [ "$comm" = "$key" ] || continue
    guard_confirms_id "$pid" "$2" || continue
    printf '%s\n' "$pid"
  done
}

# One pass over the matching processes. Returns 3 if the ceiling was crossed, 1 if nothing matched,
# 2 if a matched pid's status could not be read, else 0.
guard_scan() { # <comm> <id-substring> <ceiling-kb> [--dry-run] [--signal <name>] [--kill-pid <pid>]
  local comm="$1" id="$2" ceiling="$3"
  shift 3
  local dry_run=0 signal="INT" kill_pid=""
  while [ "$#" -gt 0 ]; do
    case "$1" in
      --dry-run) dry_run=1 ;;
      --signal) signal="$2"; shift ;;
      --kill-pid) kill_pid="$2"; shift ;;
      *) printf 'rss-guard: unknown scan option %s\n' "$1" >&2; return 64 ;;
    esac
    shift
  done

  local matched=0 fired=0 pid hwm
  for pid in $(guard_matching_pids "$comm" "$id"); do
    matched=1
    hwm="$(guard_hwm_kb "$pid")" || return 2
    if [ "$hwm" -gt "$ceiling" ]; then
      printf 'OVER pid=%s hwm_kb=%s ceiling_kb=%s\n' "$pid" "$hwm" "$ceiling"
      fired=1
      if [ "$dry_run" -eq 0 ]; then
        kill "-$signal" "${kill_pid:-$pid}" 2>/dev/null ||
          printf 'rss-guard: could not signal %s\n' "${kill_pid:-$pid}" >&2
      fi
    fi
  done

  [ "$fired" -eq 1 ] && return 3
  [ "$matched" -eq 1 ] && return 0
  return 1
}

guard_usage() {
  cat >&2 <<'USAGE'
usage: tools/rss-guard.sh <comm> <id-substring> <ceiling-kb>
                          [--poll <seconds>] [--once] [--signal <name>]
                          [--kill-pid <pid>] [--dry-run]

Watches the process whose /proc/<pid>/comm is <comm> and whose cmdline contains <id-substring>,
and signals it when VmHWM exceeds <ceiling-kb>.

  0 clean   3 ceiling crossed and signalled   1 nothing matched   2 /proc read failed   64 usage
USAGE
}

guard_main() {
  if [ "$#" -lt 3 ]; then
    guard_usage
    return 64
  fi

  local comm="$1" id="$2" ceiling="$3"
  shift 3

  if guard_is_wrapper_name "$comm"; then
    printf 'rss-guard: %s is a wrapper name, not a measured binary.\n' "$comm" >&2
    printf 'rss-guard: a wrapper reports its own footprint, so guarding one guards nothing.\n' >&2
    return 64
  fi
  case "$ceiling" in
    '' | *[!0-9]*) printf 'rss-guard: ceiling must be a count of kB, got %q\n' "$ceiling" >&2; return 64 ;;
  esac

  local poll=5 once=0 wait_limit=60 scan_options=()
  while [ "$#" -gt 0 ]; do
    case "$1" in
      --poll) poll="$2"; shift ;;
      --wait) wait_limit="$2"; shift ;;
      --once) once=1 ;;
      --dry-run) scan_options+=(--dry-run) ;;
      --signal) scan_options+=(--signal "$2"); shift ;;
      --kill-pid) scan_options+=(--kill-pid "$2"); shift ;;
      -h | --help) guard_usage; return 0 ;;
      *) printf 'rss-guard: unknown option %s\n' "$1" >&2; guard_usage; return 64 ;;
    esac
    shift
  done

  local status ever_matched=0 waited=0
  while :; do
    guard_scan "$comm" "$id" "$ceiling" "${scan_options[@]+"${scan_options[@]}"}"
    status=$?
    case $status in
      0) ever_matched=1 ;;
      3) return 3 ;;
      2 | 64) return $status ;;
      1)
        # Matched earlier and no longer matches: the run finished under the ceiling.
        [ "$ever_matched" -eq 1 ] && return 0
        # Never matched. The guard may legitimately have started before the binary, so it waits —
        # but only for a bounded time, because the alternative is a supervisor that polls an empty
        # process table forever and exits reporting a clean run it never observed.
        if [ "$once" -eq 1 ] || [ "$waited" -ge "$wait_limit" ]; then
          printf 'rss-guard: NOT GUARDED — no process named %q with %q in its command line' \
            "$comm" "$id" >&2
          printf ' after %ss.\n' "$waited" >&2
          return 1
        fi
        ;;
    esac
    [ "$once" -eq 1 ] && return $status
    sleep "$poll"
    waited=$((waited + poll))
  done
}

if [ "${BASH_SOURCE[0]}" = "${0}" ]; then
  guard_main "$@"
fi
