#!/usr/bin/env bash
#
# Report how stale the base of a pull request's tested merge is, and whether the gap touches the
# same files the pull request does.
#
#   tools/merge-base-age.sh <tested-base-sha> <head-sha> <base-ref>
#
# GitHub Actions does test a merged result: a `pull_request` run checks out `refs/pull/N/merge`,
# whose first parent is the base. What it does not do is recompute that merge when the base moves —
# the run that produced a green check merged into `main` as it was, and nothing re-runs when `main`
# advances. So two pull requests can each be green against their own snapshot of `main` and be red
# once both have landed, which is #339: #324 added twelve rungs to `corpus::ladder()` and #311 added
# a test that matched exhaustively over the seven rungs that existed when it was written. Git saw no
# textual conflict because there was none.
#
# This is the detection half of "require branches to be up to date" at none of its cost. The gate
# would re-run the suite against the new base before every merge, which serializes merges behind a
# 13-minute job (see the README section "Testing the merged result"); this reports the gap and
# leaves the judgement to the caller.
#
# The `<behind>` count alone is a nag — on this repository it is nonzero nearly always. The signal
# worth acting on is the overlap: files this pull request changes that have *also* changed on the
# base since the merge was computed. That is where a semantic conflict can hide.
#
# Exit status, three outcomes rather than two (CLAUDE.md §0):
#
#   0   the tested merge base is the tip of <base-ref>; nothing is stale
#   1   behind, and no file this pull request touches changed in the gap
#   3   behind, and the gap overlaps this pull request's own files — the #339 shape
#   2   a git read FAILED. Not "current": a failed read that reported 0 would assert exactly the
#       thing this script exists to doubt
#   64  usage error
#
# Test seam, used by `tools/test/merge-base-age-test.sh` and not meant for callers:
# `ZEEBRA_MBA_GIT` replaces the `git` invocation, so the pure half is testable without a repository
# shaped like the case under test.

set -uo pipefail

# Resolved per call rather than once, so a test can substitute it after sourcing this file. Not
# `command`, so the seam accepts a shell function as well as a path.
mba_git() { "${ZEEBRA_MBA_GIT:-git}" "$@"; }

# The files changed between two commits, one per line, sorted. Returns 2 when the read fails, which
# is the whole reason this is a function: `git diff --name-only` writing nothing is indistinguishable
# from a diff of nothing at all.
mba_changed_files() { # <from> <to>
  local out
  out="$(mba_git diff --name-only "$1" "$2" 2>/dev/null)" || return 2
  printf '%s' "$out" | LC_ALL=C sort -u | grep -v '^$'
  return 0
}

# The number of commits <to> has that <from> does not. Returns 2 on a failed read rather than 0.
mba_behind_count() { # <from> <to>
  local out
  out="$(mba_git rev-list --count "$1..$2" 2>/dev/null)" || return 2
  case "$out" in
    '' | *[!0-9]*) return 2 ;;
  esac
  printf '%s' "$out"
  return 0
}

# The sorted intersection of two newline-separated file lists. Pure.
mba_overlap() { # <list-a> <list-b>
  LC_ALL=C comm -12 \
    <(printf '%s\n' "$1" | LC_ALL=C sort -u | grep -v '^$') \
    <(printf '%s\n' "$2" | LC_ALL=C sort -u | grep -v '^$')
}

# The verdict for a gap, as the exit status this script reports. Pure, and the only place the
# policy lives: behind-with-overlap is the case worth a warning, behind-without is a note.
mba_verdict() { # <behind-count> <overlap-count>
  case "$1" in
    '' | *[!0-9]*) return 2 ;;
  esac
  case "$2" in
    '' | *[!0-9]*) return 2 ;;
  esac
  [ "$1" -eq 0 ] && return 0
  [ "$2" -gt 0 ] && return 3
  return 1
}

# One line of Markdown summarising a gap, for a job summary. Pure.
mba_summary_line() { # <base-ref> <behind-count> <overlap-count>
  if [ "$2" -eq 0 ]; then
    printf 'The tested merge base is the tip of `%s`. Nothing has landed since this run was queued.\n' "$1"
  elif [ "$3" -eq 0 ]; then
    printf 'The tested merge base is **%s commit(s) behind `%s`**, and none of those commits touch a file this pull request changes.\n' "$2" "$1"
  else
    printf 'The tested merge base is **%s commit(s) behind `%s`**, and **%s file(s) this pull request changes also changed in that gap**. A green check here does not cover the combination — rebase and let CI re-run before merging.\n' "$2" "$1" "$3"
  fi
}

mba_usage() {
  cat >&2 <<'USAGE'
usage: tools/merge-base-age.sh <tested-base-sha> <head-sha> <base-ref>

Reports how far the base of the tested merge is behind <base-ref>, and which of the pull request's
own files changed in that gap.

  0 current   1 behind   3 behind and overlapping   2 a git read failed   64 usage
USAGE
}

mba_main() {
  if [ "$#" -ne 3 ]; then
    mba_usage
    return 64
  fi

  local tested_base="$1" head="$2" base_ref="$3"
  local tip behind pr_files gap_files overlap overlap_count status

  tip="$(mba_git rev-parse "$base_ref" 2>/dev/null)" || {
    printf 'merge-base-age: READ FAILED — could not resolve %s\n' "$base_ref" >&2
    return 2
  }

  behind="$(mba_behind_count "$tested_base" "$tip")" || {
    printf 'merge-base-age: READ FAILED — could not count %s..%s\n' "$tested_base" "$tip" >&2
    return 2
  }

  # Against the tested base rather than against the tip: the tested base is the commit this run's
  # merge was actually computed from, so this is the pull request's own change set and not the
  # union of it with everything that has landed since.
  pr_files="$(mba_changed_files "$tested_base" "$head")" || {
    printf 'merge-base-age: READ FAILED — could not diff %s..%s\n' "$tested_base" "$head" >&2
    return 2
  }

  if [ "$behind" -eq 0 ]; then
    gap_files=""
  else
    gap_files="$(mba_changed_files "$tested_base" "$tip")" || {
      printf 'merge-base-age: READ FAILED — could not diff %s..%s\n' "$tested_base" "$tip" >&2
      return 2
    }
  fi

  overlap="$(mba_overlap "$pr_files" "$gap_files")"
  overlap_count="$(printf '%s' "$overlap" | grep -c . || true)"

  mba_summary_line "$base_ref" "$behind" "$overlap_count"
  if [ "$overlap_count" -gt 0 ]; then
    printf '\nFiles changed on both sides:\n\n'
    printf '%s\n' "$overlap" | sed 's/^/  - `/; s/$/`/'
  fi

  mba_verdict "$behind" "$overlap_count"
  status=$?
  return "$status"
}

if [ "${BASH_SOURCE[0]}" = "${0}" ]; then
  mba_main "$@"
fi
