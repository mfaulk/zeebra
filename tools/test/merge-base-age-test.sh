#!/usr/bin/env bash
# Unit tests for tools/merge-base-age.sh, over a real repository built to the shape of #339.
#
# The git reads are exercised against a throwaway repository rather than mocked: what the script
# has to get right is which pair of commits it diffs, and a mock would pin the mock rather than
# that choice. The failure-path tests use the `ZEEBRA_MBA_GIT` seam, because a git that fails is
# the one state a healthy repository cannot produce on demand.
set -uo pipefail

MBA="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/merge-base-age.sh"
# shellcheck source=../merge-base-age.sh
. "$MBA"

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

# --- mba_verdict, the policy -----------------------------------------------

# A merge base that is the tip of the base branch is current, whatever the overlap count says:
# there is no gap for a conflict to hide in.
mba_verdict 0 0; check_rc "verdict: at the tip is current" 0 $?
mba_verdict 0 7; check_rc "verdict: at the tip is current even with files in common" 0 $?

# Behind with no overlapping file is a note, not a warning. On this repository main advances every
# few minutes, so a bare behind-count would warn on nearly every pull request and be ignored.
mba_verdict 9 0; check_rc "verdict: behind with no overlap is a note" 1 $?

# Behind *and* overlapping is the #339 shape — two pull requests each green against their own
# snapshot of main, touching the same file, red once combined.
mba_verdict 1 1; check_rc "verdict: behind and overlapping warns" 3 $?
mba_verdict 40 3; check_rc "verdict: far behind and overlapping warns" 3 $?

# A count that is not a count is a read that failed somewhere upstream, and must not resolve to
# "current" (CLAUDE.md §0).
mba_verdict "" 0; check_rc "verdict: an empty behind-count is a failed read" 2 $?
mba_verdict x 0; check_rc "verdict: a non-numeric behind-count is a failed read" 2 $?
mba_verdict 3 ""; check_rc "verdict: an empty overlap-count is a failed read" 2 $?

# --- mba_overlap, the intersection -----------------------------------------

# Only files on both sides are reported, and the result is sorted so the output is stable.
check "overlap: common files only" "src/b.rs
src/c.rs" "$(mba_overlap 'src/a.rs
src/c.rs
src/b.rs' 'src/c.rs
src/b.rs
src/d.rs')"

# Disjoint change sets are the common, uninteresting case and must produce nothing.
check "overlap: disjoint sets are empty" "" "$(mba_overlap 'src/a.rs' 'src/b.rs')"

# An empty side cannot manufacture an overlap, which is what makes the behind=0 path safe.
check "overlap: an empty gap is empty" "" "$(mba_overlap 'src/a.rs' '')"
check "overlap: an empty pull request is empty" "" "$(mba_overlap '' 'src/a.rs')"

# --- mba_summary_line ------------------------------------------------------

# The three messages are distinguishable, and only the overlapping one tells the reader to rebase.
case "$(mba_summary_line main 0 0)" in
  *"is the tip of"*) pass=$((pass + 1)) ;;
  *) fail=$((fail + 1)); printf 'FAIL  summary: current case does not say so\n' >&2 ;;
esac
case "$(mba_summary_line main 9 0)" in
  *"9 commit(s) behind"*"none of those commits touch"*) pass=$((pass + 1)) ;;
  *) fail=$((fail + 1)); printf 'FAIL  summary: behind-without-overlap case is wrong\n' >&2 ;;
esac
case "$(mba_summary_line main 9 2)" in
  *"2 file(s)"*"rebase and let CI re-run"*) pass=$((pass + 1)) ;;
  *) fail=$((fail + 1)); printf 'FAIL  summary: overlapping case does not say to rebase\n' >&2 ;;
esac

# --- against a real repository ---------------------------------------------

REPO="$(mktemp -d)"
trap 'rm -rf "$REPO"' EXIT

git -C "$REPO" init -q -b main
git -C "$REPO" config user.email t@example.com
git -C "$REPO" config user.name test

commit() { # <file> <content> <message>
  printf '%s\n' "$2" >"$REPO/$1"
  git -C "$REPO" add "$1"
  git -C "$REPO" commit -qm "$3"
}

# The base both pull requests branch from.
commit ladder.rs "rungs: 7" "base"
BASE="$(git -C "$REPO" rev-parse HEAD)"

# One pull request, branched from BASE, that edits the shared file — #311's shape.
git -C "$REPO" checkout -q -b pr-311
commit ladder.rs "match over 7 rungs" "pr-311 edits the ladder"
PR_311="$(git -C "$REPO" rev-parse HEAD)"

# Another pull request, branched from the same BASE, touching an unrelated file.
git -C "$REPO" checkout -q -b pr-other "$BASE"
commit unrelated.rs "nothing to do with the ladder" "pr-other edits elsewhere"
PR_OTHER="$(git -C "$REPO" rev-parse HEAD)"

# ...and main advances with #324's change to the shared file, which is what makes the
# already-computed merge for pr-311 stale in a way that matters.
git -C "$REPO" checkout -q main
commit ladder.rs "rungs: 19" "pr-324 lands on main"
commit notes.md "unrelated main commit" "a second main commit"

run_mba() { # <tested-base> <head> <base-ref>
  ( cd "$REPO" && bash "$MBA" "$1" "$2" "$3" )
}

# Nothing has landed since the merge was computed: the tested base is main's tip.
out="$(run_mba "$(git -C "$REPO" rev-parse main)" "$PR_311" main 2>&1)"; rc=$?
check_rc "real repo: a merge base at main's tip exits 0" 0 "$rc"
case "$out" in *"is the tip of"*) pass=$((pass + 1)) ;;
  *) fail=$((fail + 1)); printf 'FAIL  real repo: current case message was %q\n' "$out" >&2 ;;
esac

# The #339 case itself: pr-311's merge was computed against BASE, main has since moved, and the
# commits in the gap touch the very file pr-311 edits. This must be the loud outcome.
out="$(run_mba "$BASE" "$PR_311" main 2>&1)"; rc=$?
check_rc "real repo: behind and overlapping exits 3" 3 "$rc"
case "$out" in *"2 commit(s) behind"*"ladder.rs"*) pass=$((pass + 1)) ;;
  *) fail=$((fail + 1)); printf 'FAIL  real repo: overlap output was %q\n' "$out" >&2 ;;
esac

# The common case: equally stale, but the gap and the pull request have no file in common. A
# behind-count on its own must not be reported as a risk, or the signal is lost in the noise.
out="$(run_mba "$BASE" "$PR_OTHER" main 2>&1)"; rc=$?
check_rc "real repo: behind without overlap exits 1" 1 "$rc"
case "$out" in *"none of those commits touch"*) pass=$((pass + 1)) ;;
  *) fail=$((fail + 1)); printf 'FAIL  real repo: no-overlap output was %q\n' "$out" >&2 ;;
esac

# The staleness is measured against the base branch's *current* tip, not against whatever ref the
# run was triggered on, so the same pull request reports differently as main advances.
commit ladder.rs "rungs: 20" "a third main commit"
out="$(run_mba "$BASE" "$PR_311" main 2>&1)"; rc=$?
check_rc "real repo: still exits 3 after main advances again" 3 "$rc"
case "$out" in *"3 commit(s) behind"*) pass=$((pass + 1)) ;;
  *) fail=$((fail + 1)); printf 'FAIL  real repo: count did not follow main, output %q\n' "$out" >&2 ;;
esac

# --- the failure path ------------------------------------------------------

# A git that cannot answer must exit 2. This is the case the whole three-outcome discipline is for:
# an unauthenticated or broken read that printed nothing and exited 0 would be reported as "the
# merge base is current", which is the one conclusion it cannot support.
FAKE_GIT="$REPO/failing-git"
cat >"$FAKE_GIT" <<'EOF'
#!/usr/bin/env bash
exit 1
EOF
chmod +x "$FAKE_GIT"
out="$(ZEEBRA_MBA_GIT="$FAKE_GIT" run_mba "$BASE" "$PR_311" main 2>&1)"; rc=$?
check_rc "a failed git read exits 2, not 0" 2 "$rc"
case "$out" in *"READ FAILED"*) pass=$((pass + 1)) ;;
  *) fail=$((fail + 1)); printf 'FAIL  a failed read did not say so: %q\n' "$out" >&2 ;;
esac

# A git that succeeds but prints nothing is the shape that makes an empty pipeline look like an
# answer. A non-numeric commit count is a failed read, not zero commits behind.
QUIET_GIT="$REPO/quiet-git"
cat >"$QUIET_GIT" <<'EOF'
#!/usr/bin/env bash
exit 0
EOF
chmod +x "$QUIET_GIT"
ZEEBRA_MBA_GIT="$QUIET_GIT" run_mba "$BASE" "$PR_311" main >/dev/null 2>&1
check_rc "a silent git exiting 0 is still a failed read" 2 $?

# --- usage -----------------------------------------------------------------

bash "$MBA" >/dev/null 2>&1
check_rc "no arguments is a usage error" 64 $?
bash "$MBA" a b >/dev/null 2>&1
check_rc "too few arguments is a usage error" 64 $?

# ---------------------------------------------------------------------------

printf '\n%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
