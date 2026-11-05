#!/usr/bin/env bash
# Unit tests for the pure, network-free half of zb-claim.sh.
#
# Only the parsing and lease-arithmetic functions are covered here. The
# subcommands that call `gh` are not: they are thin wrappers whose failure modes
# are the API's, and a test that mocked `gh` would pin the mock rather than the
# behaviour.
set -uo pipefail

LIB="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/zb-claim.sh"
# shellcheck source=../zb-claim.sh
. "$LIB"

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

marker() { # <agent> <at> <until>
  printf '<!-- zb-claim agent="%s" at="%s" until="%s" -->' "$1" "$2" "$3"
}

# --- zb_parse_claims -------------------------------------------------------

# A single claim marker in one comment yields one agent/at/until row.
one=$(jq -n --arg b "🔒 Claimed. $(marker alpha@feat/x 2026-01-01T00:00:00Z 2026-01-01T04:00:00Z)" '[$b]' \
  | zb_parse_claims)
check "parse: single marker" \
  "$(printf 'alpha@feat/x\t2026-01-01T00:00:00Z\t2026-01-01T04:00:00Z')" "$one"

# Comments carrying no marker contribute no rows, and the read still succeeds.
none=$(jq -n '["just a normal comment", "another one"]' | zb_parse_claims)
rc=$?
check "parse: no markers is empty" "" "$none"
check_rc "parse: no markers returns 1" 1 "$rc"

# Multiple markers across comments are emitted in document order.
multi=$(jq -n \
  --arg a "$(marker alpha@a 2026-01-01T00:00:00Z 2026-01-01T04:00:00Z)" \
  --arg b "$(marker beta@b 2026-01-01T01:00:00Z 2026-01-01T05:00:00Z)" \
  '[$a, $b]' | zb_parse_claims)
check "parse: two markers, document order" \
  "$(printf 'alpha@a\t2026-01-01T00:00:00Z\t2026-01-01T04:00:00Z\nbeta@b\t2026-01-01T01:00:00Z\t2026-01-01T05:00:00Z')" \
  "$multi"

# Two markers inside one comment body are both extracted.
twoinone=$(jq -n --arg b "$(marker alpha@a 2026-01-01T00:00:00Z 2026-01-01T04:00:00Z) and $(marker beta@b 2026-01-01T02:00:00Z 2026-01-01T06:00:00Z)" '[$b]' \
  | zb_parse_claims)
check "parse: two markers in one body" \
  "$(printf 'alpha@a\t2026-01-01T00:00:00Z\t2026-01-01T04:00:00Z\nbeta@b\t2026-01-01T02:00:00Z\t2026-01-01T06:00:00Z')" \
  "$twoinone"

# Malformed input that is not a JSON array is an UNREADABLE read, not an empty one.
printf 'not json' | zb_parse_claims >/dev/null 2>&1
check_rc "parse: non-JSON input returns 2 (unreadable), not 1 (empty)" 2 $?

# A JSON object rather than an array is likewise unreadable.
printf '{"message":"Bad credentials"}' | zb_parse_claims >/dev/null 2>&1
check_rc "parse: JSON object returns 2" 2 $?

# --- zb_newest_claim / zb_earliest_claim -----------------------------------

rows=$(printf 'alpha@a\t2026-01-01T03:00:00Z\t2026-01-01T07:00:00Z\nbeta@b\t2026-01-01T01:00:00Z\t2026-01-01T05:00:00Z\n')

# The newest claim is the one with the greatest at=, regardless of input order.
check "newest: greatest at= wins" \
  "$(printf 'alpha@a\t2026-01-01T03:00:00Z\t2026-01-01T07:00:00Z')" \
  "$(printf '%s' "$rows" | zb_newest_claim)"

# The race winner is the EARLIEST at=, which is how two agents racing resolve.
check "earliest: least at= wins the race" \
  "$(printf 'beta@b\t2026-01-01T01:00:00Z\t2026-01-01T05:00:00Z')" \
  "$(printf '%s' "$rows" | zb_earliest_claim)"

# With no rows at all there is no claim to report.
printf '' | zb_newest_claim >/dev/null 2>&1
check_rc "newest: empty input returns 1" 1 $?

# --- zb_lease_state --------------------------------------------------------

NOW=2026-01-01T06:00:00Z

# A lease whose until= is still in the future is live.
check "lease: future until= is live" live \
  "$(zb_lease_state 2026-01-01T08:00:00Z "$NOW" 0 -)"

# A lease whose until= has passed, with no PR and no recent commit, is stale.
check "lease: expired with no PR and no commits is stale" stale \
  "$(zb_lease_state 2026-01-01T04:00:00Z "$NOW" 0 -)"

# An open linked PR keeps the claim live even after until= has passed.
check "lease: open linked PR overrides expiry" live \
  "$(zb_lease_state 2026-01-01T04:00:00Z "$NOW" 1 -)"

# A commit pushed inside the lease window keeps an expired claim live.
recent=$(date -u -d '2026-01-01T05:00:00Z' +%s)
check "lease: recent branch commit overrides expiry" live \
  "$(zb_lease_state 2026-01-01T04:00:00Z "$NOW" 0 "$recent")"

# A commit older than the lease window does not rescue an expired claim.
old=$(date -u -d '2026-01-01T00:30:00Z' +%s)
check "lease: commit older than the window leaves it stale" stale \
  "$(zb_lease_state 2026-01-01T04:00:00Z "$NOW" 0 "$old")"

# The boundary is inclusive-of-future only: until= exactly now counts as expired.
check "lease: until= exactly now is stale" stale \
  "$(zb_lease_state "$NOW" "$NOW" 0 -)"

# An unparseable until= must not silently read as "live"; it is stale so the
# work can be reclaimed rather than stranded behind a corrupt marker.
check "lease: unparseable until= is stale" stale \
  "$(zb_lease_state "not-a-date" "$NOW" 0 -)"

# --- zb_agent_id -----------------------------------------------------------

# The agent id combines worktree basename and branch, which is what distinguishes
# two agents that commit as the same git user.
id="$(zb_agent_id)"
case "$id" in
  *@*) pass=$((pass + 1)) ;;
  *) fail=$((fail + 1)); printf 'FAIL  agent id lacks @: %q\n' "$id" >&2 ;;
esac

# ---------------------------------------------------------------------------

printf '\n%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
