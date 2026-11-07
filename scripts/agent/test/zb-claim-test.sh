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

# A marker in the post-#325 format, which also records the claim token.
marker_tok() { # <agent> <token> <at> <until>
  printf '<!-- zb-claim agent="%s" token="%s" at="%s" until="%s" -->' "$1" "$2" "$3" "$4"
}

# --- zb_parse_claims -------------------------------------------------------

# A single claim marker in one comment yields one agent/at/until row.
one=$(jq -n --arg b "🔒 Claimed. $(marker alpha@feat/x 2026-01-01T00:00:00Z 2026-01-01T04:00:00Z)" '[$b]' \
  | zb_parse_claims)
check "parse: single marker, tokenless, reads as token -" \
  "$(printf 'alpha@feat/x\t2026-01-01T00:00:00Z\t2026-01-01T04:00:00Z\t-')" "$one"

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
  "$(printf 'alpha@a\t2026-01-01T00:00:00Z\t2026-01-01T04:00:00Z\t-\nbeta@b\t2026-01-01T01:00:00Z\t2026-01-01T05:00:00Z\t-')" \
  "$multi"

# Two markers inside one comment body are both extracted.
twoinone=$(jq -n --arg b "$(marker alpha@a 2026-01-01T00:00:00Z 2026-01-01T04:00:00Z) and $(marker beta@b 2026-01-01T02:00:00Z 2026-01-01T06:00:00Z)" '[$b]' \
  | zb_parse_claims)
check "parse: two markers in one body" \
  "$(printf 'alpha@a\t2026-01-01T00:00:00Z\t2026-01-01T04:00:00Z\t-\nbeta@b\t2026-01-01T02:00:00Z\t2026-01-01T06:00:00Z\t-')" \
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

# --- zb_agent_token --------------------------------------------------------

IDENTITY_DIR="$(mktemp -d)"
trap 'rm -rf "$IDENTITY_DIR"' EXIT
export ZB_IDENTITY_FILE="$IDENTITY_DIR/zb-claim-identity"

# The token is minted on first use and then stable: it is what ownership is
# proved with, so a second read must not produce a second identity.
first="$(zb_agent_token)"
check "token: a second read returns the same token" "$first" "$(zb_agent_token)"
case "$first" in
  '' ) fail=$((fail + 1)); printf 'FAIL  token is empty\n' >&2 ;;
  *) pass=$((pass + 1)) ;;
esac

# A token stored with trailing whitespace reads back without it, so it still
# compares equal to the one written into a marker.
printf '  deadbeefcafe0001  \n' >"$ZB_IDENTITY_FILE"
check "token: surrounding whitespace is stripped" deadbeefcafe0001 "$(zb_agent_token)"

# --- zb_claim_is_ours ------------------------------------------------------

# The matching token wins even though the id has changed, which is the #325
# case: a branch rename must not orphan markers the agent already wrote.
check "ours: a matching token beats a changed id" token \
  "$(zb_claim_is_ours alpha@old-branch tok-1 alpha@new-branch tok-1)"

# A tokenless marker — every claim written before #325 — still resolves by id.
check "ours: a tokenless marker matches by id" id \
  "$(zb_claim_is_ours alpha@a - alpha@a tok-1)"

# A different agent's claim is not ours by either half.
zb_claim_is_ours beta@b tok-2 alpha@a tok-1
check_rc "ours: a different token and a different id is not ours" 1 $?

# Two tokenless markers from different ids stay distinct: the absent token must
# not read as a wildcard that matches everything.
zb_claim_is_ours beta@b - alpha@a -
check_rc "ours: absent tokens on both sides do not match each other" 1 $?

# --- zb_resolve_claim ------------------------------------------------------

CUTOFF=2026-01-01T00:00:00Z

# A claim written under one id is still held after the branch is renamed. This
# is the acceptance criterion of #325, and it fails against the old script,
# which compared the current id against the marker's and reported LOST RACE.
renamed="$(printf 'zb-a@feat/old\t2026-01-01T01:00:00Z\t2026-01-01T05:00:00Z\ttok-1\n')"
check "resolve: a renamed branch still holds its own claim" \
  "$(printf 'held\tzb-a@feat/old\ttoken')" \
  "$(printf '%s' "$renamed" | zb_resolve_claim zb-a@feat/new tok-1 "$CUTOFF")"
printf '%s' "$renamed" | zb_resolve_claim zb-a@feat/new tok-1 "$CUTOFF" >/dev/null
check_rc "resolve: a renamed branch exits 0, not 1" 0 $?

# The tiebreak is unchanged: against a genuinely competing claim the earliest
# at= still wins, and the token does not rescue a later claim.
contested="$(printf 'zb-b@feat/b\t2026-01-01T01:00:00Z\t2026-01-01T05:00:00Z\ttok-2\nzb-a@feat/old\t2026-01-01T02:00:00Z\t2026-01-01T06:00:00Z\ttok-1\n')"
check "resolve: an earlier competing claim still wins" \
  "$(printf 'lost\tzb-b@feat/b\t-')" \
  "$(printf '%s' "$contested" | zb_resolve_claim zb-a@feat/new tok-1 "$CUTOFF")"
printf '%s' "$contested" | zb_resolve_claim zb-a@feat/new tok-1 "$CUTOFF" >/dev/null
check_rc "resolve: losing the race still exits 1" 1 $?

# And winning it is still winning it, by the same earliest-at= rule.
check "resolve: our earlier claim beats a later competitor" \
  "$(printf 'held\tzb-a@feat/old\ttoken')" \
  "$(printf 'zb-a@feat/old\t2026-01-01T01:00:00Z\t2026-01-01T05:00:00Z\ttok-1\nzb-b@feat/b\t2026-01-01T02:00:00Z\t2026-01-01T06:00:00Z\ttok-2\n' \
     | zb_resolve_claim zb-a@feat/new tok-1 "$CUTOFF")"

# A claim older than the lease window is spent, not a holder: it must not win
# forever, which is why the window is applied before the tiebreak.
check "resolve: a claim older than the window is not a holder" \
  "$(printf 'none\t-\t-')" \
  "$(printf 'zb-a@feat/old\t2025-12-01T01:00:00Z\t2025-12-01T05:00:00Z\ttok-1\n' \
     | zb_resolve_claim zb-a@feat/new tok-1 "$CUTOFF")"

# A tokenless marker written by this very id still resolves as held, so claims
# made before #325 landed are not abandoned by the upgrade.
check "resolve: a pre-#325 marker is still held by its own id" \
  "$(printf 'held\tzb-a@feat/old\tid')" \
  "$(printf 'zb-a@feat/old\t2026-01-01T01:00:00Z\t2026-01-01T05:00:00Z\t-\n' \
     | zb_resolve_claim zb-a@feat/old tok-1 "$CUTOFF")"

# An issue claimed before #325 and heartbeaten after it, then renamed: the
# earliest live marker is the tokenless claim, so only the later heartbeat can
# prove the old id was ours. Without the alias step the agent loses a claim it
# demonstrably holds — the exact failure #325 reports, one marker further on.
legacy="$(printf 'zb-a@feat/old\t2026-01-01T01:00:00Z\t2026-01-01T05:00:00Z\t-\nzb-a@feat/old\t2026-01-01T02:00:00Z\t2026-01-01T06:00:00Z\ttok-1\n')"
check "resolve: a later token-bearing heartbeat proves the earlier tokenless claim" \
  "$(printf 'held\tzb-a@feat/old\talias')" \
  "$(printf '%s' "$legacy" | zb_resolve_claim zb-a@feat/new tok-1 "$CUTOFF")"

# The alias set is built only from markers carrying OUR token, so another
# agent's heartbeat cannot make its own earlier claim resolve as ours.
check "resolve: another agent's token builds no alias of ours" \
  "$(printf 'lost\tzb-b@feat/b\t-')" \
  "$(printf 'zb-b@feat/b\t2026-01-01T01:00:00Z\t2026-01-01T05:00:00Z\t-\nzb-b@feat/b\t2026-01-01T02:00:00Z\t2026-01-01T06:00:00Z\ttok-2\n' \
     | zb_resolve_claim zb-a@feat/new tok-1 "$CUTOFF")"

# An alias is only an alias inside the lease window: a spent marker of ours
# cannot vouch for an id, because the window is applied before anything else.
check "resolve: a marker outside the window builds no alias" \
  "$(printf 'lost\tzb-a@feat/old\t-')" \
  "$(printf 'zb-a@feat/old\t2025-11-01T02:00:00Z\t2025-11-01T06:00:00Z\ttok-1\nzb-a@feat/old\t2026-01-01T01:00:00Z\t2026-01-01T05:00:00Z\t-\n' \
     | zb_resolve_claim zb-a@feat/new tok-1 "$CUTOFF")"

# --- the marker round trip -------------------------------------------------

# A token-bearing marker parses into the fourth column, which is what connects
# the writer to the resolver.
tokrow=$(jq -n --arg b "🔒 Claimed. $(marker_tok alpha@feat/x tok-9 2026-01-01T00:00:00Z 2026-01-01T04:00:00Z)" '[$b]' \
  | zb_parse_claims)
check "parse: a token-bearing marker yields the token" \
  "$(printf 'alpha@feat/x\t2026-01-01T00:00:00Z\t2026-01-01T04:00:00Z\ttok-9')" "$tokrow"

# Mixed formats in one issue's comments both parse, in document order: an issue
# claimed before #325 and heartbeaten after it has one of each.
mixed=$(jq -n \
  --arg a "$(marker alpha@a 2026-01-01T00:00:00Z 2026-01-01T04:00:00Z)" \
  --arg b "$(marker_tok alpha@a tok-9 2026-01-01T01:00:00Z 2026-01-01T05:00:00Z)" \
  '[$a, $b]' | zb_parse_claims)
check "parse: tokenless and token-bearing markers coexist" \
  "$(printf 'alpha@a\t2026-01-01T00:00:00Z\t2026-01-01T04:00:00Z\t-\nalpha@a\t2026-01-01T01:00:00Z\t2026-01-01T05:00:00Z\ttok-9')" \
  "$mixed"

# --- pagination: zb_page_cursor --------------------------------------------

# One GraphQL response in the shape zb_orient's query returns, carrying only the
# pageInfo the cursor logic reads. $2 is JSON, so `null` and `"c1"` both work.
gql_page() { # <hasNextPage-json> <endCursor-json>
  jq -nc --argjson h "$1" --argjson c "$2" \
    '{data: {repository: {issues: {pageInfo: {hasNextPage: $h, endCursor: $c}, nodes: []}}}}'
}

# A page that reports more to come hands back the cursor to continue from.
cur="$(gql_page true '"c1"' | zb_page_cursor)"
check_rc "cursor: hasNextPage with a cursor exits 0" 0 $?
check "cursor: the endCursor is returned" c1 "$cur"

# The last page has no successor, which is genuinely empty rather than a failure.
gql_page false null | zb_page_cursor >/dev/null 2>&1
check_rc "cursor: hasNextPage false is 1 (the end), not 2" 1 $?

# The case #448 is about: more pages exist but nothing says where to resume, so
# the read is undecidable. Reporting "the end" here is exactly the silent
# truncation the issue reports, so this must be 2.
gql_page true null | zb_page_cursor >/dev/null 2>&1
check_rc "cursor: hasNextPage true with a null cursor is 2, not 1" 2 $?

# An empty endCursor string is no more resumable than a null one.
gql_page true '""' | zb_page_cursor >/dev/null 2>&1
check_rc "cursor: hasNextPage true with an empty cursor is 2" 2 $?

# A response with no pageInfo at all cannot be said to be complete.
printf '{"data":{"repository":{"issues":{"nodes":[]}}}}' | zb_page_cursor >/dev/null 2>&1
check_rc "cursor: a missing pageInfo is 2, not 1" 2 $?

# hasNextPage present but not a boolean is likewise undecidable.
gql_page '"yes"' '"c1"' | zb_page_cursor >/dev/null 2>&1
check_rc "cursor: a non-boolean hasNextPage is 2" 2 $?

# A read that produced nothing at exit 0 is the failure mode § 1 exists for.
printf '' | zb_page_cursor >/dev/null 2>&1
check_rc "cursor: empty input is 2" 2 $?

# Non-JSON input is unreadable, not the end of the list.
printf 'Bad credentials' | zb_page_cursor >/dev/null 2>&1
check_rc "cursor: non-JSON input is 2" 2 $?

# --- pagination: zb_merge_issue_pages --------------------------------------

# One issue node in the shape the orient query returns. Priority and Status are
# "-" for absent, which is how an issue on the board with no Priority set looks.
issue_node() { # <number> <title> <priority|-> <status|-> [label...]
  local n="$1" t="$2" p="$3" s="$4"
  shift 4
  jq -nc --argjson n "$n" --arg t "$t" --arg p "$p" --arg s "$s" \
    --argjson pn "$ZB_PROJECT_NUMBER" --args '
    { number: $n, title: $t,
      labels: {nodes: ($ARGS.positional | map({name: .}))},
      projectItems: {nodes: [
        { project: {number: $pn},
          fieldValueByName: (if $p == "-" then null else {name: $p} end),
          s: (if $s == "-" then null else {name: $s} end) }]} }' "$@"
}

# One page of the paginated read: a compact JSON array of nodes on one line.
page_of() { printf '%s\n' "$@" | jq -sc .; }

p1="$(page_of "$(issue_node 58 'medium one' Medium Todo)" "$(issue_node 100 'low one' Low Todo)")"
p2="$(page_of "$(issue_node 447 'high one' High Todo)" "$(issue_node 448 'unset one' - Todo)")"

# The acceptance criterion of #448: issues that only exist on the second page
# appear in the queue, and ranking is applied across the merged pages rather
# than within each one — a High on page 2 outranks a Medium on page 1.
check "merge: two pages rank as one list" \
  "$(printf 'High\t#447\thigh one\nMedium\t#58\tmedium one\nLow\t#100\tlow one\n—\t#448\tunset one')" \
  "$(printf '%s\n%s\n' "$p1" "$p2" | zb_merge_issue_pages)"
printf '%s\n%s\n' "$p1" "$p2" | zb_merge_issue_pages >/dev/null
check_rc "merge: pages with work exit 0" 0 $?

# A single page still works, so the loop's last iteration needs no special case.
check "merge: one page alone ranks correctly" \
  "$(printf 'Medium\t#58\tmedium one\nLow\t#100\tlow one')" \
  "$(printf '%s\n' "$p1" | zb_merge_issue_pages)"

# The label filter spans pages: a claimed or blocked issue on any page is out.
filtered="$(page_of \
  "$(issue_node 200 'claimed' High Todo agent:claimed)" \
  "$(issue_node 201 'blocked' High Todo blocked)" \
  "$(issue_node 202 'done' High Done)")"
printf '%s\n' "$filtered" | zb_merge_issue_pages >/dev/null 2>&1
check_rc "merge: claimed, blocked and Done issues leave nothing (1)" 1 $?

# Pages that are structurally fine but contain no issues are genuinely empty.
printf '[]\n[]\n' | zb_merge_issue_pages >/dev/null 2>&1
check_rc "merge: empty pages are 1, not 2" 1 $?

# Cursor-paginated reads over a dataset that changes mid-walk can repeat a node;
# the queue must not list the same issue twice.
check "merge: a node repeated across pages is listed once" \
  "$(printf 'High\t#447\thigh one')" \
  "$(printf '%s\n%s\n' \
      "$(page_of "$(issue_node 447 'high one' High Todo)")" \
      "$(page_of "$(issue_node 447 'high one' High Todo)")" \
    | zb_merge_issue_pages)"

# No input at all is a failed read, never an empty queue.
printf '' | zb_merge_issue_pages >/dev/null 2>&1
check_rc "merge: no pages at all is 2" 2 $?

# A page that is not a JSON array is unreadable: silently skipping it would drop
# a whole page of issues, which is the defect being fixed.
printf '%s\n{"message":"Bad credentials"}\n' "$p1" | zb_merge_issue_pages >/dev/null 2>&1
check_rc "merge: a non-array page is 2, not a short list" 2 $?

# And non-JSON on any line fails the whole merge rather than part of it.
printf '%s\nnot json\n' "$p1" | zb_merge_issue_pages >/dev/null 2>&1
check_rc "merge: non-JSON on any page is 2" 2 $?

# ---------------------------------------------------------------------------

printf '\n%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
