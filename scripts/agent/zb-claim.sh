#!/usr/bin/env bash
# Issue claiming for parallel agents: claim, heartbeat, release, reap.
#
# GitHub issues are the coordination substrate. An agent claims an issue before
# working it and releases it when done, so two agents never start the same work.
# A claim is a structured comment carrying the claimant's identity and an expiry,
# plus the `agent:claimed` label; the comment is what makes a claim *expire*,
# since a label alone cannot say when it was applied.
#
# Two design points that are not obvious:
#
# 1. **Every read distinguishes three outcomes, not two.** 0 = data, 1 = the
#    answer is genuinely empty, 2 = the read FAILED. A rate-limited or
#    unauthenticated `gh` prints nothing and exits 0, and through a `| jq`
#    pipeline that empty output is indistinguishable from "no work is claimed" —
#    which would hand the same issue to every agent at once. Callers must branch
#    on the status and never on whether stdout was empty.
#
# 2. **Earliest `at=` wins a race**, not latest. Two agents that claim within the
#    same second both see their own comment land; the tiebreak has to be a
#    property of the data rather than of who looked last.
#
# 3. **A claim carries a token, because `worktree@branch` is mutable.** Renaming
#    the branch changes the derived id, which used to orphan every marker the
#    agent had already written: `verify` then found a claim by "someone else"
#    inside a live window, applied the tiebreak, and reported LOST RACE against
#    the agent itself (#325). The token is minted once per checkout, kept in the
#    worktree's own git directory, and written into the marker, so ownership is
#    *proved* rather than re-derived from git state that a rebase can change.
#    The tiebreak itself is untouched: the token decides only whether the
#    earliest live claim is ours.
#
# Sourceable as a library (the `zb_*` functions) or runnable as a CLI; see
# CLAUDE.md § Multi-agent coordination for the protocol these implement.
# Unit tests: scripts/agent/test/zb-claim-test.sh

ZB_REPO="${ZB_REPO:-mfaulk/zeebra}"
ZB_PROJECT_OWNER="${ZB_PROJECT_OWNER:-mfaulk}"
ZB_PROJECT_NUMBER="${ZB_PROJECT_NUMBER:-7}"
ZB_PROJECT_ID="${ZB_PROJECT_ID:-PVT_kwHOABTRqc4Bp4Jk}"
ZB_STATUS_FIELD="${ZB_STATUS_FIELD:-PVTSSF_lAHOABTRqc4Bp4JkzhoRuKA}"
ZB_STATUS_TODO="${ZB_STATUS_TODO:-f75ad846}"
ZB_STATUS_IN_PROGRESS="${ZB_STATUS_IN_PROGRESS:-47fc9ee4}"
ZB_CLAIM_LABEL="${ZB_CLAIM_LABEL:-agent:claimed}"
ZB_LEASE_SECONDS="${ZB_LEASE_SECONDS:-14400}" # 4 hours
# Page bound for the orient read. GraphQL caps `first:` at 100, so this is a
# ceiling on open issues, not on the query. Exhausting it is a FAILED read.
ZB_ORIENT_MAX_PAGES="${ZB_ORIENT_MAX_PAGES:-20}"

# === pure functions (no network; covered by the unit tests) ================

# This worktree + branch. All agents commit as the same git user, so the
# assignee cannot tell them apart; the checkout is the distinguishing identity.
zb_agent_id() {
  local root branch
  root="$(basename "$(git rev-parse --show-toplevel 2>/dev/null || echo unknown)")"
  branch="$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo detached)"
  printf '%s@%s\n' "$root" "$branch"
}

zb_now() { date -u +%Y-%m-%dT%H:%M:%SZ; }
zb_until() { date -u -d "+${ZB_LEASE_SECONDS} seconds" +%Y-%m-%dT%H:%M:%SZ; }

# Where this checkout's claim token lives: the worktree's own git directory, so
# it is per-checkout, never committed, and unaffected by renaming the branch.
zb_identity_file() {
  if [ -n "${ZB_IDENTITY_FILE:-}" ]; then printf '%s\n' "$ZB_IDENTITY_FILE"; return 0; fi
  local git_dir
  if git_dir="$(git rev-parse --absolute-git-dir 2>/dev/null)"; then
    printf '%s/zb-claim-identity\n' "$git_dir"
  else
    printf '%s/.zeebra/zb-claim-identity\n' "$HOME"
  fi
}

# This checkout's claim token, minted on first use. Stable across branch
# renames, rebases and force-pushes — the mutations that change zb_agent_id and
# used to orphan an agent's own markers.
zb_agent_token() {
  local file token
  file="$(zb_identity_file)"
  if [ -r "$file" ]; then
    token="$(tr -d '[:space:]' <"$file")"
    [ -n "$token" ] && { printf '%s\n' "$token"; return 0; }
  fi
  token="$(od -An -tx1 -N8 /dev/urandom 2>/dev/null | tr -d ' \n')"
  [ -n "$token" ] || return 2
  mkdir -p "$(dirname "$file")" 2>/dev/null
  printf '%s\n' "$token" >"$file" 2>/dev/null || return 2
  printf '%s\n' "$token"
}

# Claim markers from a JSON array of comment bodies on stdin, as
# agent/at/until/token TSV in document order.
#
# `token=` is optional and reads as `-` when absent: markers written before #325
# have no token, and they must keep resolving by id rather than becoming
# unparseable — an unreadable marker is treated as stale, which would strand
# issues claimed under the old format.
#   0 — markers found   1 — no markers   2 — input unreadable
zb_parse_claims() {
  local raw out
  raw="$(cat)"
  [ -n "$raw" ] || return 2
  out="$(printf '%s' "$raw" | jq -r '
      if type == "array" then .[] else error("not a JSON array") end
      | tostring
      | scan("<!-- zb-claim agent=\"([^\"]*)\"(?: token=\"([^\"]*)\")? at=\"([^\"]*)\" until=\"([^\"]*)\" -->")
      | [.[0], .[2], .[3], (.[1] // "-")]
      | @tsv' 2>/dev/null)" || return 2
  [ -n "$out" ] || return 1
  printf '%s\n' "$out"
}

# Withdrawal markers in a JSON array of comment bodies, as "<agent>\t<at>\t<token>".
#
# A withdrawal is how the loser of a race retracts its own claim without touching
# the label, the assignee or the board row — all of which are shared, and none of
# which belong to it (#544). A comment cannot be unsaid, so the retraction has to
# be a marker the resolver reads rather than a deletion.
#   0 — rows printed   1 — none   2 — UNREADABLE
zb_parse_withdrawals() {
  local raw out
  raw="$(cat)"
  [ -n "$raw" ] || return 2
  out="$(printf '%s' "$raw" | jq -r '
      if type == "array" then .[] else error("not a JSON array") end
      | tostring
      | scan("<!-- zb-withdraw agent=\"([^\"]*)\" token=\"([^\"]*)\" at=\"([^\"]*)\" -->")
      | [.[0], .[2], .[1]]
      | @tsv' 2>/dev/null)" || return 2
  [ -n "$out" ] || return 1
  printf '%s\n' "$out"
}

# Whether a claim marker has been retracted by a later withdrawal.
#
# A withdrawal retracts a claim when it is **strictly later** and provably from the
# same checkout: same token, or — for a marker written before tokens existed — the
# same id with no token on either side to contradict it. Only the owner of a token
# can write that token, so this cannot retract another agent's claim; and the
# strictly-later test means a withdrawal cannot pre-emptively cancel a claim made
# after it, which is what keeps a reclaim honest.
#   0 — withdrawn   1 — still standing
zb_claim_is_withdrawn() { # <marker-agent> <marker-token> <marker-at> <withdrawals-tsv>
  local marker_agent="$1" marker_token="$2" marker_at="$3" withdrawals="$4"
  local w_agent w_at w_token
  [ -n "$withdrawals" ] || return 1
  while IFS="$(printf '\t')" read -r w_agent w_at w_token; do
    [ -n "$w_at" ] || continue
    # Not strictly later, so it says nothing about this claim.
    [ "$w_at" \> "$marker_at" ] || continue
    if [ -n "$w_token" ] && [ "$w_token" != "-" ] && [ "$w_token" = "$marker_token" ]; then
      return 0
    fi
    if { [ -z "$marker_token" ] || [ "$marker_token" = "-" ]; } && [ "$w_agent" = "$marker_agent" ]; then
      return 0
    fi
  done <<EOF
$withdrawals
EOF
  return 1
}

# Whether one marker belongs to this agent.
#
# Three ways, in order of strength:
#   token — the marker carries our token. Proof, and what survives a rename.
#   id    — the marker's id is the one we have now. The pre-#325 rule, and still
#           the only thing a tokenless marker can be matched on.
#   alias — the marker's id appears in some other marker bearing our token, so
#           that id was ours at some point. This is what rescues an issue
#           claimed before #325 and heartbeaten after it: the earliest live
#           marker is the tokenless one, and only a later marker can prove whose
#           it was. Only we can write a marker carrying our token, so the alias
#           set cannot be used to take someone else's claim.
#   0 — ours (prints which of the three matched)   1 — not ours
zb_claim_is_ours() { # <marker-agent> <marker-token> <our-id> <our-token> [alias-ids...]
  local marker_agent="$1" marker_token="$2" our_id="$3" our_token="$4" alias
  if [ -n "$marker_token" ] && [ "$marker_token" != "-" ] && [ "$marker_token" = "$our_token" ]; then
    echo token
    return 0
  fi
  if [ "$marker_agent" = "$our_id" ]; then echo id; return 0; fi
  shift 4
  for alias in "$@"; do
    [ "$marker_agent" = "$alias" ] && { echo alias; return 0; }
  done
  return 1
}

# Who holds the claim, from an agent/at/until/token TSV on stdin.
#
# The resolution rule is untouched: among claims inside the current lease window
# the earliest `at=` wins. The token only answers the separate question of
# whether that winner is us.
#
# Retracted claims are dropped before the rule is applied, so a withdrawn claim
# cannot win the race it had already conceded. Dropping them first rather than
# excusing them afterwards is what makes the rule's one sentence stay true.
#   prints "<held|lost|none>\t<winner-id>\t<id|token|->"
#   0 — held by us   1 — lost, or no claim inside the window
zb_resolve_claim() { # <our-id> <our-token> <cutoff-iso> [withdrawals-tsv]
  local live standing winner winner_id winner_token how aliases
  local agent at until token
  live="$(awk -F'\t' -v c="$3" '$2 >= c')"
  if [ -n "${4:-}" ] && [ -n "$live" ]; then
    standing=""
    while IFS="$(printf '\t')" read -r agent at until token; do
      [ -n "$at" ] || continue
      zb_claim_is_withdrawn "$agent" "$token" "$at" "$4" && continue
      standing="$standing$agent	$at	$until	$token
"
    done <<EOF
$live
EOF
    live="$(printf '%s' "$standing")"
  fi
  if [ -z "$live" ]; then
    printf 'none\t-\t-\n'
    return 1
  fi
  # Ids this checkout has claimed under, read off the markers carrying our token.
  aliases=""
  if [ -n "$2" ] && [ "$2" != "-" ]; then
    aliases="$(printf '%s\n' "$live" | awk -F'\t' -v t="$2" '$4 == t {print $1}' | sort -u)"
  fi
  winner="$(printf '%s\n' "$live" | zb_earliest_claim)"
  winner_id="$(printf '%s' "$winner" | cut -f1)"
  winner_token="$(printf '%s' "$winner" | cut -f4)"
  # shellcheck disable=SC2086  # aliases is a deliberately word-split id list
  if how="$(zb_claim_is_ours "$winner_id" "$winner_token" "$1" "$2" $aliases)"; then
    printf 'held\t%s\t%s\n' "$winner_id" "$how"
    return 0
  fi
  printf 'lost\t%s\t-\n' "$winner_id"
  return 1
}

# ISO-8601 UTC sorts lexicographically, so these need no date parsing.
zb_newest_claim() { _zb_pick_claim tail; }
zb_earliest_claim() { _zb_pick_claim head; }
_zb_pick_claim() {
  local out
  out="$(sort -t"$(printf '\t')" -k2,2 | "$1" -n1)"
  [ -n "$out" ] || return 1
  printf '%s\n' "$out"
}

# live|stale for one claim. Live if ANY of: an open linked PR exists, the lease
# has not expired, or a commit landed inside the lease window.
#
# An unparseable `until=` is deliberately STALE: a corrupt marker must not strand
# the issue behind a claim no one can ever disprove.
zb_lease_state() { # <until_iso> <now_iso> <has_open_pr 0|1> <last_commit_epoch|-> [lease_s]
  local until_iso="$1" now_iso="$2" has_pr="$3" last_commit="$4" lease="${5:-$ZB_LEASE_SECONDS}"
  local now_e until_e
  if [ "$has_pr" = 1 ]; then echo live; return 0; fi
  now_e="$(date -u -d "$now_iso" +%s 2>/dev/null)" || { echo stale; return 0; }
  if until_e="$(date -u -d "$until_iso" +%s 2>/dev/null)"; then
    if [ "$until_e" -gt "$now_e" ]; then echo live; return 0; fi
  fi
  if [ "$last_commit" != "-" ] && [ -n "$last_commit" ]; then
    if [ $((now_e - last_commit)) -lt "$lease" ]; then echo live; return 0; fi
  fi
  echo stale
}

# The cursor to resume a paginated read from, given one GraphQL response.
#
# `hasNextPage: true` with no usable `endCursor` is status 2 and emphatically NOT
# "the end of the list". A read that cannot be continued is a failed read; saying
# otherwise is #448, where orient returned the first 100 of 112 open issues and
# exited 0 with a queue that looked complete.
#   0 — cursor printed   1 — that was the last page   2 — undecidable
zb_page_cursor() {
  local raw has cursor
  raw="$(cat)"
  [ -n "$raw" ] || return 2
  has="$(printf '%s' "$raw" | jq -r '
      .data.repository.issues.pageInfo.hasNextPage
      | if type == "boolean" then tostring else error("hasNextPage is not a boolean") end' 2>/dev/null)" || return 2
  [ "$has" = true ] || return 1
  cursor="$(printf '%s' "$raw" | jq -r '.data.repository.issues.pageInfo.endCursor // empty' 2>/dev/null)" || return 2
  [ -n "$cursor" ] || return 2
  printf '%s\n' "$cursor"
}

# The ranked queue from a paginated read: one compact JSON array of issue nodes
# per line on stdin, merged across pages and ranked High -> Medium -> Low ->
# unset. Open, unclaimed, unblocked, not Done.
#
# Split out from the fetch loop because this half is pure and the fetch half is
# not. Ranking has to span the merged pages rather than each page, and a page
# that fails to parse has to fail the whole merge: dropping it would silently
# lose 100 issues, which is the shape of the bug this replaces.
#   0 — rows printed   1 — nothing qualifies   2 — a page was unreadable
zb_merge_issue_pages() {
  local raw out
  raw="$(cat)"
  [ -n "$raw" ] || return 2
  out="$(printf '%s\n' "$raw" | jq -r -s --argjson pn "$ZB_PROJECT_NUMBER" --arg cl "$ZB_CLAIM_LABEL" '
      def rank: {High: 0, Medium: 1, Low: 2}[.] // 3;
      if length == 0 or (map(type) | any(. != "array")) then error("not a page of issue nodes") else . end
      | add
      | [ unique_by(.number)[]
          | . as $i
          | ($i.labels.nodes | map(.name)) as $L
          | select(($L | index($cl)) == null and ($L | index("blocked")) == null)
          # An open linked PR is a LIVE claim by §4 whether or not the label is
          # still on. §6 tells the finishing agent to drop the label and leave the
          # issue for the PR to close, so keying on the label alone put finished
          # work back in the queue (#544).
          | select([$i.closedByPullRequestsReferences.nodes[] | select(.state == "OPEN")] | length == 0)
          | ($i.projectItems.nodes[] | select(.project.number == $pn)) as $it
          | select(($it.s.name // "") != "Done")
          | {n: $i.number, t: $i.title, p: ($it.fieldValueByName.name // "—")} ]
      | sort_by([(.p | rank), .n]) | .[] | "\(.p)\t#\(.n)\t\(.t)"' 2>/dev/null)" || return 2
  [ -n "$out" ] || return 1
  printf '%s\n' "$out"
}

# === network reads =========================================================

# Run a GraphQL query, failing loudly rather than returning an empty string.
_zb_gql() { # <query> [jq-filter]
  local raw
  raw="$(gh api graphql -f query="$1" 2>/dev/null)" || {
    echo "zb-claim: GraphQL read failed" >&2
    return 2
  }
  [ -n "$raw" ] || { echo "zb-claim: GraphQL returned NO output at exit 0 — treating as failure" >&2; return 2; }
  if printf '%s' "$raw" | jq -e 'has("errors")' >/dev/null 2>&1; then
    echo "zb-claim: GraphQL returned errors: $(printf '%s' "$raw" | jq -c '.errors')" >&2
    return 2
  fi
  if [ $# -ge 2 ]; then printf '%s' "$raw" | jq -r "$2" 2>/dev/null || return 2
  else printf '%s' "$raw"; fi
}

# Open, unclaimed, unblocked issues ranked High -> Medium -> Low -> unset.
# Priority is a board field, not a label, so this joins issues to their row.
#
# Paginated, because `first:` is capped at 100 per page and the repo passed 100
# open issues (#448). The pages it drops are always the newest — exactly the
# follow-up issues agents file for each other — so an incomplete walk is a
# status-2 failure and never a short queue.
#   0 — work found   1 — nothing open and unclaimed   2 — UNREADABLE
zb_orient() {
  local owner="${ZB_REPO%%/*}" name="${ZB_REPO##*/}"
  local after="null" pages="" page nodes cursor rc n=0
  while [ "$n" -lt "$ZB_ORIENT_MAX_PAGES" ]; do
    n=$((n + 1))
    page="$(_zb_gql "
      { repository(owner: \"$owner\", name: \"$name\") {
          issues(first: 100, states: OPEN, after: $after) {
            pageInfo { hasNextPage endCursor }
            nodes {
              number title
              labels(first: 20) { nodes { name } }
              closedByPullRequestsReferences(first: 10) { nodes { state } }
              projectItems(first: 5) { nodes {
                project { number }
                fieldValueByName(name: \"Priority\") { ... on ProjectV2ItemFieldSingleSelectValue { name } }
                s: fieldValueByName(name: \"Status\") { ... on ProjectV2ItemFieldSingleSelectValue { name } }
              } } } } } }")" || return 2
    nodes="$(printf '%s' "$page" | jq -c '
        .data.repository.issues.nodes
        | if type == "array" then . else error("no issue nodes in the response") end' 2>/dev/null)" || return 2
    pages="$pages$nodes
"
    rc=0; cursor="$(printf '%s' "$page" | zb_page_cursor)" || rc=$?
    case $rc in
      0) after="\"$cursor\"" ;;
      1) printf '%s' "$pages" | zb_merge_issue_pages; return $? ;;
      *) echo "zb-claim: the paginated issue read could not be continued after page $n — refusing to report a partial queue" >&2
         return 2 ;;
    esac
  done
  echo "zb-claim: the open-issue walk exceeded ZB_ORIENT_MAX_PAGES=$ZB_ORIENT_MAX_PAGES; raise it. Refusing to report a truncated queue" >&2
  return 2
}

# Claim markers on one issue, as TSV. Statuses are zb_parse_claims's.
zb_issue_claims() { # <issue-number>
  local bodies
  bodies="$(gh issue view "$1" --repo "$ZB_REPO" --json comments --jq '[.comments[].body]' 2>/dev/null)" || return 2
  printf '%s' "$bodies" | zb_parse_claims
}

# Withdrawal markers on one issue, as TSV. Statuses are zb_parse_withdrawals's.
zb_issue_withdrawals() { # <issue-number>
  local bodies
  bodies="$(gh issue view "$1" --repo "$ZB_REPO" --json comments --jq '[.comments[].body]' 2>/dev/null)" || return 2
  printf '%s' "$bodies" | zb_parse_withdrawals
}

# The issue's claim resolution for this checkout, withdrawals accounted for.
#   prints zb_resolve_claim's row
#   0 — held by us   1 — lost or unclaimed   2 — UNREADABLE
zb_issue_resolution() { # <issue-number>
  local claims withdrawals id token cutoff rc=0
  id="$(zb_agent_id)"
  token="$(zb_agent_token)" || token="-"
  claims="$(zb_issue_claims "$1")" || {
    rc=$?
    [ "$rc" -eq 2 ] && return 2
    printf 'none\t-\t-\n'
    return 1
  }
  withdrawals="$(zb_issue_withdrawals "$1")" || {
    rc=$?
    [ "$rc" -eq 2 ] && return 2
    withdrawals=""
  }
  cutoff="$(date -u -d "-${ZB_LEASE_SECONDS} seconds" +%Y-%m-%dT%H:%M:%SZ)"
  printf '%s\n' "$claims" | zb_resolve_claim "$id" "$token" "$cutoff" "$withdrawals"
}

# 1 if the issue has an open linked PR, else 0. Prints nothing on failure (rc 2).
zb_has_open_pr() { # <issue-number>
  local n
  n="$(gh issue view "$1" --repo "$ZB_REPO" --json closedByPullRequestsReferences \
        --jq '[.closedByPullRequestsReferences[] | select(.state == "OPEN")] | length' 2>/dev/null)" || return 2
  [ -n "$n" ] || return 2
  [ "$n" -gt 0 ] && echo 1 || echo 0
}

# live|stale for the issue's most recent claim.
#   0 — state printed   1 — no claim on this issue   2 — UNREADABLE
zb_issue_lease_state() { # <issue-number>
  local claims rc=0 newest until has_pr
  claims="$(zb_issue_claims "$1")" || rc=$?
  [ "$rc" -eq 2 ] && return 2
  [ "$rc" -eq 1 ] && return 1
  newest="$(printf '%s' "$claims" | zb_newest_claim)" || return 1
  until="$(printf '%s' "$newest" | cut -f3)"
  has_pr="$(zb_has_open_pr "$1")" || return 2
  zb_lease_state "$until" "$(zb_now)" "$has_pr" -
}

# === mutations =============================================================

_zb_item_id() { # <issue-number> -> project item id
  local owner="${ZB_REPO%%/*}" name="${ZB_REPO##*/}"
  _zb_gql "
    { repository(owner: \"$owner\", name: \"$name\") { issue(number: $1) {
        projectItems(first: 5) { nodes { id project { number } } } } } }" \
    ".data.repository.issue.projectItems.nodes[] | select(.project.number == $ZB_PROJECT_NUMBER) | .id"
}

zb_set_status() { # <issue-number> <option-id>
  local item
  item="$(_zb_item_id "$1")" || return 2
  [ -n "$item" ] || { echo "zb-claim: issue #$1 is not on the board" >&2; return 2; }
  _zb_gql "mutation { updateProjectV2ItemFieldValue(input: {
      projectId: \"$ZB_PROJECT_ID\", itemId: \"$item\",
      fieldId: \"$ZB_STATUS_FIELD\", value: {singleSelectOptionId: \"$2\"}
    }) { projectV2Item { id } } }" '.data.updateProjectV2ItemFieldValue.projectV2Item.id' >/dev/null
}

zb_claim() { # <issue-number> <intent>
  local n="$1" intent="${2:-unspecified}" id token now until
  id="$(zb_agent_id)"; now="$(zb_now)"; until="$(zb_until)"
  token="$(zb_agent_token)" || { echo "zb-claim: could not mint a claim token" >&2; return 2; }
  gh issue comment "$n" --repo "$ZB_REPO" --body \
"🔒 Claimed by agent \`$id\`. Lease until $until (UTC). Intent: $intent.
<!-- zb-claim agent=\"$id\" token=\"$token\" at=\"$now\" until=\"$until\" -->" >/dev/null || return 2
  gh issue edit "$n" --repo "$ZB_REPO" --add-label "$ZB_CLAIM_LABEL" --add-assignee "@me" >/dev/null || return 2
  zb_set_status "$n" "$ZB_STATUS_IN_PROGRESS" || return 2
  echo "claimed #$n as $id until $until"
  zb_verify "$n"
}

# Confirm we actually hold the claim. Among claims posted within the current
# lease window, the earliest `at=` wins; older markers are spent claims from
# previous, already-released rounds and must not win forever.
#   0 — we hold it   1 — another agent won; back off   2 — UNREADABLE
zb_verify() { # <issue-number>
  local id resolution verdict winner how
  id="$(zb_agent_id)"
  resolution="$(zb_issue_resolution "$1")" || {
    [ $? -eq 2 ] && return 2
  }
  verdict="$(printf '%s' "$resolution" | cut -f1)"
  winner="$(printf '%s' "$resolution" | cut -f2)"
  how="$(printf '%s' "$resolution" | cut -f3)"
  case "$verdict" in
    none)
      echo "zb-claim: no claim inside the current lease window on #$1" >&2
      return 1 ;;
    held)
      if [ "$winner" != "$id" ]; then
        # The rename case. Saying so is the point: the operator should not have
        # to guess why a claim under another name is theirs.
        echo "verified: #$1 is held by this checkout, claimed as $winner (matched by $how; the id is now $id)"
      else
        echo "verified: #$1 is held by $id"
      fi ;;
    *)
      echo "LOST RACE on #$1 — $winner claimed first. Run 'withdraw $1' and pick other work; do NOT release, which would strip their label." >&2
      return 1 ;;
  esac
}

zb_heartbeat() { # <issue-number>
  local id token now until
  id="$(zb_agent_id)"; now="$(zb_now)"; until="$(zb_until)"
  token="$(zb_agent_token)" || { echo "zb-claim: could not read this checkout's claim token" >&2; return 2; }
  gh issue comment "$1" --repo "$ZB_REPO" --body \
"⏱️ Lease refreshed by \`$id\` until $until (UTC).
<!-- zb-claim agent=\"$id\" token=\"$token\" at=\"$now\" until=\"$until\" -->" >/dev/null || return 2
  echo "refreshed #$1 until $until"
}

zb_reclaim() { # <issue-number> <intent>
  local state
  state="$(zb_issue_lease_state "$1")" || {
    [ $? -eq 2 ] && return 2
    state=stale # no claim marker at all; the label is a leftover
  }
  if [ "$state" = live ]; then
    echo "zb-claim: #$1 holds a LIVE lease — do not take it" >&2
    return 1
  fi
  local prev
  prev="$(zb_issue_claims "$1" | zb_newest_claim | cut -f1)" || prev="unknown"
  gh issue comment "$1" --repo "$ZB_REPO" --body \
"♻️ Lease from \`$prev\` expired (no open PR, no recent commits). Taking over as \`$(zb_agent_id)\`." >/dev/null || return 2
  zb_claim "$1" "${2:-taking over an expired lease}"
}

# Retract this checkout's own claim, touching nothing that is shared.
#
# What the loser of a race is for. The label, the assignee and the board row are
# one each and belong to whoever won; `release` used to remove them anyway, so the
# loser following CLAUDE.md §3 broke the winner's claim (#544). This writes a
# marker the resolver reads and changes nothing else.
zb_withdraw() { # <issue-number>
  local id token now
  id="$(zb_agent_id)"; now="$(zb_now)"
  token="$(zb_agent_token)" || { echo "zb-claim: could not read this checkout's claim token" >&2; return 2; }
  gh issue comment "$1" --repo "$ZB_REPO" --body \
"🚫 \`$id\` withdraws its claim on this issue. No label, assignee or board state was changed.
<!-- zb-withdraw agent=\"$id\" token=\"$token\" at=\"$now\" -->" >/dev/null || return 2
  echo "withdrew this checkout's claim on #$1 (shared state untouched)"
}

# Drop the working label, and optionally the assignee and the board row.
#
# Refuses when another agent demonstrably holds the claim, because all three of
# those are shared state and there is one of each. `--force` is the override the
# refusal names; `reclaim` already refuses a live lease and this is the mutation
# that used to trust its caller instead (#544).
zb_release() { # <issue-number> [--abandon] [--force]
  local issue="$1" abandon=0 force=0 arg resolution verdict winner
  shift
  for arg in "$@"; do
    case "$arg" in
      --abandon) abandon=1 ;;
      --force)   force=1 ;;
      *) echo "zb-claim: unknown release option $arg" >&2; return 2 ;;
    esac
  done

  if [ "$force" -eq 0 ]; then
    resolution="$(zb_issue_resolution "$issue")" || {
      [ $? -eq 2 ] && return 2
    }
    verdict="$(printf '%s' "$resolution" | cut -f1)"
    winner="$(printf '%s' "$resolution" | cut -f2)"
    if [ "$verdict" = lost ]; then
      echo "zb-claim: #$issue is held by $winner, not by this checkout — refusing to remove a label, assignee or board row that is not yours." >&2
      echo "zb-claim: to retract your own losing claim, use 'withdraw $issue'. To override anyway, pass --force." >&2
      return 1
    fi
  fi

  if [ "$abandon" -eq 1 ]; then
    gh issue edit "$issue" --repo "$ZB_REPO" --remove-label "$ZB_CLAIM_LABEL" --remove-assignee "@me" >/dev/null || return 2
    zb_set_status "$issue" "$ZB_STATUS_TODO" || return 2
    echo "abandoned #$issue — label and assignee removed, board back to Todo"
  else
    gh issue edit "$issue" --repo "$ZB_REPO" --remove-label "$ZB_CLAIM_LABEL" >/dev/null || return 2
    echo "released the working label on #$issue (the open PR keeps it In Progress)"
  fi
}

# Every claimed issue whose lease is stale, as "<number> <agent> <until>".
#   0 — stale claims found   1 — none   2 — UNREADABLE
zb_reap() {
  local nums out="" n claims newest state
  nums="$(gh issue list --repo "$ZB_REPO" --label "$ZB_CLAIM_LABEL" --state open \
            --limit 200 --json number --jq '.[].number' 2>/dev/null)" || return 2
  [ -n "$nums" ] || return 1
  for n in $nums; do
    claims="$(zb_issue_claims "$n")" || continue
    newest="$(printf '%s' "$claims" | zb_newest_claim)" || continue
    state="$(zb_issue_lease_state "$n")" || continue
    [ "$state" = stale ] && out="$out$n	$(printf '%s' "$newest" | cut -f1)	$(printf '%s' "$newest" | cut -f3)
"
  done
  [ -n "$out" ] || return 1
  printf '%s' "$out"
}

# === CLI ===================================================================

if [ "${BASH_SOURCE[0]}" = "${0}" ]; then
  cmd="${1:-help}"; shift || true
  case "$cmd" in
    orient)    zb_orient; rc=$?; [ $rc -eq 1 ] && echo "nothing open and unclaimed"; [ $rc -eq 2 ] && { echo "BOARD READ FAILED — this is not an empty queue" >&2; exit 2; }; exit 0 ;;
    claim)     zb_claim "$@" ;;
    verify)    zb_verify "$@" ;;
    heartbeat) zb_heartbeat "$@" ;;
    reclaim)   zb_reclaim "$@" ;;
    release)   zb_release "$@" ;;
    withdraw)  zb_withdraw "$@" ;;
    state)     zb_issue_lease_state "$@" ;;
    reap)      zb_reap; rc=$?; [ $rc -eq 1 ] && echo "no stale claims"; [ $rc -eq 2 ] && { echo "REAP READ FAILED" >&2; exit 2; }; exit 0 ;;
    id)        zb_agent_id ;;
    token)     zb_agent_token ;;
    *)
      cat <<'USAGE'
zb-claim.sh — issue claiming for parallel agents

  orient                     open, unclaimed, unblocked issues, best first
  claim <N> "<intent>"       claim #N for 4 hours (comment + label + In Progress)
  verify <N>                 confirm you won the claim; rc 1 means back off
  heartbeat <N>              extend the lease by another 4 hours
  state <N>                  live | stale
  reclaim <N> "<intent>"     take over #N, only if its lease is stale
  release <N>                drop the label (finished; PR keeps it In Progress)
  release <N> --abandon      drop label + assignee and return the board to Todo
  release <N> --force        release even when another agent holds the claim
  withdraw <N>               retract your own claim, touching no shared state
  reap                       every claimed issue whose lease has expired
  id                         this agent's id (worktree@branch)
  token                      this checkout's claim token, minted on first use

Exit statuses on reads: 0 = data, 1 = genuinely empty, 2 = READ FAILED.
Never treat 2 as "nothing to do".

A claim records both the id and the token. The id can change under you — a
branch rename, a rebase onto a new base, a retargeted PR — and the token cannot,
so `verify` still recognizes your own claim afterwards.
USAGE
      ;;
  esac
fi
