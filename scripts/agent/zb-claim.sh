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

# Claim markers from a JSON array of comment bodies on stdin, as agent/at/until
# TSV in document order.
#   0 — markers found   1 — no markers   2 — input unreadable
zb_parse_claims() {
  local raw out
  raw="$(cat)"
  [ -n "$raw" ] || return 2
  out="$(printf '%s' "$raw" | jq -r '
      if type == "array" then .[] else error("not a JSON array") end
      | tostring
      | scan("<!-- zb-claim agent=\"([^\"]*)\" at=\"([^\"]*)\" until=\"([^\"]*)\" -->")
      | @tsv' 2>/dev/null)" || return 2
  [ -n "$out" ] || return 1
  printf '%s\n' "$out"
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
#   0 — work found   1 — nothing open and unclaimed   2 — UNREADABLE
zb_orient() {
  local owner="${ZB_REPO%%/*}" name="${ZB_REPO##*/}" raw out
  raw="$(_zb_gql "
    { repository(owner: \"$owner\", name: \"$name\") {
        issues(first: 100, states: OPEN) { nodes {
          number title
          labels(first: 20) { nodes { name } }
          projectItems(first: 5) { nodes {
            project { number }
            fieldValueByName(name: \"Priority\") { ... on ProjectV2ItemFieldSingleSelectValue { name } }
            s: fieldValueByName(name: \"Status\") { ... on ProjectV2ItemFieldSingleSelectValue { name } }
          } } } } } }")" || return 2
  out="$(printf '%s' "$raw" | jq -r --argjson pn "$ZB_PROJECT_NUMBER" --arg cl "$ZB_CLAIM_LABEL" '
      def rank: {High: 0, Medium: 1, Low: 2}[.] // 3;
      [ .data.repository.issues.nodes[]
        | . as $i
        | ($i.labels.nodes | map(.name)) as $L
        | select(($L | index($cl)) == null and ($L | index("blocked")) == null)
        | ($i.projectItems.nodes[] | select(.project.number == $pn)) as $it
        | select(($it.s.name // "") != "Done")
        | {n: $i.number, t: $i.title, p: ($it.fieldValueByName.name // "—")} ]
      | sort_by([(.p | rank), .n]) | .[] | "\(.p)\t#\(.n)\t\(.t)"' 2>/dev/null)" || return 2
  [ -n "$out" ] || return 1
  printf '%s\n' "$out"
}

# Claim markers on one issue, as TSV. Statuses are zb_parse_claims's.
zb_issue_claims() { # <issue-number>
  local bodies
  bodies="$(gh issue view "$1" --repo "$ZB_REPO" --json comments --jq '[.comments[].body]' 2>/dev/null)" || return 2
  printf '%s' "$bodies" | zb_parse_claims
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
  local n="$1" intent="${2:-unspecified}" id now until
  id="$(zb_agent_id)"; now="$(zb_now)"; until="$(zb_until)"
  gh issue comment "$n" --repo "$ZB_REPO" --body \
"🔒 Claimed by agent \`$id\`. Lease until $until (UTC). Intent: $intent.
<!-- zb-claim agent=\"$id\" at=\"$now\" until=\"$until\" -->" >/dev/null || return 2
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
  local claims id cutoff live winner
  id="$(zb_agent_id)"
  claims="$(zb_issue_claims "$1")" || {
    [ $? -eq 1 ] && { echo "zb-claim: no claim markers on #$1" >&2; return 1; }
    return 2
  }
  cutoff="$(date -u -d "-${ZB_LEASE_SECONDS} seconds" +%Y-%m-%dT%H:%M:%SZ)"
  live="$(printf '%s\n' "$claims" | awk -F'\t' -v c="$cutoff" '$2 >= c')"
  [ -n "$live" ] || { echo "zb-claim: no claim inside the current lease window on #$1" >&2; return 1; }
  winner="$(printf '%s\n' "$live" | zb_earliest_claim | cut -f1)"
  if [ "$winner" = "$id" ]; then
    echo "verified: #$1 is held by $id"
  else
    echo "LOST RACE on #$1 — $winner claimed first. Release and pick other work." >&2
    return 1
  fi
}

zb_heartbeat() { # <issue-number>
  local id now until
  id="$(zb_agent_id)"; now="$(zb_now)"; until="$(zb_until)"
  gh issue comment "$1" --repo "$ZB_REPO" --body \
"⏱️ Lease refreshed by \`$id\` until $until (UTC).
<!-- zb-claim agent=\"$id\" at=\"$now\" until=\"$until\" -->" >/dev/null || return 2
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

zb_release() { # <issue-number> [--abandon]
  if [ "${2:-}" = "--abandon" ]; then
    gh issue edit "$1" --repo "$ZB_REPO" --remove-label "$ZB_CLAIM_LABEL" --remove-assignee "@me" >/dev/null || return 2
    zb_set_status "$1" "$ZB_STATUS_TODO" || return 2
    echo "abandoned #$1 — label and assignee removed, board back to Todo"
  else
    gh issue edit "$1" --repo "$ZB_REPO" --remove-label "$ZB_CLAIM_LABEL" >/dev/null || return 2
    echo "released the working label on #$1 (the open PR keeps it In Progress)"
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
    state)     zb_issue_lease_state "$@" ;;
    reap)      zb_reap; rc=$?; [ $rc -eq 1 ] && echo "no stale claims"; [ $rc -eq 2 ] && { echo "REAP READ FAILED" >&2; exit 2; }; exit 0 ;;
    id)        zb_agent_id ;;
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
  reap                       every claimed issue whose lease has expired
  id                         this agent's id (worktree@branch)

Exit statuses on reads: 0 = data, 1 = genuinely empty, 2 = READ FAILED.
Never treat 2 as "nothing to do".
USAGE
      ;;
  esac
fi
