#!/usr/bin/env bash
# Unit tests for tools/check-agent-authorship.sh (#1058).
#
# The matcher is tested as a pure function over (name, email) pairs, including the humans it must
# not reject. The range scan runs against a throwaway repository rather than a mock, because what it
# has to get right is which commits and which header fields it reads.
set -uo pipefail

CAA="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/check-agent-authorship.sh"
# shellcheck source=../check-agent-authorship.sh
. "$CAA"

pass=0 fail=0

check_rc() { # <label> <expected-rc> <actual-rc>
  if [ "$2" -eq "$3" ]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    printf 'FAIL  %s\n  expected rc: %s\n  actual rc:   %s\n' "$1" "$2" "$3" >&2
  fi
}

check() { # <label> <expected> <actual>
  if [ "$2" = "$3" ]; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    printf 'FAIL  %s\n  expected: %q\n  actual:   %q\n' "$1" "$2" "$3" >&2
  fi
}

agent() { caa_is_agent "$2" "$3"; check_rc "agent: $1" 0 $?; }
human() { caa_is_agent "$2" "$3"; check_rc "human: $1" 1 $?; }

# --- caa_is_agent: identities agents actually write ---------------------------

agent "Claude Code trailer" "Claude Opus 5.5" "noreply@anthropic.com"
agent "older Claude trailer" "Claude" "noreply@anthropic.com"
agent "bare Claude, any email" "Claude" "claude@example.com"
agent "Claude Code by name" "Claude Code" "someone@example.com"
agent "Claude Sonnet" "Claude Sonnet 4" "x@example.com"
agent "anthropic domain" "Some Bot" "bot@anthropic.com"
agent "anthropic subdomain" "Some Bot" "bot@mail.anthropic.com"
agent "Codex" "Codex" "codex@openai.com"
agent "codex by name only" "codex" "noreply@example.com"
agent "openai domain" "Someone" "agent@openai.com"
agent "Gemini" "Gemini" "gemini@example.com"
agent "Gemini Code Assist app" "gemini-code-assist[bot]" "176961590+gemini-code-assist[bot]@users.noreply.github.com"
agent "DeepSeek" "DeepSeek Coder" "x@example.com"
agent "deepseek domain" "Someone" "a@deepseek.com"
agent "Copilot coding agent" "Copilot" "198982749+Copilot@users.noreply.github.com"
agent "copilot-swe-agent app" "copilot-swe-agent[bot]" "198982749+Copilot@users.noreply.github.com"
agent "Cursor agent" "Cursor Agent" "cursoragent@cursor.com"
agent "Devin app" "devin-ai-integration[bot]" "158243242+devin-ai-integration[bot]@users.noreply.github.com"
agent "bare Devin" "Devin" "devin@example.com"
agent "Aider author suffix" "Matthew Faulkner (aider)" "mnfaulk@gmail.com"
agent "Jules app" "google-labs-jules[bot]" "161369871+google-labs-jules[bot]@users.noreply.github.com"
agent "ChatGPT" "ChatGPT" "x@example.com"
agent "GPT model name" "GPT-5" "x@example.com"
agent "Qwen" "Qwen Code" "x@example.com"
agent "Amazon Q app" "amazon-q-developer[bot]" "x@users.noreply.github.com"
agent "case-insensitive" "CLAUDE OPUS" "X@EXAMPLE.COM"

# --- caa_is_agent: humans and ordinary bots that must pass --------------------

human "the owner" "Matthew Faulkner" "mnfaulk@gmail.com"
human "owner noreply" "mfaulk" "mfaulk@users.noreply.github.com"
human "GitHub as committer" "GitHub" "noreply@github.com"
human "a human named Claude" "Claude Monet" "claude.monet@example.com"
human "a human named Devin" "Devin Smith" "devin@example.com"
human "a human named Jules" "Jules Verne" "jules@example.com"
human "dependabot" "dependabot[bot]" "49699333+dependabot[bot]@users.noreply.github.com"
human "github-actions" "github-actions[bot]" "41898282+github-actions[bot]@users.noreply.github.com"
human "surname containing a token" "Ann Codexter" "ann@example.com"
human "gmail, not google agent" "Someone" "someone@google.com"

# --- caa_coauthors: trailer extraction ----------------------------------------

msg='fix: a thing

Body text mentioning Co-authored-by: inline is not a trailer line.

Co-authored-by: Claude Opus 5.5 <noreply@anthropic.com>
co-authored-by: Jane Doe <jane@example.com>'
check "coauthors: every line, any case" \
  "Claude Opus 5.5	noreply@anthropic.com
Jane Doe	jane@example.com" "$(caa_coauthors "$msg")"
check "coauthors: none" "" "$(caa_coauthors 'no trailers here')"

# --- caa_main over a real repository ------------------------------------------

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
repo="$tmp/repo"
git init -q "$repo"
g() { git -C "$repo" -c user.name="Matthew Faulkner" -c user.email=mnfaulk@gmail.com "$@"; }
g commit -q --allow-empty -m base
base="$(g rev-parse HEAD)"
g commit -q --allow-empty -m "clean change"
clean="$(g rev-parse HEAD)"

out="$(cd "$repo" && caa_main "$base" "$clean" 2>&1)"; rc=$?
check_rc "main: a clean range passes" 0 "$rc"

g commit -q --allow-empty -m "change

Co-authored-by: Claude Opus 5.5 <noreply@anthropic.com>"
trailer="$(g rev-parse HEAD)"
out="$(cd "$repo" && caa_main "$base" "$trailer" 2>&1)"; rc=$?
check_rc "main: a Claude co-author fails" 1 "$rc"
case "$out" in *"${trailer:0:12}"*"Claude Opus 5.5"*) pass=$((pass + 1)) ;;
  *) fail=$((fail + 1)); printf 'FAIL  main: report names the commit and identity\n%s\n' "$out" >&2 ;; esac

git -C "$repo" -c user.name=Codex -c user.email=codex@openai.com commit -q --allow-empty -m "by codex"
authored="$(g rev-parse HEAD)"
out="$(cd "$repo" && caa_main "$trailer" "$authored" 2>&1)"; rc=$?
check_rc "main: an agent author fails" 1 "$rc"

GIT_COMMITTER_NAME=Gemini GIT_COMMITTER_EMAIL=gemini@example.com \
  git -C "$repo" -c user.name="Matthew Faulkner" -c user.email=mnfaulk@gmail.com commit -q --allow-empty -m "committed by gemini"
committed="$(g rev-parse HEAD)"
out="$(cd "$repo" && caa_main "$authored" "$committed" 2>&1)"; rc=$?
check_rc "main: an agent committer fails" 1 "$rc"

# Extra text files (the pull request body) are scanned for co-author lines too, because a squash
# merge can carry them into the commit that lands on main.
printf 'Summary\n\nCo-authored-by: DeepSeek <bot@deepseek.com>\n' >"$tmp/body.md"
out="$(cd "$repo" && caa_main "$base" "$clean" "$tmp/body.md" 2>&1)"; rc=$?
check_rc "main: an agent co-author in the PR body fails" 1 "$rc"
printf 'Summary only.\n' >"$tmp/clean.md"
out="$(cd "$repo" && caa_main "$base" "$clean" "$tmp/clean.md" 2>&1)"; rc=$?
check_rc "main: a clean PR body passes" 0 "$rc"

# A range git cannot read is a failed read, never a clean pass (CLAUDE.md §0).
out="$(cd "$repo" && caa_main "$base" deadbeefdeadbeefdeadbeefdeadbeefdeadbeef 2>&1)"; rc=$?
check_rc "main: an unreadable range is a failed read" 2 "$rc"
out="$(cd "$repo" && caa_main "$base" "$clean" "$tmp/missing.md" 2>&1)"; rc=$?
check_rc "main: a missing text file is a failed read" 2 "$rc"
out="$(caa_main 2>&1)"; rc=$?
check_rc "main: no arguments is a usage error" 64 "$rc"

printf '%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
