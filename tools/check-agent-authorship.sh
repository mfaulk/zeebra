#!/usr/bin/env bash
#
# Reject commits that name a coding agent as author, committer or co-author (#1058).
#
#   tools/check-agent-authorship.sh <base> <head> [<text-file>...]
#
# Every commit in <base>..<head> is checked: its author, its committer, and every
# `Co-authored-by:` line in its message. Each <text-file> (in CI, the pull request body) is scanned
# for `Co-authored-by:` lines too, because a squash merge can carry them into the commit that lands
# on main — which is how #1022 put a Claude trailer on main.
#
# Some agent names are also given names: a "Claude Monet" or "Devin Smith" is a person. Those names
# count as an agent only when nothing but product words, version numbers or bot markers accompanies
# them ("Claude", "Claude Opus 5.5", "devin-ai-integration[bot]").
#
# Exit status, three outcomes rather than two (CLAUDE.md §0):
#
#   0   no agent identity in the range or the text files
#   1   at least one agent identity found; each is reported on stderr
#   2   a read FAILED — an unresolvable commit or an unreadable file. Never a pass.
#   64  usage error

set -uo pipefail

caa_git() { "${ZEEBRA_CAA_GIT:-git}" "$@"; }

# Names that are only ever an agent, matched as whole tokens.
CAA_AGENT_TOKENS=' anthropic openai codex chatgpt gpt gemini deepseek copilot aider qwen grok cursoragent windsurf codeium openhands opendevin tabnine '
# Names a person can also have, an agent only when every other token is in CAA_PRODUCT_TOKENS.
CAA_AMBIGUOUS_TOKENS=' claude devin jules cursor kimi mistral cline '
CAA_PRODUCT_TOKENS=' code opus sonnet haiku fable instant ai agent bot integration labs google developer cli assist coder swe '
# Email domains that only agents commit from; subdomains count.
CAA_AGENT_DOMAINS=' anthropic.com openai.com deepseek.com cursor.com cursor.sh devin.ai cognition.ai '

caa_lower() { printf '%s' "$1" | tr '[:upper:]' '[:lower:]'; }

# Whether a name is an agent's, by the token rules above. Pure.
caa_name_is_agent() { # <name>
  local tokens t ambiguous=0 other=0
  tokens="$(caa_lower "$1" | tr -c 'a-z0-9\n' ' ')"
  case " $tokens " in *" amazon q "*) return 0 ;; esac
  for t in $tokens; do
    case "$CAA_AGENT_TOKENS" in *" $t "*) return 0 ;; esac
    case "$CAA_AMBIGUOUS_TOKENS" in *" $t "*) ambiguous=1; continue ;; esac
    case "$CAA_PRODUCT_TOKENS" in *" $t "*) continue ;; esac
    case "$t" in '' | *[!0-9]* ) ;; *) continue ;; esac
    case "$t" in v[0-9]*) continue ;; esac
    other=1
  done
  [ "$ambiguous" -eq 1 ] && [ "$other" -eq 0 ]
}

# 0 if <name> <email> is a coding agent's identity, 1 if not. Pure.
caa_is_agent() { # <name> <email>
  local email domain d login
  email="$(caa_lower "$2")"
  domain="${email##*@}"
  for d in $CAA_AGENT_DOMAINS; do
    case "$domain" in "$d" | *."$d") return 0 ;; esac
  done
  caa_name_is_agent "$1" && return 0
  # A GitHub noreply address carries the account login, which names the app for agent accounts.
  case "$domain" in
    users.noreply.github.com)
      login="${email%@*}"
      login="${login#*+}"
      caa_name_is_agent "$login" && return 0
      ;;
  esac
  return 1
}

# The `Co-authored-by:` lines of a text as "name<TAB>email" rows, matched case-insensitively. Pure.
caa_coauthors() { # <text>
  printf '%s\n' "$1" | awk '
    tolower($0) ~ /^[ \t]*co-authored-by:/ {
      line = $0
      sub(/^[ \t]*[^:]*:[ \t]*/, "", line)
      email = ""
      if (match(line, /<[^>]*>/)) {
        email = substr(line, RSTART + 1, RLENGTH - 2)
        line = substr(line, 1, RSTART - 1)
      }
      sub(/[ \t]+$/, "", line)
      printf "%s\t%s\n", line, email
    }'
}

caa_usage() {
  cat >&2 <<'USAGE'
usage: tools/check-agent-authorship.sh <base> <head> [<text-file>...]

Fails when a commit in <base>..<head>, or a Co-authored-by line in a text file, names a coding agent.

  0 clean   1 agent identity found   2 a read failed   64 usage
USAGE
}

caa_main() {
  if [ "$#" -lt 2 ]; then
    caa_usage
    return 64
  fi
  local base="$1" head="$2" found=0 commits c header body name email role file
  shift 2

  for c in "$base" "$head"; do
    caa_git rev-parse --verify --quiet "$c^{commit}" >/dev/null || {
      printf 'check-agent-authorship: READ FAILED — %s is not a commit here\n' "$c" >&2
      return 2
    }
  done
  commits="$(caa_git rev-list "$base..$head" 2>/dev/null)" || {
    printf 'check-agent-authorship: READ FAILED — could not list %s..%s\n' "$base" "$head" >&2
    return 2
  }

  report() { # <where> <role> <name> <email>
    printf '%s: %s is a coding agent: %s <%s>\n' "$1" "$2" "$3" "$4" >&2
    found=1
  }

  for c in $commits; do
    header="$(caa_git log -1 --format='author%x09%an%x09%ae%ncommitter%x09%cn%x09%ce' "$c" 2>/dev/null)" &&
      body="$(caa_git log -1 --format=%B "$c" 2>/dev/null)" || {
      printf 'check-agent-authorship: READ FAILED — could not read commit %s\n' "$c" >&2
      return 2
    }
    while IFS="$(printf '\t')" read -r role name email; do
      [ -n "$role" ] || continue
      caa_is_agent "$name" "$email" && report "commit ${c:0:12}" "$role" "$name" "$email"
    done <<<"$header"
    while IFS="$(printf '\t')" read -r name email; do
      [ -n "$name$email" ] || continue
      caa_is_agent "$name" "$email" && report "commit ${c:0:12}" co-author "$name" "$email"
    done <<<"$(caa_coauthors "$body")"
  done

  for file in "$@"; do
    [ -r "$file" ] || {
      printf 'check-agent-authorship: READ FAILED — cannot read %s\n' "$file" >&2
      return 2
    }
    while IFS="$(printf '\t')" read -r name email; do
      [ -n "$name$email" ] || continue
      caa_is_agent "$name" "$email" && report "$file" co-author "$name" "$email"
    done <<<"$(caa_coauthors "$(cat "$file")")"
  done

  if [ "$found" -eq 1 ]; then
    printf '\nCommits here are attributed to people, not coding agents (#1058). Reword the commits\n' >&2
    printf '(git rebase -i, then edit the author or drop the trailer) and force-push the branch.\n' >&2
    return 1
  fi
  return 0
}

if [ "${BASH_SOURCE[0]}" = "${0}" ]; then
  caa_main "$@"
fi
