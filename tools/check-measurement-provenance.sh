#!/usr/bin/env bash
#
# Every document that publishes a measurement says which commit the measurement came from.
#
#   tools/check-measurement-provenance.sh [file...]
#
# With no arguments, checks `docs/research/*.md` and `docs/MILESTONE-*.md`.
#
# #335 is the defect this exists to stop recurring: twenty-odd figures were on record with the
# machine, the pinning, the build flags and the lock all stated, and the commit stated nowhere — so
# when #318 found a figure 1.2x off the one on record, the one experiment that would settle it
# ("re-measure at the old commit") could not be set up from what was written down. A checklist item
# already asked for this and was not followed, which is why it is a check and not a convention.
#
# The rule: a document containing a table row with a timing or a memory figure carries a
# declaration in its header —
#
#   **Measured at:** `93bb1c2` …            a commit, or several
#   **Measured at:** unrecorded — <why>     the era is genuinely unrecoverable, and the document
#                                           says so rather than leaving the reader to assume
#   **Measured at:** not measured here — …  every figure is quoted from a cited source, so there is
#                                           no commit of ours to name
#
# `Frozen at:` is accepted as the same thing; `docs/research/m27-baseline.md` already spells it that
# way. The declaration must be in the first 40 lines, because a declaration below the figures is one
# the reader meets too late.
#
# What this does *not* check, deliberately: whether the commit is the one the binary was built from,
# whether it is reachable from `main` (#505), or whether the figure reproduces at it (#318 found the
# answer is sometimes no — the session and the ambient load matter too, which is why
# `tools/benchlock.sh` now records `load=`). A lint can hold the line that the field is populated;
# only a re-measurement can say it is right.
#
# Exit status, three outcomes rather than two (CLAUDE.md §0):
#
#   0   every document that publishes a measurement declares its era
#   1   at least one does not — the finding, printed one line per document
#   2   a file could not be read, or the default set matched nothing. Not "clean": a lint that
#       reported 0 after reading nothing would assert exactly what it exists to doubt
#   64  usage error

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# How far into a document the declaration may be and still be met before the figures.
readonly HEADER_LINES=40

# A table row carrying a figure with a time or memory unit. The unit must be followed by a
# non-alphanumeric or end of line, so `3 steps` and `4 seeds` are not timings.
readonly FIGURE_RE='^[[:space:]]*\|.*[0-9]([.,][0-9]+)?[[:space:]]?(ms|µs|μs|ns|s|h|GiB|MiB|KiB|GB|MB|kB)([^[:alnum:]]|$)'

# The declaration, and the two values that satisfy it.
readonly DECLARATION_RE='\*\*(Measured at|Frozen at):\*\*'
readonly COMMIT_RE='`[0-9a-f]{7,40}`'
readonly UNRECORDED_RE='unrecorded|not measured here'

# The leading comment block, less its `#` markers: the usage text and the file header are the same
# text, so neither can drift from the other.
usage() {
  awk 'NR == 1 { next } /^#/ { sub(/^# ?/, ""); print; next } { exit }' "${BASH_SOURCE[0]}"
}

files=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    -h | --help)
      usage
      exit 0
      ;;
    --)
      shift
      files+=("$@")
      break
      ;;
    -*)
      printf 'unknown option: %s\n' "$1" >&2
      usage >&2
      exit 64
      ;;
    *)
      files+=("$1")
      shift
      ;;
  esac
done

if [[ "${#files[@]}" -eq 0 ]]; then
  for candidate in "$ROOT"/docs/research/*.md "$ROOT"/docs/MILESTONE-*.md; do
    [[ -f "$candidate" ]] && files+=("$candidate")
  done
  if [[ "${#files[@]}" -eq 0 ]]; then
    echo "READ FAILED: the default document set matched nothing under $ROOT/docs" >&2
    exit 2
  fi
fi

# The first line number carrying a published figure, or empty if the document publishes none.
first_figure_line() {
  grep -nE "$FIGURE_RE" -- "$1" | head -1 | cut -d: -f1
}

# 0 if the document's header declares an era, 1 if it declares one that names neither a commit nor
# `unrecorded`, 2 if it declares nothing at all.
declaration_state() {
  local declared
  declared="$(head -n "$HEADER_LINES" -- "$1" | grep -E "$DECLARATION_RE")" || return 2
  [[ -n "$declared" ]] || return 2
  if printf '%s\n' "$declared" | grep -qE "$COMMIT_RE|$UNRECORDED_RE"; then
    return 0
  fi
  return 1
}

violations=0
for file in "${files[@]}"; do
  if [[ ! -r "$file" ]]; then
    printf 'READ FAILED: %s is not readable\n' "$file" >&2
    exit 2
  fi

  line="$(first_figure_line "$file")"
  [[ -n "$line" ]] || continue

  state=0
  declaration_state "$file" || state=$?
  case "$state" in
    0) ;;
    1)
      printf '%s: declares an era that names neither a commit nor `unrecorded` (first figure at line %s)\n' \
        "$file" "$line"
      violations=$((violations + 1))
      ;;
    *)
      printf '%s: publishes a measurement and declares no era (first figure at line %s)\n' \
        "$file" "$line"
      violations=$((violations + 1))
      ;;
  esac
done

if [[ "$violations" -gt 0 ]]; then
  printf '\n%s document(s) publish a measurement without saying which commit it came from (#335).\n' \
    "$violations"
  printf 'Add to the header: **Measured at:** `<sha>` — or `unrecorded`, with the reason.\n'
  exit 1
fi

exit 0
