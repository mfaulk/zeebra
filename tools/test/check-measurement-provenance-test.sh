#!/usr/bin/env bash
#
# Unit tests for `tools/check-measurement-provenance.sh`.
#
# The script's whole job is a classification — does this document publish a measurement, and does
# it say which commit the measurement came from — so the tests are documents written to a temporary
# directory and checked by exit status. No repository and no git history is involved, which is the
# point: the lint must not need either.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LINT="$SCRIPT_DIR/check-measurement-provenance.sh"

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

failures=0
checks=0

# Assert the lint exits with the expected status over the given files, and say which case failed.
expect_status() {
  local want="$1" name="$2"
  shift 2
  local out rc=0
  out="$(bash "$LINT" "$@" 2>&1)" || rc=$?
  checks=$((checks + 1))
  if [[ "$rc" != "$want" ]]; then
    printf 'FAIL %s: expected status %s, got %s\n%s\n' "$name" "$want" "$rc" "$out" >&2
    failures=$((failures + 1))
  fi
}

# Assert the lint's output mentions the given text, so a violation names the file it is about.
expect_output_contains() {
  local needle="$1" name="$2"
  shift 2
  local out
  out="$(bash "$LINT" "$@" 2>&1)"
  checks=$((checks + 1))
  if [[ "$out" != *"$needle"* ]]; then
    printf 'FAIL %s: output does not mention %q\n%s\n' "$name" "$needle" "$out" >&2
    failures=$((failures + 1))
  fi
}

write_doc() {
  local path="$1"
  shift
  printf '%s\n' "$@" >"$WORK/$path"
}

# A table row carrying a timing, with a declaration naming a commit.
write_doc declared.md \
  '# A document' \
  '' \
  '**Measured at:** `93bb1c2`, publication bound.' \
  '' \
  '| order | time |' \
  '|---|---:|' \
  '| 162 | 3.624 ms |'

# The same table with no declaration anywhere.
write_doc undeclared.md \
  '# A document' \
  '' \
  'Some prose about the measurement.' \
  '' \
  '| order | time |' \
  '|---|---:|' \
  '| 162 | 3.624 ms |'

# No figure in any table, so nothing to date.
write_doc no-figures.md \
  '# A source study' \
  '' \
  '| library | licence |' \
  '|---|---|' \
  '| singular | GPL-2.0 |'

# The era is genuinely unrecoverable, and the document says so.
write_doc unrecorded.md \
  '# A document' \
  '' \
  '**Measured at:** unrecorded — the generating run was not retained.' \
  '' \
  '| rung | peak RSS |' \
  '|---|---:|' \
  '| 20 000 000 | 14.41 GiB |'

# A document whose figures are all cited from the literature measured nothing here, and says so.
write_doc cited.md \
  '# A source study' \
  '' \
  '**Measured at:** not measured here — every figure is quoted from the cited papers.' \
  '' \
  '| instance | time reported |' \
  '|---|---:|' \
  '| (11,9,8)-MinRank | 15.1 h |'

# A declaration that names no commit and does not say `unrecorded` is not a declaration.
write_doc vague.md \
  '# A document' \
  '' \
  '**Measured at:** some time last week.' \
  '' \
  '| order | time |' \
  '|---|---:|' \
  '| 162 | 3.624 ms |'

# A declaration below the header window does not count: a reader meets the figures first.
{
  printf '# A document\n\n'
  for _ in $(seq 1 60); do printf 'Filler prose.\n'; done
  printf '\n| order | time |\n|---|---:|\n| 162 | 3.624 ms |\n'
  printf '\n**Measured at:** `93bb1c2`.\n'
} >"$WORK/late.md"

# Ratios and counts are not measurements with units, so a table of them needs no era.
write_doc ratios.md \
  '# A document' \
  '' \
  '| stage | factor | rows |' \
  '|---|---:|---:|' \
  '| interreduction | 4.18x | 387 |'

# `Frozen at:` is the spelling `m27-baseline.md` already uses, and is accepted.
write_doc frozen.md \
  '# The M27 baseline' \
  '' \
  '**Issue:** #451. **Frozen at:** `1985504`, re-verified at `53fbf50`.' \
  '' \
  '| problem | wall |' \
  '|---|---:|' \
  '| cyclic-8 | 41.2 s |'

echo "== cases =="
expect_status 0 'a declared document passes' "$WORK/declared.md"
expect_status 1 'an undeclared document fails' "$WORK/undeclared.md"
expect_output_contains 'undeclared.md' 'the violation names the file' "$WORK/undeclared.md"
expect_status 0 'a document with no figures needs no declaration' "$WORK/no-figures.md"
expect_status 0 'an explicitly unrecorded era passes' "$WORK/unrecorded.md"
expect_status 0 'a document citing only published figures passes' "$WORK/cited.md"
expect_status 1 'a declaration naming no commit fails' "$WORK/vague.md"
expect_status 1 'a declaration below the header window fails' "$WORK/late.md"
expect_status 0 'a table of ratios and counts needs no declaration' "$WORK/ratios.md"
expect_status 0 'the "Frozen at" spelling is accepted' "$WORK/frozen.md"

# One violation among several files is still a violation, and the passing files are not reported.
expect_status 1 'a mixed file set fails' "$WORK/declared.md" "$WORK/undeclared.md"
expect_output_contains 'undeclared.md' 'the mixed set names the offender' \
  "$WORK/declared.md" "$WORK/undeclared.md"

# An unreadable path is a failed read (2), not a clean pass: silence must never read as compliance.
expect_status 2 'a missing file is a read failure, not a pass' "$WORK/does-not-exist.md"

# Usage errors are distinct from both findings and read failures.
expect_status 64 'an unknown option is a usage error' --no-such-option

echo
if [[ "$failures" -eq 0 ]]; then
  echo "ok: $checks checks passed"
  exit 0
fi
echo "FAILED: $failures of $checks checks" >&2
exit 1
