#!/usr/bin/env bash
# Classify NUL-separated git paths; only known documentation paths may skip Rust checks.
# `comparand` selects the slow retained-comparand replay, which reads only its own records and
# the Python under tools/external/.
set -euo pipefail
rust=false
docs=false
comparand=false
seen=false
while IFS= read -r -d '' path; do
    seen=true
    case "$path" in
        # Before the prose rule: the replay checks BOARD.md against its records.
        research/comparand-scaling/*|tools/external/*|tools/test/comparand-scaling-test.py|\
        tools/ci-scope.sh|.github/workflows/*)
            rust=true; docs=true; comparand=true ;;
        README.md|docs/guide/*.md) docs=true ;;
        docs/*.md|research/*.md|CHANGELOG.md|CLAUDE.md) ;;
        *) rust=true; docs=true ;;
    esac
done
# Empty or truncated input is not evidence of a documentation-only change.
if [[ "$seen" == false || -n "$path" ]]; then
    rust=true
    docs=true
    comparand=true
fi
printf 'rust=%s\ndocs=%s\ncomparand=%s\n' "$rust" "$docs" "$comparand"
