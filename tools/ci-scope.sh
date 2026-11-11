#!/usr/bin/env bash
# Classify NUL-separated git paths; only known documentation paths may skip Rust checks.
set -euo pipefail
rust=false
docs=false
seen=false
while IFS= read -r -d '' path; do
    seen=true
    case "$path" in
        README.md|docs/guide/*.md) docs=true ;;
        docs/*.md|research/*.md|CHANGELOG.md|CLAUDE.md) ;;
        *) rust=true; docs=true ;;
    esac
done
# Empty or truncated input is not evidence of a documentation-only change.
if [[ "$seen" == false || -n "$path" ]]; then
    rust=true
    docs=true
fi
printf 'rust=%s\ndocs=%s\n' "$rust" "$docs"
