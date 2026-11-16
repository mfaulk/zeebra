#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
checks=0
check() {
    local expected="$1"
    shift
    local actual
    actual="$(printf '%s\0' "$@" | bash "$ROOT/tools/ci-scope.sh")"
    if [[ "$actual" != "$expected" ]]; then
        printf 'FAIL: expected %q, got %q for %q\n' "$expected" "$actual" "$*" >&2
        exit 1
    fi
    checks=$((checks + 1))
}
full=$'rust=true\ndocs=true\ncomparand=true'
code=$'rust=true\ndocs=true\ncomparand=false'
docs=$'rust=false\ndocs=true\ncomparand=false'
prose=$'rust=false\ndocs=false\ncomparand=false'
# Source changes require every Rust check.
check "$code" src/lib.rs
# Workflow changes exercise the full pipeline.
check "$full" .github/workflows/rust.yml
# Build configuration changes require every Rust check.
check "$code" Cargo.toml Cargo.lock .cargo/config.toml
# Unknown paths fail closed to the full suite.
check "$code" new-file.txt
# README examples continue through Rustdoc and doctests.
check "$docs" README.md
# Guide examples continue through Rustdoc and doctests.
check "$docs" docs/guide/f4.md
# Research prose needs provenance checks without compiling Rust.
check "$prose" docs/research/classical-benchmarks.md research/competitive/CURATION.md
# Changed measurement records still exercise their Rust validation.
check "$code" research/competitive/results/history.json
# Mixed source and prose changes retain full coverage.
check "$code" README.md docs/research/notes.md src/util/json.rs
# Markdown in source directories cannot bypass the suite.
check "$code" src/new.md
# Retained comparand records select the comparand replay.
check "$full" research/comparand-scaling/inventory.json
# The replay checks the generated board, so comparand Markdown selects it too.
check "$full" research/comparand-scaling/BOARD.md
# The replay's Python modules select it.
check "$full" tools/external/proof_artifacts.py
# The replay's own tests select it.
check "$full" tools/test/comparand-scaling-test.py
# Changing the scope rules selects every check.
check "$full" tools/ci-scope.sh
# NUL separation preserves unusual filenames and prevents suffix spoofing.
check "$code" $'docs/research/note.md\nsrc/lib.rs'
# An empty comparison cannot silently skip checks.
actual="$(bash "$ROOT/tools/ci-scope.sh" < /dev/null)"
[[ "$actual" == "$full" ]]
checks=$((checks + 1))
# A truncated path after valid prose still selects all checks.
actual="$(printf 'docs/research/note.md\0src/lib.rs' | bash "$ROOT/tools/ci-scope.sh")"
[[ "$actual" == "$full" ]]
checks=$((checks + 1))
# Renaming code into the prose allowlist still reports the removed source path.
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
git -C "$scratch" init -q
mkdir -p "$scratch/src" "$scratch/docs/research"
printf 'source\n' > "$scratch/src/lib.rs"
git -C "$scratch" add src/lib.rs
git -C "$scratch" -c user.name=Test -c user.email=test@example.invalid commit -qm initial
base="$(git -C "$scratch" rev-parse HEAD)"
git -C "$scratch" mv src/lib.rs docs/research/archive.md
git -C "$scratch" -c user.name=Test -c user.email=test@example.invalid commit -qm rename
actual="$(git -C "$scratch" diff --no-renames --name-only -z "$base...HEAD" | bash "$ROOT/tools/ci-scope.sh")"
[[ "$actual" == "$code" ]]
checks=$((checks + 1))
printf 'ok: %s CI scope checks passed\n' "$checks"
