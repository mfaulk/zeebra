#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
HOOK="$ROOT/.githooks/pre-push"
checks=0

check() {
    local expected="$1"
    shift
    local actual
    actual="$(printf '%s\0' "$@" | bash "$HOOK" --classify)"
    if [[ "$actual" != "$expected" ]]; then
        printf 'FAIL: expected %q, got %q for %q\n' "$expected" "$actual" "$*" >&2
        exit 1
    fi
    checks=$((checks + 1))
}

both=$'fmt=true\nrustdoc=true'
doc=$'fmt=false\nrustdoc=true'
skip=$'fmt=false\nrustdoc=false'

# A research-only push runs neither check.
check "$skip" docs/research/notes.md research/m30-symbolic/table.md tools/external/run.py
# A Rust source change runs fmt and rustdoc.
check "$both" src/grobner/f4/mod.rs
# A Rust file outside src/ (an example) still runs fmt and rustdoc.
check "$both" examples/symbolic_parallel_price.rs
# A Cargo.lock change runs rustdoc only.
check "$doc" Cargo.lock
# A Cargo.toml change runs rustdoc only.
check "$doc" Cargo.toml
# The README is included into the crate docs, so it runs rustdoc.
check "$doc" README.md
# Guide pages are included into the crate docs, so they run rustdoc.
check "$doc" docs/guide/f4.md
# A non-Rust file under src/ can be include_str!'d, so it runs rustdoc.
check "$doc" src/grobner/external/data.json
# Mixed prose and source changes keep both checks.
check "$both" docs/research/notes.md src/lib.rs
# A suffix embedded mid-name does not count as a Rust file.
check "$skip" docs/research/notes.rs.md

# Truncated (non-NUL-terminated) input fails closed to both checks.
actual="$(printf 'docs/research/notes.md' | bash "$HOOK" --classify)"
[[ "$actual" == "$both" ]] || { echo "FAIL: truncated input gave $actual" >&2; exit 1; }
checks=$((checks + 1))

# End to end: the hook diffs pushed commits against origin/main and hands the steps to
# scripts/ci-lint.sh, stubbed here to record its arguments.
scratch="$(mktemp -d "${TMPDIR:-/tmp}/zb-pre-push-test.XXXXXX")"
trap 'rm -rf "$scratch"' EXIT
repo="$scratch/repo"
git init -q -b main "$repo"
git -C "$repo" config user.email test@example.invalid
git -C "$repo" config user.name test
mkdir -p "$repo/scripts" "$repo/docs/research"
cat > "$repo/scripts/ci-lint.sh" <<EOF
#!/usr/bin/env bash
echo "\$*" > "$scratch/ran"
EOF
git -C "$repo" add scripts
git -C "$repo" commit -q -m base
git -C "$repo" update-ref refs/remotes/origin/main HEAD

push_runs() {
    local sha
    sha="$(git -C "$repo" rev-parse HEAD)"
    rm -f "$scratch/ran"
    (cd "$repo" && printf 'refs/heads/x %s refs/heads/x %040d\n' "$sha" 0 | bash "$HOOK" 2>/dev/null)
    if [[ -f "$scratch/ran" ]]; then cat "$scratch/ran"; else echo skipped; fi
}

expect_run() {
    local expected="$1" what="$2" actual
    actual="$(push_runs)"
    if [[ "$actual" != "$expected" ]]; then
        printf 'FAIL: %s: expected %q, got %q\n' "$what" "$expected" "$actual" >&2
        exit 1
    fi
    checks=$((checks + 1))
}

# A push whose commits touch only research prose exits without running ci-lint.
echo note > "$repo/docs/research/notes.md"
git -C "$repo" add docs
git -C "$repo" commit -q -m prose
expect_run skipped "research-only push"

# Adding a Rust file on top runs fmt and rustdoc, judged against origin/main, not HEAD~1.
echo 'fn main() {}' > "$repo/lib.rs"
git -C "$repo" add lib.rs
git -C "$repo" commit -q -m rust
expect_run "fmt rustdoc" "rust push"

# A branch deletion (all-zero local sha) has nothing to check.
rm -f "$scratch/ran"
(cd "$repo" && printf '(delete) %040d refs/heads/x %040d\n' 0 0 | bash "$HOOK")
[[ ! -f "$scratch/ran" ]] || { echo "FAIL: deletion ran ci-lint" >&2; exit 1; }
checks=$((checks + 1))

# A branch that predates scripts/ci-lint.sh exits 0 with a notice instead of failing the push.
git -C "$repo" rm -q scripts/ci-lint.sh
echo 'fn f() {}' > "$repo/lib2.rs"
git -C "$repo" add lib2.rs
git -C "$repo" commit -q -m old-branch
sha="$(git -C "$repo" rev-parse HEAD)"
rc=0
notice="$(cd "$repo" && printf 'refs/heads/x %s refs/heads/x %040d\n' "$sha" 0 | bash "$HOOK" 2>&1)" || rc=$?
[[ $rc -eq 0 ]] || { echo "FAIL: missing ci-lint.sh exited $rc: $notice" >&2; exit 1; }
[[ "$notice" == *"predates scripts/ci-lint.sh"* ]] \
    || { echo "FAIL: missing ci-lint.sh gave no notice: $notice" >&2; exit 1; }
checks=$((checks + 1))

echo "pre-push: $checks checks passed"
