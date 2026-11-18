#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRIPT="$ROOT/tools/ci-research.sh"
checks=0
fail() {
    printf 'FAIL: %s\n' "$*" >&2
    exit 1
}

sets="$(bash "$SCRIPT" --sets)"

# The workflow matrix runs exactly the sets the script defines.
matrix="$(sed -n 's/^ *set: *\[\(.*\)\] *$/\1/p' "$ROOT/.github/workflows/rust.yml" | tr -d ' ' | tr ',' '\n')"
[[ -n "$matrix" ]] || fail "no research matrix found in rust.yml"
[[ "$matrix" == "$sets" ]] || fail "rust.yml matrix ($(echo $matrix)) != script sets ($(echo $sets))"
checks=$((checks + 1))

# Every research feature in Cargo.toml has its own set, so a new one cannot silently join another's build.
while read -r feature; do
    grep -qx "$feature" <<<"$sets" || fail "Cargo.toml feature $feature has no research set"
    checks=$((checks + 1))
done < <(sed -n 's/^\(research-[a-z0-9-]*\) *=.*/\1/p' "$ROOT/Cargo.toml")

# A set compiles under its own feature only: a second feature set in one job is a second full build.
while read -r set; do
    body="$(awk -v s="    $set)" '$0 == s {on=1; next} on && /^ *;;$/ {exit} on' "$SCRIPT")"
    [[ -n "$body" ]] || fail "set $set has no case branch"
    used="$(grep -oE -- '--features [a-z0-9-]+' <<<"$body" | sort -u | cut -d' ' -f2 || true)"
    case "$set" in
        research-*) [[ "$used" == "$set" ]] || fail "set $set builds features: $(echo $used)" ;;
        *) [[ -z "$used" ]] || fail "set $set builds non-default features: $(echo $used)" ;;
    esac
    checks=$((checks + 1))
done <<<"$sets"

# An unknown set is a usage error, not a silent pass.
rc=0
bash "$SCRIPT" no-such-set >/dev/null 2>&1 || rc=$?
[[ $rc -eq 2 ]] || fail "unknown set exited $rc, expected 2"
checks=$((checks + 1))

printf 'ci-research: %d checks passed\n' "$checks"
