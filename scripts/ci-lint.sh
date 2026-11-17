#!/usr/bin/env bash
# The checks of CI's "Format and lint" job, one step per subcommand, so the workflow and the
# pre-push hook (.githooks/pre-push) run the same commands and cannot drift apart.
#
# CARGO_TARGET_DIR and TMPDIR are the caller's. Off CI, an unset CARGO_TARGET_DIR defaults to
# /buildcache when it exists, never to the worktree: $HOME is the btrfs system drive, and heavy
# link output there stalls every writer on the machine (CLAUDE.md §1).
set -euo pipefail

usage() {
    cat >&2 <<'EOF'
usage: scripts/ci-lint.sh <step>...
steps: fmt clippy clippy-no-default proptest-graph rustdoc package all
EOF
    exit 64
}

default_target_dir() {
    [[ -n "${CARGO_TARGET_DIR:-}" || -n "${CI:-}" ]] && return 0
    local base=/buildcache/cargo-target
    [[ -d "$base" && -w "$base" ]] || return 0
    local top
    top="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
    CARGO_TARGET_DIR="$base/zeebra-lint-$(basename "$top")"
    export CARGO_TARGET_DIR
}

step() {
    case "$1" in
        fmt) cargo fmt --all --check ;;
        clippy) cargo clippy --all-targets --all-features -- -D warnings ;;
        # The crate as a consumer gets it with `default-features = false`.
        clippy-no-default) cargo clippy --all-targets --no-default-features -- -D warnings ;;
        # proptest belongs behind the `proptest` feature (#676); a lost `optional = true` would
        # not fail clippy, so check the graph a default consumer gets.
        proptest-graph)
            if cargo tree --locked -e normal --prefix none | grep -q '^proptest '; then
                echo "proptest is a normal dependency of a default build; gate it behind the feature" >&2
                return 1
            fi
            ;;
        # All features, matching `package.metadata.docs.rs`.
        rustdoc) RUSTDOCFLAGS="${RUSTDOCFLAGS:+$RUSTDOCFLAGS }-D warnings" cargo doc --no-deps --all-features --locked ;;
        package) cargo package --locked ;;
        all)
            local s
            for s in fmt clippy clippy-no-default proptest-graph rustdoc package; do step "$s"; done
            ;;
        *) usage ;;
    esac
}

[[ $# -gt 0 ]] || usage
cd "$(dirname "${BASH_SOURCE[0]}")/.."
default_target_dir
for s in "$@"; do
    echo "ci-lint: $s" >&2
    step "$s"
done
