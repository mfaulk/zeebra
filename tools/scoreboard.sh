#!/usr/bin/env bash
#
# Run a scoreboard tier and update research/scoreboard/.
#
# The rendering and the comparison live in the crate rather than in a script here, deliberately: a
# second implementation of "are these two runs of the same problem?" would be a second place for it
# to be wrong, and that rule is the one piece of this machinery that must not be. What this script
# is for is the measurement protocol around the runner — a private target directory, a pinned core
# set, and a stated affinity — which is not the crate's business.
#
#   tools/scoreboard.sh                      # smoke tier, writes nothing
#   tools/scoreboard.sh smoke --write        # smoke tier, updates research/scoreboard/
#   tools/scoreboard.sh stable --write       # adds the published MQ instances
#   tools/scoreboard.sh frontier --write     # adds the full-width rows
#
# ZEEBRA_CORES pins the run (default 0-7). ZEEBRA_MACHINE labels it; without one the hostname is
# used, which is what a cross-machine comparison keys on.
set -euo pipefail

TIER="${1:-smoke}"
shift || true

# A private target directory. The shared one is keyed by package and profile rather than by
# checkout, so two worktrees of this repository overwrite each other's rlib and an example can link
# against a library built from different source. That failure looks like a missing export.
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$PWD/target}"
export RUSTC_WRAPPER=""
export ZEEBRA_AFFINITY="${ZEEBRA_CORES:-0-7}"

echo "building (release; the first build relinks under fat LTO and takes minutes)"
cargo build --release --example scoreboard

CORES="${ZEEBRA_CORES:-0-7}"
if command -v taskset >/dev/null 2>&1; then
    echo "running tier $TIER on cores $CORES"
    exec taskset --cpu-list "$CORES" \
        "$CARGO_TARGET_DIR/release/examples/scoreboard" "$TIER" "$@"
else
    echo "taskset not found; running unpinned, which makes runtimes less comparable"
    exec "$CARGO_TARGET_DIR/release/examples/scoreboard" "$TIER" "$@"
fi
