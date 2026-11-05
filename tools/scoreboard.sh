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
#   tools/scoreboard.sh ladder --write       # the nine full-width rows, one process each
#   tools/scoreboard.sh row poseidon31-cico-t16-rf2-rp0 --slice 0 --write
#
# ZEEBRA_WALL_SECONDS bounds each frontier row (default 600).
#
# ZEEBRA_CORES pins the run (default 0-7). ZEEBRA_MACHINE labels it; without one the hostname is
# used, which is what a cross-machine comparison keys on.
set -euo pipefail

TIER="${1:-smoke}"
shift || true

# A private target directory. The shared one is keyed by package and profile rather than by
# checkout, so two worktrees of this repository overwrite each other's rlib and an example can link
# against a library built from different source. That failure looks like a missing export.
#
# Forced rather than defaulted: this machine's shell profile exports a shared `CARGO_TARGET_DIR`,
# so `${CARGO_TARGET_DIR:-...}` would inherit exactly the directory the hazard lives in.
# `ZEEBRA_TARGET_DIR` overrides it deliberately.
export CARGO_TARGET_DIR="${ZEEBRA_TARGET_DIR:-$PWD/target}"
export RUSTC_WRAPPER=""
export ZEEBRA_AFFINITY="${ZEEBRA_CORES:-0-7}"

echo "building (release; the first build relinks under fat LTO and takes minutes)"
cargo build --release --example scoreboard

CORES="${ZEEBRA_CORES:-0-7}"
BINARY="$CARGO_TARGET_DIR/release/examples/scoreboard"

run() {
    if command -v taskset >/dev/null 2>&1; then
        taskset --cpu-list "$CORES" "$BINARY" "$@"
    else
        echo "taskset not found; running unpinned, which makes runtimes less comparable"
        "$BINARY" "$@"
    fi
}

# The full-width ladder: one process per row, because the wall-clock supervisor stops a run by
# leaving its thread behind and exiting — F4 has no cooperative time check. Nine rows, each
# unspecialized and then as a slice with all but two free inputs fixed at a precommitted seed.
if [ "$TIER" = "ladder" ]; then
    LADDER="rf2-rp0 rf2-rp2 rf2-rp4 rf4-rp0 rf4-rp2 rf4-rp4 rf6-rp0 rf6-rp2 rf6-rp4"
    for row in $LADDER; do
        id="poseidon31-cico-t16-$row"
        run row "$id" "$@" || echo "$id: the runner exited nonzero"
        run row "$id" --slice 0 "$@" || echo "$id slice: the runner exited nonzero"
    done
    exit 0
fi

echo "running tier $TIER on cores $CORES"
run "$TIER" "$@"
