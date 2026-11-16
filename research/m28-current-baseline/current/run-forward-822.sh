#!/usr/bin/env bash
# #822: the #751 whole-route cells at production F4 after #813, serial against 16 forward workers,
# on 16 dedicated physical cores. Build first (README "Fresh current cohort"), then commit, then run.
set -euo pipefail
cd "$(dirname "$0")/../../.."
target=/buildcache/cargo-target/zeebra-822
build_commit=d7f0f3e61b6b1d4fcf6028f0dff8740d96eb01a4
ZEEBRA_MACHINE=trpro-5995wx
ZEEBRA_AFFINITY=2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17
export ZEEBRA_MACHINE ZEEBRA_AFFINITY
exec tools/benchlock.sh m28-forward-822 taskset -c 2-17 \
  timeout --signal=TERM --kill-after=5 960 \
  python3 tools/external/whole-route-study.py \
    --binary "$target/bin/mq10_profile-822" \
    --scratch "$target/forward" \
    --output research/m28-current-baseline/current/forward-822.json.gz \
    --phase forward --build-commit "$build_commit"
