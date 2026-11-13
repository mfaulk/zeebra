#!/usr/bin/env bash
set -euo pipefail
cd /home/mfaulk/projects/zeebra-685
exec tools/benchlock.sh batch-splitting-685 taskset -c 0 python3 tools/external/batch-splitting-study.py \
  --binary /buildcache/cargo-target/zeebra-685/release/examples/batch_splitting_study \
  --scratch /buildcache/cargo-target/zeebra-685/campaign/scratch \
  --output /buildcache/cargo-target/zeebra-685/campaign/cohort.json.gz
