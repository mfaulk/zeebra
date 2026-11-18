#!/usr/bin/env bash
# One #901 measurement session: reserve CCDs 1-2 (unless another session already holds them),
# run one campaign suite under `bench-reserve run` (benchlock, CPUs 8-23), and release on any exit.
#
#   setsid research/m31-baseline/run.sh walls|split|probe OUTDIR [campaign.py args...]
#
# Binaries come from the private target directories the README names; build them first.
set -euo pipefail
suite="${1:?suite}"
out="${2:?output directory}"
shift 2
cd "$(dirname "$0")/../.."
timed=/buildcache/cargo-target/zeebra-901/release/examples
split=/buildcache/cargo-target/zeebra-901-split/release/examples
bin="$timed/sig_f4_study"
[ "$suite" = split ] && bin="$split/sig_f4_study"

rc=0
tools/bench-reserve.sh status >/dev/null || rc=$?
case $rc in
  0) owned=0; echo "reservation already held by another session; not releasing it" >&2 ;;
  1) tools/bench-reserve.sh reserve; owned=1 ;;
  *) echo "bench-reserve status failed (rc=$rc)" >&2; exit 2 ;;
esac
release() { if [ "$owned" = 1 ]; then tools/bench-reserve.sh release || tools/bench-reserve.sh release --force; fi; }
trap release EXIT

mkdir -p "$out"
tools/bench-reserve.sh run zb-901 8-23 python3 -u research/m31-baseline/campaign.py \
  --suite "$suite" --sig "$bin" --cost "$timed/m29_cost_model" --output "$out/$suite.jsonl" "$@"
