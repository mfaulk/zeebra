#!/usr/bin/env bash
# #859: run the cost-model suites, one tools/benchlock.sh acquisition per suite.
#
#   T=/buildcache/cargo-target/zeebra-859 OUT=$T/m30 REPS=5 \
#     setsid bash research/m30-symbolic/run.sh walls stages components level
#
# Needs $T/bin/m29_cost_model (external-runners) and $T/bin/symbolic_cost_model
# (external-runners,research-work), built as research/m30-symbolic/README.md says.
set -u
: "${T:?target dir}" "${OUT:?output directory}"
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/../.." && pwd)"
cd "$root" || exit 2
export TMPDIR="$T/tmp"
mkdir -p "$OUT" "$TMPDIR"
status=0
for suite in "$@"; do
  case "$suite" in
  walls | stages) bin="$T/bin/m29_cost_model" ;;
  components | level) bin="$T/bin/symbolic_cost_model" ;;
  *) echo "unknown suite $suite" >&2; exit 64 ;;
  esac
  printf '%s\n' "{\"suite\":\"$suite\",\"context\":$(bash tools/cpu-context.sh 8-23)}" >>"$OUT/suite-starts.jsonl"
  # Inside a CCD reservation of 8-23 (another session's, often), queue on those CCDs through it;
  # otherwise take the machine-wide lock. Never both: the unscoped lock waits on the scoped one.
  if tools/bench-reserve.sh status >/dev/null 2>&1; then
    lock=(tools/bench-reserve.sh run zb-859 8-23)
  else
    lock=(tools/benchlock.sh zb-859)
  fi
  "${lock[@]}" timeout --signal=INT --kill-after=60s "${SUITE_WALL:-5400}" \
    python3 "$here/campaign.py" --binary "$bin" --suite "$suite" --reps "${REPS:-5}" \
    --output "$OUT/$suite.jsonl" || status=$?
done
exit "$status"
