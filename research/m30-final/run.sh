#!/usr/bin/env bash
# #862: the M30 final cohort, one lock acquisition per suite.
#
#   T=/buildcache/cargo-target/zeebra-862 OUT=$T/m30 REPS=9 bash research/m30-final/run.sh walls stages census
#
# walls|stages|census run campaign.py over $T/bin/m29_cost_model{,_work} (the final main) and
# $T/bin/base/m29_cost_model{,_work} (the freeze library), interleaved. The comparands run through
# #834's research/m29-baseline/run.sh (`wide` with WIDE_CELLS, `mq10`), unchanged. Inside a CCD 1-2
# reservation the lock is `bench-reserve.sh run`, otherwise `benchlock.sh`; never both.
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
  walls | stages) final="$T/bin/m29_cost_model" base="$T/bin/base/m29_cost_model" ;;
  census) final="$T/bin/m29_cost_model_work" base="$T/bin/base/m29_cost_model_work" ;;
  *) echo "unknown suite $suite" >&2; exit 64 ;;
  esac
  if tools/bench-reserve.sh status >/dev/null 2>&1; then
    lock=(tools/bench-reserve.sh run "${TAG:-zb-862}" 8-23)
  else
    lock=(tools/benchlock.sh "${TAG:-zb-862}")
  fi
  reps="${REPS:-9}"
  [ "$suite" = census ] && reps=1
  # One acquisition: the context is read inside it, where it describes the suite, not the queue.
  "${lock[@]}" bash -c 'printf "%s\n" "{\"suite\":\"$1\",\"context\":$(bash tools/cpu-context.sh 8-23)}" >>"$2"
    shift 2; exec timeout --signal=INT --kill-after=60s "$@"' _ "$suite" "$OUT/suite-starts.jsonl" \
    "${SUITE_WALL:-7200}" python3 "$here/campaign.py" --baseline "$base" --final "$final" \
    --suite "$suite" --reps "$reps" --output "$OUT/$suite.jsonl" || status=$?
done
exit "$status"
