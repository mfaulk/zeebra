#!/usr/bin/env bash
# Run only under the existing benchmark lock and an outer 1200-second watchdog.
set -euo pipefail
study_root="${1:?fresh campaign directory required}"
exporter="${ZEEBRA_739_EXPORTER:?input-only exporter required}"
exporter_source="${ZEEBRA_739_EXPORTER_SOURCE:?exact exporter source required}"
reference_a="${ZEEBRA_739_REFERENCE_A:?exact reference archive required}"
reference_b="${ZEEBRA_739_REFERENCE_B:?exact reference archive required}"
test ! -e "$study_root"
mkdir -p "$study_root"
run_stage() {
    local limit="$1" cutoff="$2" label="$3" result
    shift 3
    if timeout --foreground --signal=TERM --kill-after=3s "$limit" \
      python3 tools/external/comparand-scaling.py \
      --binary "$exporter" --input-source "$exporter_source" \
      --references "$reference_a" "$reference_b" \
      --scratch "$study_root/$label" --output "$study_root/$label.json.gz" \
      --wall 60 --campaign-wall "$cutoff" "$@"; then result=0; else result=$?; fi
    printf '%s %s\n' "$label" "$result" >> "$study_root/stage-exits.txt"
    case "$result" in 0|124) ;; *) exit "$result" ;; esac
}
run_stage 900 840 ordinary --engines groebner.jl --workers 1,2,4,8,16,32 \
  --fields 32003,2147483647 --rows katsura-4,mq-random-10,katsura-11,cyclic-7 --repeats 3 \
  --case-pairs 32003/katsura-4,32003/mq-random-10,32003/cyclic-7,2147483647/katsura-4,2147483647/mq-random-10,2147483647/katsura-11
run_stage 15 10 rust-diagnostic --engines groebner-rs --workers 1,8,16 \
  --fields 2147483647 --rows katsura-11 --repeats 1 --diagnostic
run_stage 165 105 julia-diagnostic --engines groebner.jl --workers 1,8,16 \
  --fields 2147483647 --rows katsura-11 --repeats 1 --diagnostic --julia-full-warmup
run_stage 120 60 wide --engines groebner.jl --workers 1,8,16 \
  --fields wide64 --rows katsura-4,mq-random-10,cyclic-7 --repeats 1
