#!/usr/bin/env bash
# #1077's bench-host whole solves: one solve per fresh process, arms interleaved in a rotating
# order, each process pinned.
#
#   research/gf2-residual/fresh.sh <binary> <out.tsv> <cpus> <workers> <reps> <set>... [-- <arm>...]
#
# Run it under tools/benchlock.sh; the caller pins nothing, this script pins each process to <cpus>.
set -euo pipefail

binary="$1"
out="$2"
cpus="$3"
workers="$4"
reps="$5"
shift 5
sets=()
while (($#)) && [[ "$1" != "--" ]]; do
  sets+=("$1")
  shift
done
[[ "${1:-}" == "--" ]] && shift
arms=("$@")
((${#arms[@]})) || arms=(packed eager auto auto-eager)

printf 'set\tinstance\tarm\trep\tworkers\tbasis\twall_ms\telim_ms\tbatches\tpacked_batches\tresidual_batches\tpeak_rss_kib\n' >"$out"
for set in "${sets[@]}"; do
  mapfile -t instances < <("$binary" list "$set")
  for instance in "${instances[@]}"; do
    for ((rep = 0; rep < reps; rep++)); do
      for ((offset = 0; offset < ${#arms[@]}; offset++)); do
        arm="${arms[$(((rep + offset) % ${#arms[@]}))]}"
        row="$(taskset -c "$cpus" "$binary" one "$set" "$instance" "$arm" "$workers")"
        IFS=$'\t' read -r label arm_out workers_out rest <<<"$row"
        printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$set" "$label" "$arm_out" "$rep" "$workers_out" "$rest" >>"$out"
      done
    done
  done
done
