#!/usr/bin/env bash
# #1075's adjacent-round campaign: every row in the three buffer modes, fresh processes, one at a
# time, the arm order rotated each repetition so no arm always runs first.
# Usage: run.sh <binary> <rows-file> <out.jsonl> [reps]
set -euo pipefail
bin=$1
rows=$2
out=$3
reps=${4:-9}
arms=(off count reuse)

list=()
while read -r row; do list+=("$row"); done < <(grep -v -e '^#' -e '^$' "$rows")
: >"$out"
for ((rep = 0; rep < reps; rep++)); do
    for row in "${list[@]}"; do
        for ((k = 0; k < 3; k++)); do
            arm=${arms[$(((rep + k) % 3))]}
            line=$("$bin" --row "$row" --engine sigf4 --adjacent "$arm" --wall-s 600) ||
                line="{\"row\":\"$row\",\"adjacent_mode\":\"$arm\",\"status\":\"failed: exit $?\"}"
            printf '{"rep":%d,%s\n' "$rep" "${line#\{}" >>"$out"
        done
    done
done
