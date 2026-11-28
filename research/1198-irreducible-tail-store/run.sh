#!/usr/bin/env bash
# #1198's count: every row once on the signature engine with --tail-store. Counts only, so the
# runs are unpinned and run side by side.
# A row named `<row>+lane` runs with the opt-in lanes on.
# Usage: run.sh <reuse_census binary> <rows-file> <out-dir> [jobs]
set -euo pipefail
bin=$1
rows=$2
out=$3
jobs=${4:-6}
mkdir -p "$out"

run_one() {
    local bin=$1 row=${2%+lane} file=$3 line flags=()
    [[ $2 == *+lane ]] && flags=(--lane)
    if line=$( (ulimit -v $((48 * 1024 * 1024)); timeout 3700 \
        "$bin" --row "$row" --engine sigf4 --tail-store --wall-s 3600 "${flags[@]}") 2>/dev/null); then
        printf '%s\n' "$line" >"$file"
    else
        printf '{"row":"%s","engine":"sigf4","status":"failed: exit %s"}\n' "$row" "$?" >"$file"
    fi
}
export -f run_one

while read -r row; do
    [[ -z $row || $row == \#* ]] && continue
    printf '%s %s %s\n' "$bin" "$row" "$out/$row.json"
done <"$rows" | xargs -P "$jobs" -L 1 bash -c 'run_one "$@"' _
