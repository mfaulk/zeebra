#!/usr/bin/env bash
# #1031's census campaign: every row once per engine with --census (untimed), and once per engine
# without it (the timed arm, whose wall, stage split, peak RSS and basis digest the census is read
# against). Usage: run.sh <census-binary> <timed-binary> <rows-file> <out-dir> [jobs]
set -euo pipefail
census_bin=$1
timed_bin=$2
rows=$3
out=$4
jobs=${5:-8}
mkdir -p "$out"

run_one() {
    local bin=$1 row=$2 engine=$3 mode=$4 file=$5
    local flags=()
    case $mode in
        census) flags=(--census) ;;
        timed) [[ $engine == f4 ]] && flags=(--stages) ;;
    esac
    # 180 s per timed run (the issue's budget; its 8 GiB is checked on the reported peak RSS). A
    # census run replays every batch three times, so it gets four times the wall, and a 32 GiB
    # address-space cap as a safety net for tail-reduction fill-in.
    local wall=180
    [[ $mode == census ]] && wall=720
    local line
    if line=$( (ulimit -v $((32 * 1024 * 1024)); timeout $((wall + 60)) \
        "$bin" --row "$row" --engine "$engine" --wall-s "$wall" "${flags[@]}") 2>/dev/null); then
        printf '%s\n' "$line" >"$file"
    else
        printf '{"row":"%s","engine":"%s","census":%s,"status":"failed: exit %s"}\n' \
            "$row" "$engine" "$([[ $mode == census ]] && echo true || echo false)" "$?" >"$file"
    fi
}
export -f run_one

while read -r row; do
    [[ -z $row || $row == \#* ]] && continue
    for engine in f4 sigf4; do
        printf '%s %s %s timed %s\n' "$timed_bin" "$row" "$engine" "$out/$row.$engine.timed.json"
        printf '%s %s %s census %s\n' "$census_bin" "$row" "$engine" "$out/$row.$engine.census.json"
    done
done <"$rows" | xargs -P "$jobs" -L 1 bash -c 'run_one "$@"' _
