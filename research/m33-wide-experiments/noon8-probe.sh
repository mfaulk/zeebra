#!/usr/bin/env bash
# Untimed attribution of G2-1's Noon-8 elimination growth (#971 Gate C, owner condition on #965).
# Off the bench CPUs: base and head interleaved, the engine's own stage clocks, under glibc's default
# malloc and under `glibc.malloc.hugetlb=1` (transparent huge pages for the heap, which removes almost
# every first-touch page fault); then user-space page faults by faulting function (`perf record`).
#   noon8-probe.sh <base-commit> <head-commit> [cpu] > noon8-probe.txt
set -euo pipefail
base=$1 head=$2 cpu=${3:-40}
bin=/buildcache/cargo-target/zeebra-971/bin
scratch=${TMPDIR:-/buildcache/cargo-target/zeebra-971/tmp}
run() {
    GLIBC_TUNABLES=$1 taskset -c "$cpu" "$bin/sig_f4_study-sig-$2" --field wide64 --name noon-8 \
        --engine sigf4 --workers 1 --digest-only --wall-s 120
}
echo "# noon8-probe.sh $base $head cpu=$cpu $(date -u +%FT%TZ)"
echo "malloc commit rep elimination_ms symbolic_ms bookkeeping_ms element_hashing_ms"
for tunables in "" "glibc.malloc.hugetlb=1"; do
    for rep in 1 2 3 4 5; do
        for c in "$base" "$head"; do
            run "$tunables" "$c" | python3 -c "
import json, sys
s = json.load(sys.stdin)['statistics']
ms = lambda k: s.get(k + '_ns', 0) / 1e6
print('${tunables:-default}', '$c', $rep, *(f'{ms(k):.2f}' for k in ('elimination', 'symbolic', 'bookkeeping', 'element_hashing')))"
        done
    done
done
set +o pipefail  # `head` closes the report early
echo "# user-space page faults by faulting function, default malloc (top 6)"
for c in "$base" "$head"; do
    perf record -q -c 1 -e page-faults:u -o "$scratch/pf-$c.data" -- \
        taskset -c "$cpu" "$bin/sig_f4_study-sig-$c" --field wide64 --name noon-8 --engine sigf4 \
        --workers 1 --digest-only --wall-s 120 > /dev/null 2>&1
    echo "## $c total $(perf report -q -i "$scratch/pf-$c.data" --stdio -n --sort symbol 2>/dev/null \
        | awk '{n += $2} END {print n}')"
    perf report -q -i "$scratch/pf-$c.data" --stdio -n --sort symbol 2>/dev/null | head -6 \
        | awk '{printf "%s %s ", $1, $2; $1 = $2 = $3 = ""; print substr($0, 1, 90)}'
done
