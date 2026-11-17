#!/usr/bin/env bash
# A/B for #845: base (origin/main) vs new, both default forward order, plus base FL reference.
# Usage: ab845.sh <out.jsonl> <reps> <workers> [--stages]
set -u
out=$1 reps=$2 workers=$3 extra=${4:-}
B=/buildcache/cargo-target/zeebra-845/base/release/examples/m29_cost_model
N=/buildcache/cargo-target/zeebra-845/new/release/examples/m29_cost_model
CPUS=${CPUS:-8-23}
cd /buildcache/cargo-target/zeebra-845/base-src || exit 2   # data paths resolve relative to the repo
arms=(base new basefl)
for t in mq10-32003 mq10-m31 eco12-wide64 mq11-goldilocks; do
  for ((r = 0; r < reps; r++)); do
    for ((k = 0; k < 3; k++)); do
      arm=${arms[$(((k + r) % 3))]}
      case $arm in
        base) bin=$B; flags=() ;;
        new) bin=$N; flags=() ;;
        basefl) bin=$B; flags=(--batch-order fl) ;;
      esac
      load=$(cut -d' ' -f1 /proc/loadavg)
      s=$(date +%s%N)
      json=$(/usr/bin/time -f '%M' -o /buildcache/cargo-target/zeebra-845/tmp/rss taskset -c "$CPUS" \
        "$bin" --target "$t" --workers "$workers" $extra "${flags[@]}" 2>/dev/null | tail -1)
      e=$(date +%s%N)
      rss=$(cat /buildcache/cargo-target/zeebra-845/tmp/rss)
      printf '{"target":"%s","arm":"%s","rep":%d,"workers":%s,"wall_ms":%.1f,"rss_kb":%s,"load":%s,"run":%s}\n' \
        "$t" "$arm" "$r" "$workers" "$(echo "($e-$s)/1000000" | bc -l)" "$rss" "$load" "${json:-null}" >>"$out"
    done
  done
done
