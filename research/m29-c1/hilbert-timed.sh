#!/usr/bin/env bash
# MQ10 Hilbert-limited batch selection vs off, one binary, interleaved, rotated. Usage: hb835.sh out reps workers
set -u
out=$1 reps=$2 workers=$3
B=/buildcache/cargo-target/zeebra-835/release/examples/m29_cost_model
modes=(off limited+100 limited+400)
for t in mq10-32003 mq10-m31; do
  for ((r = 0; r < reps; r++)); do
    for ((k = 0; k < 3; k++)); do
      m=${modes[$(((k + r) % 3))]}
      s=$(date +%s%N)
      json=$(taskset -c 8-23 "$B" --target "$t" --workers "$workers" --hilbert "$m" 2>/dev/null | tail -1)
      e=$(date +%s%N)
      python3 -I -c "
import json,sys
r=json.loads(sys.argv[1]); s=r['statistics']
print(json.dumps(dict(target='$t',mode='$m',workers=$workers,wall_ms=($e-$s)/1e6,f4_ms=r['f4_call_ns']/1e6,sha=r['basis_sha256'],batches=s['batches'],row_operations=s['row_operations'],load=open('/proc/loadavg').read().split()[0])))" "$json" >>"$out"
    done
  done
done
