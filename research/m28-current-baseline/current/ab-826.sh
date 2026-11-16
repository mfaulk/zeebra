#!/usr/bin/env bash
# Interleaved whole-route A/B on MQ10: main against #826, both moduli, 5 reps, order alternating.
set -euo pipefail
T=/buildcache/cargo-target/zeebra-826
out=$T/ab
mkdir -p "$out"
for rep in 0 1 2 3 4; do
  if (( rep % 2 )); then arms="826 main"; else arms="main 826"; fi
  for m in 32003 2147483647; do
    for arm in $arms; do
      taskset -c 2-17 "$T/bin/mq10-$arm" "$m" --problem=mq-random-10 --whole-route=fglm --stages \
        > "$out/$arm-$m-$rep.ndjson"
    done
  done
done
python3 - "$out" <<'EOF'
import json, sys, glob, statistics, hashlib
out = sys.argv[1]
rows = {}
lex = {}
for path in sorted(glob.glob(out + '/*.ndjson')):
    arm, m, rep = path.rsplit('/', 1)[1][:-7].split('-')
    recs = [json.loads(l) for l in open(path)]
    final = recs[-1]
    lx = next(r for r in recs if r.get('checkpoint') == 'lex-basis')
    lex.setdefault(m, set()).add(hashlib.sha256(json.dumps(lx['lex_basis']).encode()).hexdigest())
    c = final['conversion']
    rows.setdefault((m, arm), []).append((final['whole_route_ns'] / 1e6, c['operator_ns'] / 1e6, final['outcome']))
for (m, arm), v in sorted(rows.items()):
    w = [x[0] for x in v]; o = [x[1] for x in v]
    print(f"{m:>10} {arm:>4}: whole median {statistics.median(w):6.1f} [{min(w):6.1f},{max(w):6.1f}]  operator median {statistics.median(o):6.1f} [{min(o):6.1f},{max(o):6.1f}] outcomes {set(x[2] for x in v)}")
for m, s in lex.items():
    print(m, 'lex bases identical across arms and reps' if len(s) == 1 else f'LEX DIFFERS: {len(s)}')
EOF
