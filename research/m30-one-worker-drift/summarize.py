"""#890: per-commit ratios, paired per repetition, against the freeze and against the previous commit."""
import gzip, json, random, statistics as st, sys
from collections import defaultdict

ORDER = '4f5784c5,f4d4ae8e,53af1dde,833bb6bb,a3524d66,a5089c5c,5452ae13,28e4e063,d6aa0526,d6aa0526-inline,e4826153'.split(',')
METRICS = (('symbolic', lambda r: r['stats']['symbolic_ns']), ('total', lambda r: r['stats']['total_ns']),
           ('process', lambda r: r['process_wall_ns']))


def ci(xs, n=4000, rng=random.Random(890)):
    meds = sorted(st.median(rng.choices(xs, k=len(xs))) for _ in range(n))
    return meds[int(0.025 * n)], meds[int(0.975 * n)]


for path in sys.argv[1:]:
    runs = defaultdict(dict)
    digests = set()
    for l in (gzip.open if path.endswith('.gz') else open)(path, 'rt'):
        r = json.loads(l)
        if r['rc'] == 0:
            runs[r['build']][r['rep']] = r
            digests.add(r['basis_sha256'])
    target = next(iter(next(iter(runs.values())).values()))['target']
    print(f'## {target}  digests={len(digests)}  reps={min(len(v) for v in runs.values())}')
    print('build  symbolic_ms  symbolic/first  symbolic/prev  total/first  process/first  process/prev')
    present = [b for b in ORDER if b in runs]
    for i, b in enumerate(present):
        out = [b, f"{st.median(METRICS[0][1](r) for r in runs[b].values()) / 1e6:.1f}"]
        for name, f in METRICS:
            for ref in ([present[0], present[max(i - 1, 0)]] if name != 'total' else [present[0]]):
                reps = sorted(set(runs[b]) & set(runs[ref]))
                xs = [f(runs[b][k]) / f(runs[ref][k]) for k in reps]
                lo, hi = ci(xs)
                out.append(f'{st.median(xs):.3f} [{lo:.3f},{hi:.3f}]')
        print('  '.join(out))
