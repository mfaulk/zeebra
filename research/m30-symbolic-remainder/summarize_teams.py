import gzip, json, sys, statistics as st
from collections import defaultdict
rows = defaultdict(lambda: defaultdict(dict))
for l in (gzip.open if sys.argv[1].endswith(".gz") else open)(sys.argv[1], "rt"):
    r = json.loads(l)
    if r['rc'] == 0:
        rows[r['target']][r['team']][r['rep']] = r['report']
print('target team n symbolic_med f4_med  sym_ratio_vs16[min,max] f4_ratio_vs16[min,max] stitch merge seed_step solo basis_ids')
for t, by in rows.items():
    base = by[16]
    for team, reps in sorted(by.items(), reverse=True):
        common = sorted(set(reps) & set(base))
        sr = [reps[k]['symbolic_ns'] / base[k]['symbolic_ns'] for k in common]
        fr = [reps[k]['f4_call_ns'] / base[k]['f4_call_ns'] for k in common]
        m = lambda key: st.median(r[key] for r in reps.values()) / 1e6
        print(t, team, len(reps), f"{m('symbolic_ns'):.1f}", f"{m('f4_call_ns'):.1f}",
              f"{st.median(sr):.3f}[{min(sr):.3f},{max(sr):.3f}]", f"{st.median(fr):.3f}[{min(fr):.3f},{max(fr):.3f}]",
              f"{m('stitch_ns'):.1f}", f"{m('merge_ns'):.1f}", f"{m('seed_step_ns'):.1f}", f"{m('solo_ns'):.1f}",
              len({r['basis_sha256'] for r in reps.values()} | {r['basis_sha256'] for r in base.values()}))
