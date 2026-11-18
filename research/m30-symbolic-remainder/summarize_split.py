import gzip, json, sys, statistics as st
from collections import defaultdict
rows = defaultdict(list)
for l in (gzip.open if sys.argv[1].endswith(".gz") else open)(sys.argv[1], "rt"):
    r = json.loads(l)
    if r['rc'] == 0:
        rows[(r['target'], r['workers'])].append(r['report'])
keys = ['symbolic_ns', 'seed_ns', 'seed_step_ns', 'spawn_ns', 'scan_ns', 'solo_ns', 'merge_ns', 'emit_ns', 'stitch_ns']
print('target w n f4ms ' + ' '.join(k[:-3] for k in keys) + ' other steps disp basis')
for (t, w), rs in sorted(rows.items()):
    med = {k: st.median(r[k] for r in rs) / 1e6 for k in keys + ['f4_call_ns']}
    parts = sum(med[k] for k in ['seed', 'spawn', 'scan', 'merge', 'emit', 'stitch'] for k in [k + '_ns'])
    other = med['symbolic_ns'] - parts
    print(t, w, len(rs), f"{med['f4_call_ns']:.1f}", ' '.join(f"{med[k]:.2f}" for k in keys), f"{other:.2f}",
          rs[0]['served_steps'], rs[0]['dispatched_steps'], len({r['basis_sha256'] for r in rs}), rs[0]['fallback'])
