"""Summarize the #1106 pilot: §7.2's n, §4.3's held-out small pair, §4.2's m5 tuning. Exploratory.

Usage: python3 -I summarize.py <repo> <workdir> <pilot-out>   (writes <pilot-out>/summary.md)"""
import importlib.util, json, math, sys
from pathlib import Path

REPO, W, OUT = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
spec = importlib.util.spec_from_file_location('bench_stats', REPO / 'tools/bench_stats.py')
bs = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bs)
res = json.loads((OUT / 'results.json').read_text())
jobs = res['jobs']


def walls(job):
    out = {}
    for line in (W / 'jobs' / job / 'journal' / 'journal.jsonl').open():
        r = json.loads(line)
        md = r.get('metadata') or {}
        if r.get('kind') == 'exit' and md.get('exit') == 0:
            c = r['cell']
            out.setdefault((c['instance'], c['workers'], c['arm']), {})[c['rep']] = md['wall_seconds']
    return out


def ci(num, den, seed):
    return bs.paired_ratio(bs.paired_ratios(num, den), seed=seed)


lines = [f"# #1106 pilot summary (exploratory; decides nothing)\n\nC = `{res['C']}`. Reservation: {res['reservation']}.\n",
         '## Binaries\n', '| binary | SHA-256 |', '|---|---|']
lines += [f'| `{k}` | `{v}` |' for k, v in res['binaries'].items()]

# §7.2: calibration A/A half-widths at n0 = 9, W0 and W4-32.
CAL = [('S1', 'wide64/eco-12', 1, 'a2', 'a', 'C-E1'), ('S1', 'gf32003/mq-random-10', 1, 'a2', 'a', 'C-M1'),
       ('S16', 'gf32003/mq-random-10', 16, 'a2', 'a', 'C-M16'), ('P', 'mq10-32003', 16, 'distinct2', 'distinct', 'C-P16')]
lines += ['\n## A/A on the calibration cohort (§7.2)\n',
          '| cell | load | n | median a | A/A median [95% CI] | half-width |', '|---|---|---:|---:|---|---:|']
n_cells = {}
for step, inst, w, x, y, cell in CAL:
    hs = []
    for load in ('W0', 'W4'):
        v = walls(jobs[f'{step}-{load}'])
        c = ci(v[(inst, w, x)], v[(inst, w, y)], f'1106-pilot-{cell}-{load}')
        h = max(c.hi - c.median, c.median - c.lo)
        hs.append(h)
        a = sorted(v[(inst, w, y)].values())
        lines.append(f'| {cell} | {load} | {c.n} | {a[len(a) // 2]:.4f} | {c.median:.4f} [{c.lo:.4f}, {c.hi:.4f}] | {h:.4f} |')
    n_cells[cell] = min(30, max(15, math.ceil(9 * (max(hs) / 0.010) ** 2)))
n = max(n_cells.values())
lines += ['', 'n per cell, `min(30, max(15, ceil(9 (h / 0.010)^2)))` with h the larger half-width: '
          + ', '.join(f'{k} {v}' for k, v in n_cells.items()) + f'. **n = {n}**' + (' (the cap of 30 binds)' if n == 30 else '') + '.']

# §4.3: held-out small pair, idle only, first candidate in order with median distinct/every in
# [0.95, 0.98] and CI below 1.0. C-P16's idle effect is reported beside them.
v = walls(jobs['P-W0'])
lines += ['\n## Real small pair (§4.3), W0 only\n', '| target | median every s | distinct/every [95% CI] | qualifies |',
          '|---|---:|---|---|']
chosen = None
for t in ('mq10-32003', 'cyclic7-wide64', 'katsura11-wide64', 'katsura11-m31'):
    c = ci(v[(t, 16, 'distinct')], v[(t, 16, 'every')], f'1106-pilot-q-{t}')
    ok = 0.95 <= c.median <= 0.98 and c.hi < 1.0
    e = sorted(v[(t, 16, 'every')].values())
    note = 'calibration (C-P16)' if t == 'mq10-32003' else ('yes' if ok else 'no')
    if t != 'mq10-32003' and ok and chosen is None:
        chosen = t
    lines.append(f'| {t} | {e[len(e) // 2]:.4f} | {c.median:.4f} [{c.lo:.4f}, {c.hi:.4f}] | {note} |')
lines.append(f'\nH-S16 = **{chosen}**.' if chosen else '\n**No candidate qualified**: H3 falls back to `m5`/`s5` (§4.3).')

lines += ['\n## m5 tuning (§4.2)\n', '| cell | threads | MiB | t_A s | t_0 s | t_1 s | passes | validation 1 | validation 2 | status |',
          '|---|---:|---:|---:|---:|---:|---:|---|---|---|']
for k, t in res['m5'].items():
    st = 'accepted' if t.get('accepted') else 'untuned' if t.get('untuned') else '?'
    lines.append(f"| {k} | {t['threads']} | {t['mib']} | {t['t_A']:.4f} | {t['t_0']:.4f} | {t['t_1']:.4f} | {t['passes']} | "
                 f"{t.get('validation1', float('nan')):.4f} | {t.get('validation2', float('nan')):.4f} | {st} |")
(OUT / 'summary.md').write_text('\n'.join(lines) + '\n')
print('\n'.join(lines))
