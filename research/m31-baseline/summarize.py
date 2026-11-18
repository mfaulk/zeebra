#!/usr/bin/env python3
"""#901 tables from `campaign.py` records. Every attempt is counted; only complete ones are timed.

Ratios are **paired per repetition** (arm A's repetition r over arm B's repetition r, which the
rotation keeps adjacent in time): the median of those ratios, with a 95% percentile bootstrap over
repetitions. The §6.3 projection subtracts each stage's saving from design 1's own median process
wall and divides by the same binary's F4-16 median; it is an additive Amdahl estimate, not a result.

    python3 research/m31-baseline/summarize.py walls.jsonl.gz split.jsonl.gz > tables.md
"""
import gzip
import json
import random
import statistics
import sys
from collections import defaultdict

DRAWS = 20000
STAGES = ('elimination', 'interreduction', 'bookkeeping', 'symbolic')
# §6.3's scenarios: speed-up factor per stage (None = unchanged, inf = free).
INF = float('inf')
SCENARIOS = [
    ('Elimination free, rest unchanged', dict(elimination=INF)),
    ('Other stages free, elimination unchanged', dict(interreduction=INF, bookkeeping=INF, symbolic=INF)),
    ('Moderate', dict(elimination=3, interreduction=1.5, bookkeeping=1.25, symbolic=2)),
    ('Required shape (§6.3)', dict(elimination=3.5, interreduction=2, bookkeeping=1.5, symbolic=3)),
    ('Optimistic', dict(elimination=6, interreduction=3, bookkeeping=2, symbolic=3.9)),
]


def load(paths):
    records = []
    for path in paths:
        opener = gzip.open if path.endswith('.gz') else open
        with opener(path, 'rt') as handle:
            records.extend(json.loads(line) for line in handle if line.strip())
    return records


def complete(r):
    return r['returncode'] == 0 and (r.get('report') or {}).get('status') == 'complete'


def median_interval(values, seed=901):
    rng = random.Random(seed)
    meds = sorted(statistics.median(rng.choices(values, k=len(values))) for _ in range(DRAWS))
    return statistics.median(values), meds[int(0.025 * DRAWS)], meds[int(0.975 * DRAWS) - 1]


def paired(a, b):
    """Per-repetition ratios a[rep] / b[rep] over the repetitions both arms completed."""
    return [a[k] / b[k] for k in sorted(set(a) & set(b))]


def s(ns):
    return ns / 1e9


class Cohort:
    def __init__(self, records):
        self.wall = defaultdict(dict)       # (row, arm) -> rep -> process wall s
        self.rss = defaultdict(list)
        self.reports = defaultdict(dict)    # (row, arm) -> rep -> report
        self.attempts = defaultdict(int)
        self.failures = defaultdict(list)
        self.digests = defaultdict(set)
        self.rows = []
        for r in records:
            key = (r['row'], r['arm'])
            if r['row'] not in self.rows:
                self.rows.append(r['row'])
            self.attempts[key] += 1
            if not complete(r):
                rep = r.get('report') or {}
                self.failures[key].append(rep.get('status') or f"rc={r['returncode']}")
                continue
            self.wall[key][r['rep']] = s(r['process_wall_ns'])
            self.reports[key][r['rep']] = r['report']
            self.rss[key].append(r['report']['peak_rss_bytes'] / 2**20)
            self.digests[r['row']].add(r['report']['basis_sha256'])

    def arms(self, row):
        return [a for (r, a) in self.attempts if r == row]


def walls_table(c):
    out = ['| row | arm | attempts | complete | median wall s [95%] | median RSS MiB |',
           '|---|---|---:|---:|---:|---:|']
    for row in c.rows:
        for arm in c.arms(row):
            key = (row, arm)
            w = list(c.wall[key].values())
            cell = '—'
            if w:
                m, lo, hi = median_interval(w)
                cell = f'{m:.3f} [{lo:.3f}, {hi:.3f}]'
            rss = f'{statistics.median(c.rss[key]):.0f}' if c.rss[key] else '—'
            fail = f' ({"; ".join(sorted(set(c.failures[key])))[:80]})' if c.failures[key] else ''
            out.append(f'| {row} | {arm} | {c.attempts[key]} | {len(w)}{fail} | {cell} | {rss} |')
    return '\n'.join(out)


def ratio_cell(c, row, a, b):
    r = paired(c.wall[(row, a)], c.wall[(row, b)])
    if not r:
        return '—'
    m, lo, hi = median_interval(r)
    return f'{m:.3f} [{lo:.3f}, {hi:.3f}] (n={len(r)})'


def ratios_table(c):
    pairs = [('sigf4:1', 'f4:16'), ('sigf4:16', 'f4:16'), ('sigf4:16', 'sigf4:1'), ('sigf4:1', 'f4:1'),
             ('f4:1', 'f4:16'), ('f4:4', 'f4:16'), ('f4:8', 'f4:16')]
    out = ['| row | ' + ' | '.join(f'{a} ÷ {b}' for a, b in pairs) + ' | bases identical |',
           '|---|' + '---:|' * len(pairs) + '---|']
    for row in c.rows:
        cells = [ratio_cell(c, row, a, b) for a, b in pairs]
        n = len(c.digests[row])
        same = 'yes' if n == 1 else ('—' if n == 0 else f'NO ({n} digests)')
        out.append(f'| {row} | ' + ' | '.join(cells) + f' | {same} |')
    return '\n'.join(out)


def med(reports, f):
    return statistics.median(f(r) for r in reports)


def stage_table(c):
    """Stage clocks from the timed binary (they are always on in the signature engine), and the
    process-wall decomposition design 1's §4.3 item 4 asks for."""
    out = ['| row | arm | n | ' + ' | '.join(STAGES) + ' | Σ stages | total − Σ | call − total | '
           'setup (main − call − render) | render | exec + exit (process − main) | process wall | '
           'Σ named ÷ process |',
           '|---|---|---:|' + '---:|' * (len(STAGES) + 9)]
    for row in c.rows:
        for arm in ('sigf4:1', 'sigf4:16'):
            reps = list(c.reports[(row, arm)].items())
            if not reps:
                continue
            reports = [r for _, r in reps]
            st = {k: med(reports, lambda r, k=k: s(r['statistics'][f'{k}_ns'])) for k in STAGES}
            total_minus = med(reports, lambda r: s(r['statistics']['total_ns'] - sum(
                r['statistics'][f'{k}_ns'] for k in STAGES)))
            call_minus = med(reports, lambda r: s(r['call_ns'] - r['statistics']['total_ns']))
            setup = med(reports, lambda r: s(r['main_ns'] - r['call_ns'] - r['render_ns']))
            render = med(reports, lambda r: s(r['render_ns']))
            proc = {rep: c.wall[(row, arm)][rep] for rep, _ in reps}
            exec_exit = statistics.median(proc[rep] - s(r['main_ns']) for rep, r in reps)
            wall = statistics.median(proc.values())
            # Every named piece sums to process wall by construction; the check is that the
            # per-component medians do too.
            named = sum(st.values()) + total_minus + call_minus + setup + render + exec_exit
            out.append(f'| {row} | {arm} | {len(reports)} | ' + ' | '.join(f'{st[k]:.3f}' for k in STAGES)
                       + f' | {sum(st.values()):.3f} | {total_minus:.3f} | {call_minus:.4f} | {setup:.3f} | '
                       f'{render:.3f} | {exec_exit:.3f} | {wall:.3f} | {named / wall:.3f} |')
    return '\n'.join(out)


def amdahl(c, row='wide64/eco-12', target=0.75, gate=0.70):
    d1 = list(c.wall[(row, 'sigf4:1')].values())
    f4 = list(c.wall[(row, 'f4:16')].values())
    reports = list(c.reports[(row, 'sigf4:1')].values())
    if not (d1 and f4 and reports):
        return f'(no complete design-1 and F4-16 arms for {row})'
    w, b = statistics.median(d1), statistics.median(f4)
    st = {k: med(reports, lambda r, k=k: s(r['statistics'][f'{k}_ns'])) for k in STAGES}
    out = [f'{row}: design 1 median {w:.3f} s, F4-16 median {b:.3f} s (same binary, same session); '
           f'target {target} × F4-16 = {target * b:.3f} s, so the required cut is {w - target * b:.3f} s.',
           '', '| scenario | ' + ' | '.join(f'{k} ({st[k]:.3f} s)' for k in STAGES)
           + ' | projected wall s | ÷ F4-16 |', '|---|' + '---|' * len(STAGES) + '---:|---:|']
    for name, factors in SCENARIOS:
        saved, cells = 0.0, []
        for k in STAGES:
            f = factors.get(k)
            if f is None:
                cells.append('—')
                continue
            cut = st[k] * (1 - 1 / f)
            saved += cut
            cells.append(f'{"free" if f == INF else f"{f}×"} (−{cut:.3f})')
        proj = w - saved
        out.append(f'| {name} | ' + ' | '.join(cells) + f' | {proj:.3f} | {proj / b:.3f} |')
    if gate is None:
        return '\n'.join(out)
    # The elimination factor that alone, or with the others at the required shape, reaches Gate A.
    others = sum(st[k] * (1 - 1 / f) for k, f in SCENARIOS[3][1].items() if k != 'elimination')
    for label, rest in (('alone', 0.0), ('with the other stages at the required shape', others)):
        need = w - gate * b - rest
        e = st['elimination']
        factor = '∞ (unreachable)' if need >= e else f'{e / (e - need):.2f}×'
        out.append(f'\nElimination speed-up for {gate} × F4-16 {label}: {factor}.')
    return '\n'.join(out)


class Split:
    """The `split` suite: per-batch reducer-block / cascade work from the instrument binary."""

    def __init__(self, records):
        self.runs = defaultdict(list)
        self.walls = defaultdict(list)
        for r in records:
            if complete(r):
                self.runs[(r['row'], r['arm'])].append(r['report'])
                self.walls[(r['row'], r['arm'])].append(s(r['process_wall_ns']))

    def table(self):
        out = ['| row | arm | n | wall s | elimination s | setup s | parallel pass s | serial pass s | '
               'products G: parallel / serial-reducer / cascade | cascade share of products | '
               'cascading targets / targets | inputs s | materialize s | drop s |',
               '|---|---|---:|' + '---:|' * 11]
        for (row, arm), reports in sorted(self.runs.items()):
            def tot(field, r):
                return sum(b[field] for b in r['statistics']['split']['batches'])
            sp = lambda k: med(reports, lambda r: s(tot(k, r)))  # noqa: E731
            r0 = reports[0]
            prods = [tot(k, r0) for k in ('parallel_products', 'serial_reducer_products', 'cascade_products')]
            casc_t = tot('cascading_targets', r0)
            targets = tot('targets', r0)
            g = med(reports, lambda r: s(r['statistics']['split']['materialize_ns']))
            out.append(
                f'| {row} | {arm} | {len(reports)} | {statistics.median(self.walls[(row, arm)]):.3f} | '
                f'{med(reports, lambda r: s(r["statistics"]["elimination_ns"])):.3f} | {sp("setup_ns"):.3f} | '
                f'{sp("parallel_pass_ns"):.3f} | {sp("serial_pass_ns"):.3f} | '
                f'{" / ".join(f"{p / 1e9:.3f}" for p in prods)} | {prods[2] / sum(prods):.3f} | '
                f'{casc_t} / {targets} | '
                f'{med(reports, lambda r: s(r["statistics"]["split"]["inputs_ns"])):.4f} | {g:.3f} | '
                f'{med(reports, lambda r: s(r["statistics"]["split"]["drop_ns"])):.3f} |')
        return '\n'.join(out)

    def batches(self, row, top=12):
        """Per batch, design 1's serial products split and design 2's measured pass times."""
        d1, d2 = self.runs.get((row, 'sigf4:1')), self.runs.get((row, 'sigf4:16'))
        if not (d1 and d2):
            return f'(need both designs for {row})'
        b1 = [r['statistics']['split']['batches'] for r in d1]
        b2 = [r['statistics']['split']['batches'] for r in d2]
        n = len(b1[0])
        assert all(len(b) == n for b in b1 + b2), 'batch sequences differ between runs'

        def mb(runs, i, k):
            return statistics.median(run[i][k] for run in runs)
        rows = []
        for i in range(n):
            x = b1[0][i]
            rows.append(dict(
                i=i, targets=x['targets'], reducers=x['reducers'], columns=x['columns'],
                d1_elim=s(mb(b1, i, 'setup_ns') + mb(b1, i, 'serial_pass_ns')),
                d1_red=x['serial_reducer_products'], d1_casc=x['cascade_products'],
                d2_par=s(mb(b2, i, 'parallel_pass_ns')), d2_ser=s(mb(b2, i, 'serial_pass_ns')),
                d2_setup=s(mb(b2, i, 'setup_ns')),
                d2_prod=b2[0][i]['parallel_products'] + b2[0][i]['serial_reducer_products']
                + b2[0][i]['cascade_products'], d2_casc=b2[0][i]['cascade_products']))
        total = sum(r['d1_elim'] for r in rows)
        rows.sort(key=lambda r: -r['d1_elim'])
        out = [f'{row}: {n} batches; the {top} with the most design-1 elimination time '
               f'({sum(r["d1_elim"] for r in rows[:top]) / total:.1%} of it).', '',
               '| batch | targets | reducers | columns | d1 elim s | d1 products M: reducer / cascade | '
               'd2 setup / parallel / serial s | d2 products M (cascade) |',
               '|---:|---:|---:|---:|---:|---:|---:|---:|']
        for r in rows[:top]:
            out.append(f'| {r["i"]} | {r["targets"]} | {r["reducers"]} | {r["columns"]} | {r["d1_elim"]:.3f} | '
                       f'{r["d1_red"] / 1e6:.1f} / {r["d1_casc"] / 1e6:.1f} | '
                       f'{r["d2_setup"]:.3f} / {r["d2_par"]:.3f} / {r["d2_ser"]:.3f} | '
                       f'{r["d2_prod"] / 1e6:.1f} ({r["d2_casc"] / 1e6:.1f}) |')
        return '\n'.join(out)


def main(paths):
    records = load(paths)
    walls = [r for r in records if r['suite'] == 'walls']
    split = [r for r in records if r['suite'] == 'split']
    print('# #901 tables (generated by summarize.py; do not edit)\n')
    if walls:
        c = Cohort(walls)
        print('## Wall cohort\n\n' + walls_table(c) + '\n\n## Paired ratios (median of per-repetition '
              'ratios [95% bootstrap])\n\n' + ratios_table(c) + '\n\n## Signature-engine stages and '
              'process decomposition (timed binary, medians)\n\n' + stage_table(c)
              + '\n\n## §6.3 re-derived\n\n' + amdahl(c) + '\n\n' + amdahl(c, 'goldilocks/katsura-11', 0.90, None))
    if split:
        sp = Split(split)
        print('\n## Elimination split (instrument binary)\n\n' + sp.table())
        for row in SPLIT_BATCH_ROWS:
            print('\n### Per batch: ' + row + '\n\n' + sp.batches(row))


SPLIT_BATCH_ROWS = ('wide64/eco-12', 'goldilocks/katsura-11')

if __name__ == '__main__':
    main(sys.argv[1:])
