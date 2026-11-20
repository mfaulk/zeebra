#!/usr/bin/env python3
"""#941 Gate Q tables from `campaign.py` records (plan §6.2 T3–T9, §8.2, §9).

Timing: the adaptive option (`ad`) against its reference, conventional F4 (`f4`) or the M31
reference entry point (`m31`), paired per repetition; median with a 95% bootstrap interval of the
median (20,000 draws); plan §10.3's precision rule (half-width ≤ half the distance from the bound
to 1.0). The `small` suite uses each process's median warm call (#934). Memory: peak RSS (VmHWM)
medians per arm. Correctness, from the `check` suite and every timed child: one basis digest per
row and order across arms, workers and repetitions; equality with each independent reference;
certification; thread high-water against the worker cap; the 1 s wall budget.

    python3 research/m32-qualification/summarize.py dev.jsonl[.gz] small... held... check...
"""
import gzip
import json
import random
import statistics
import sys
from collections import defaultdict

DRAWS = 20000
T9_NS = 50_000
FAVOURABLE = ['wide64/eco-12', 'goldilocks/katsura-11', 'wide64/katsura-11', 'goldilocks/mq-random-11',
              'goldilocks/noon-7', 'wide64/noon-8', 'wide64/katsura-9']
CONTROLS = ['goldilocks/cyclic-7', 'wide64/cyclic-7', 'goldilocks/katsura-4', 'wide64/katsura-4',
            'goldilocks/noon-7']
MQ10 = ['gf32003/mq-random-10', 'm31/mq-random-10']
HELD_OUT = ['goldilocks/mq-random-10', 'm31/katsura-10', 'm31/eco-11']
# T4's absolute bounds on adaptive ÷ conventional at 16 workers (medians).
T4_ABSOLUTE = {'goldilocks/katsura-11': 0.50, 'wide64/katsura-11': 0.50, 'goldilocks/mq-random-11': 0.50,
               'wide64/eco-12': 0.70}
# M31's grobx certified answers on the same pinned inputs (research/m31-final/certified.jsonl.gz),
# in sig_f4_study's digest encoding: an independent grevlex reference for these rows.
GROBX_CERTIFIED = {
    'wide64/eco-12': '3bf17412e9d0902cc1b67511e11207c8219ff756ed9a72fd7369300c2fbbb984',
    'goldilocks/mq-random-11': 'ddef89cb69323c4ee9fb3d706dac4bcb50b1888130b309b6ef675461be072d41',
    'wide64/katsura-11': 'c673510949d6676c48a9284bbf4290045786939f51118845417ae2fde3b8a637',
    'wide64/cyclic-7': '31c838c1df12307110124e249e6a632bcb6a99faa39c58ec33bbd191055e6bff',
}
REFERENCES = {'rs': 'groebner-rs', 'sg': 'Singular', 'bb': 'buchberger_reference'}
LOAD_FLAG = 4.0


def interval(values, seed=941):
    rng = random.Random(seed)
    medians = sorted(statistics.median(rng.choices(values, k=len(values))) for _ in range(DRAWS))
    return medians[int(0.025 * DRAWS)], medians[int(0.975 * DRAWS) - 1]


def load(paths):
    records = []
    for path in paths:
        opener = gzip.open if path.endswith('.gz') else open
        with opener(path, 'rt') as handle:
            records.extend(json.loads(line) for line in handle if line.strip())
    return records


def complete(r):
    return r['returncode'] == 0 and (r.get('report') or {}).get('status') == 'complete'


def split(arm):
    label, workers = arm.split(':')
    label, _, order = label.partition('.')
    return label, order or 'grevlex', int(workers)


def metric(r):
    """Milliseconds: process wall, or the median warm in-process call for the small suite."""
    if r['suite'] != 'small':
        return r['process_wall_ns'] / 1e6
    report = r['report']
    warm = report.get('warm_ns') or report['calls_ns'][1:]
    return statistics.median(warm) / 1e6


def ratio_cell(reps, label, ref):
    pairs = [(reps[k][label], reps[k][ref]) for k in sorted(reps) if label in reps[k] and ref in reps[k]]
    if not pairs:
        return None
    ratios = [metric(a) / metric(b) for a, b in pairs]
    lo, hi = interval(ratios)
    med = statistics.median(ratios)
    return dict(n=len(ratios), med=med, lo=lo, hi=hi, half=(hi - lo) / 2 / med,
                a=statistics.median(metric(a) for a, _ in pairs),
                b=statistics.median(metric(b) for _, b in pairs), sample=pairs[0][0])


def main(paths):
    records = load(paths)
    cells = defaultdict(lambda: defaultdict(dict))  # (suite, row, workers) -> rep -> label -> record
    digests = defaultdict(lambda: defaultdict(set))  # (row, order) -> label -> digests
    rss = defaultdict(list)  # (row, label, workers) -> peak RSS bytes, timed suites
    failures, dispatch, threads, walls, certs, loaded = [], [], [], [], [], []
    for r in records:
        label, order, workers = split(r['arm'])
        if r['load_start'] > LOAD_FLAG:
            loaded.append((r['suite'], r['rep'], r['row'], r['arm'], round(r['load_start'], 1)))
        report = r.get('report') or {}
        if label == 'adw':
            walls.append((r['row'], workers, report.get('status', f"rc={r['returncode']}"),
                          r['process_wall_ns'] / 1e6))
            continue
        if not complete(r):
            failures.append((r['suite'], r['row'], r['arm'], r['rep'], r['returncode'], report.get('status')))
            continue
        digests[(r['row'], order)][label].add(report['basis_sha256'])
        if r['suite'] != 'check':
            cells[(r['suite'], r['row'], workers)][r['rep']][label] = r
            if report.get('peak_rss_bytes'):
                rss[(r['row'], label, workers)].append(report['peak_rss_bytes'])
        if label in ('ad', 'adc'):
            stats = report['statistics']
            if stats.get('dispatch_ns') is not None:
                dispatch.append((r['row'], workers, stats['dispatch_ns'], metric(r)))
            if report.get('threads_peak') is not None:
                threads.append((r['row'], order, workers, report['threads_peak']))
        if label == 'adc':
            certs.append((r['row'], order, report.get('certification')))

    verdicts = {}

    def gate(name, ok):
        verdicts[name] = verdicts.get(name, True) and ok

    print('## Timing (adaptive option ÷ reference, paired; median [95%])\n')
    print('| criterion | row | w | n | ref | ref ms | ad ms | ad ÷ ref [95%] | half-width | bound | read | route | team |')
    print('|---|---|---:|---:|---|---:|---:|---:|---:|---:|---|---|---:|')
    imprecise = []
    for (suite, row, workers) in sorted(cells):
        reps = cells[(suite, row, workers)]
        rows = []
        if suite == 'held':
            rows.append(('held-out' if workers in (1, 16) else 'held-out (info)', 'f4', 1.05))
        elif row in MQ10:
            rows.append(('T3', 'f4', 1.05))
        if row in CONTROLS and workers in (1, 16):
            rows.append(('T5', 'f4', 1.05))
        if row in FAVOURABLE:
            rows.append(('T4' if workers == 16 else 'T4 (info)', 'm31', 1.03))
            if workers == 16 and row in T4_ABSOLUTE:
                rows.append(('T4 abs', 'f4', T4_ABSOLUTE[row]))
        for criterion, ref, bound in rows:
            c = ratio_cell(reps, 'ad', ref)
            if c is None:
                continue
            stats = c['sample']['report']['statistics']
            info = '(info)' in criterion
            if criterion == 'T4 abs':
                ok, read = c['med'] <= bound, 'pass' if c['med'] <= bound else 'FAIL'
            else:
                ok = c['hi'] <= bound
                readable = c['half'] <= (bound - 1.0) / 2
                read = ('pass' if ok else 'FAIL') + ('' if readable else ' (imprecise)')
                if not readable and not info:
                    imprecise.append((suite, row, workers, criterion))
            if not info:
                gate(criterion.split()[0], ok)
            print(f"| {criterion} | {row} | {workers} | {c['n']} | {ref} | {c['b']:.2f} | {c['a']:.2f} | "
                  f"{c['med']:.3f} [{c['lo']:.3f}, {c['hi']:.3f}] | {100 * c['half']:.1f}% | {bound} | {read} | "
                  f"{stats.get('route')} | {stats.get('team', '—')} |")

    print('\n## T6 memory (median peak RSS, MiB)\n')
    print('| row | w | ad | f4 | ad ÷ f4 (≤ 1.25) | m31 | ad ÷ m31 (≤ 1.10) |')
    print('|---|---:|---:|---:|---:|---:|---:|')
    for (row, label, workers) in sorted(k for k in rss if k[1] == 'ad'):
        ad = statistics.median(rss[(row, 'ad', workers)])
        f4 = rss.get((row, 'f4', workers))
        m31 = rss.get((row, 'm31', workers))
        r_f4 = ad / statistics.median(f4) if f4 else None
        r_m31 = ad / statistics.median(m31) if m31 else None
        if r_f4 is not None:
            gate('T6', r_f4 <= 1.25)
        if r_m31 is not None:
            gate('T6', r_m31 <= 1.10)
        fmt = lambda v: '—' if v is None else f'{v:.3f}'
        mib = lambda v: '—' if not v else f'{statistics.median(v) / 2**20:.0f}'
        print(f"| {row} | {workers} | {ad / 2**20:.0f} | {mib(f4)} | {fmt(r_f4)} | {mib(m31)} | {fmt(r_m31)} |")

    print('\n## T7 / §9.1 correctness\n')
    print('| row | order | digests (all arms) | ad = f4 | references agreeing | certified |')
    print('|---|---|---:|---|---|---|')
    cert_by = defaultdict(list)
    for row, order, c in certs:
        cert_by[(row, order)].append(c)
    for (row, order) in sorted(digests):
        by = digests[(row, order)]
        every = set().union(*by.values())
        same = by.get('ad') == by.get('f4') and len(by.get('ad', ())) == 1
        refs = [f"{REFERENCES[k]} {'=' if by[k] == by.get('ad') else '≠'}" for k in REFERENCES if k in by]
        if order == 'grevlex' and row in GROBX_CERTIFIED:
            refs.append(f"grobx certified (M31) {'=' if by.get('ad') == {GROBX_CERTIFIED[row]} else '≠'}")
        cs = cert_by.get((row, order), [])
        certified = bool(cs) and all(c and c['checks_passed'] and c['complete'] for c in cs)
        gate('T7', len(every) == 1 and same and certified and all('≠' not in x for x in refs) and bool(refs))
        print(f"| {row} | {order} | {len(every)} | {'yes' if same else 'NO'} | {', '.join(refs) or 'none'} | "
              f"{'yes' if certified else 'NO'} |")

    print('\n## T8 behaviour\n')
    over = [t for t in threads if t[3] > t[2]]
    gate('T8', not over and bool(threads))
    print(f"Thread high-water: {len(threads)} adaptive children; worst peak minus cap "
          f"{max((t[3] - t[2] for t in threads), default=0)}; over the cap: {over or 'none'}")
    for row, workers, status, wall in walls:
        ok = status.startswith('stopped') and 'time' in status.lower()
        gate('T8', ok)
        print(f"1 s wall budget, {row}, {workers} w: {status!r}, process wall {wall:.0f} ms")

    print('\n## T9 dispatch cost\n')
    worst = max(dispatch, key=lambda d: d[2]) if dispatch else None
    share = max((d[2] / 1e6 / d[3] for d in dispatch if d[3] >= 50), default=0.0)
    if worst:
        gate('T9', worst[2] <= T9_NS and share <= 0.001)
        print(f"n = {len(dispatch)}: max {worst[2] / 1e3:.1f} µs ({worst[0]}, {worst[1]} w); median "
              f"{statistics.median(d[2] for d in dispatch) / 1e3:.1f} µs; worst share of wall on rows "
              f"≥ 50 ms {100 * share:.4f}%")

    print('\n## Children\n')
    gate('complete', not failures)
    print(f"Incomplete children: {len(failures)} {failures[:10]}")
    print(f"Children started at load > {LOAD_FLAG}: {len(loaded)} {loaded[:10]}")
    print(f"Imprecise gated cells (extension candidates): {imprecise}")
    print('\n## Verdicts\n')
    for name, ok in sorted(verdicts.items()):
        print(f"- {name}: {'pass' if ok else 'FAIL'}")


if __name__ == '__main__':
    main(sys.argv[1:])
