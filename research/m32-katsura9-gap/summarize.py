#!/usr/bin/env python3
"""#958 and #964 tables from the committed records.

    python3 research/m32-katsura9-gap/summarize.py research/m32-katsura9-gap > research/m32-katsura9-gap/tables.md

`gap`: each process's metric is the median of its warm calls (`warm_ns` under `--calls`,
`calls_ns[1:]` under `--repeat`, as Gate Q's `summarize.py` reads them); ratios are paired by
repetition, median with a 95% percentile bootstrap (20,000 draws, seed 958). `ab`: #939's own table
code (`research/m32-baseline/summarize.py` `ab`) on the original records and on this session's.
"""
import gzip
import importlib.util
import json
import random
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
DRAWS = 20000
WORKERS = (1, 16)
LABELS = ['m31', 'base', 'rev1', 'f2', 'f2rep', 'f2own', 'c1own']
# (numerator, denominator, what the ratio isolates)
CELLS = [
    ('f2', 'm31', 'library: F2 ÷ true M31 (`8715c8ed`), one harness, `--calls 20`'),
    ('f2', 'base', 'library: F2 ÷ `ce67df76` (Gate R/Q reference library), one harness'),
    ('rev1', 'base', 'library: Gate R rev 1 head ÷ `ce67df76`, one harness (Gate R read 1.006 / 0.989)'),
    ('f2', 'rev1', 'library: F2 ÷ rev 1 head (same measured `src/`): A/A on the library'),
    ('base', 'm31', 'library: `ce67df76` ÷ `8715c8ed` (#947/#948 refactor), one harness'),
    ('f2rep', 'f2', 'protocol alone: `--repeat 21` ÷ `--calls 20`, the same F2 binary'),
    ('c1own', 'base', 'harness text alone: `c1d93389`\'s own example ÷ the shared harness, same library'),
    ('f2own', 'f2rep', 'harness text alone: F2\'s own example ÷ the shared harness, both `--repeat 21`'),
    ('f2own', 'c1own', "#941's diagnostic reproduced: F2 own `--repeat 21` ÷ `c1d93389` own `--calls 20`"),
]
ALLOC_LABELS = ['f2', 'f2rep', 'f2rept']
ALLOC_CELLS = [
    ('f2rep', 'f2', 'protocol alone, re-read: `--repeat 21` ÷ `--calls 20`, the same F2 binary'),
    ('f2rept', 'f2', '`--repeat 21` with glibc heap trimming off ÷ `--calls 20`'),
    ('f2rept', 'f2rep', 'heap trimming alone: trimming off ÷ on, both `--repeat 21`'),
]


def _module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load(path):
    opener = gzip.open if str(path).endswith('.gz') else open
    with opener(path, 'rt') as handle:
        return [json.loads(line) for line in handle if line.strip()]


def complete(r):
    return r['returncode'] == 0 and (r.get('report') or {}).get('status') == 'complete'


def metric(r):
    report = r['report']
    warm = report.get('warm_ns') or report['calls_ns'][1:]
    return statistics.median(warm) / 1e6


def interval(values, seed=958):
    rng = random.Random(seed)
    medians = sorted(statistics.median(rng.choices(values, k=len(values))) for _ in range(DRAWS))
    return medians[int(0.025 * DRAWS)], medians[int(0.975 * DRAWS) - 1]


def gap(records, out, title, labels=LABELS, cells=CELLS):
    by = {}
    bad = [r for r in records if not complete(r)]
    for r in records:
        if complete(r):
            by.setdefault(r['rep'], {})[r['arm']] = r
    digests = {r['report']['basis_sha256'] for r in records if complete(r)}
    loads = [r['load_start'] for r in records]
    l3 = {r['before'].get('l3_domains') for r in records if isinstance(r.get('before'), dict)}
    compilers = [r['before'].get('compilers') for r in records if isinstance(r.get('before'), dict)]
    compilers = [c for c in compilers if c is not None]
    out.append(f'## {title}\n')
    out.append(f'{len(records)} children, {len(bad)} incomplete; {len(by)} repetitions; '
               f'basis SHA-256s seen: {len(digests)}; load at child start {min(loads):.2f}–{max(loads):.2f} '
               f'(median {statistics.median(loads):.2f}); L3 domains per snapshot {sorted(x for x in l3 if x is not None)}; '
               f'compiler processes per snapshot {min(compilers, default="-")}–{max(compilers, default="-")}.\n')
    out.append('| arm | workers | n | median warm call, ms | min | max |')
    out.append('|---|---:|---:|---:|---:|---:|')
    for w in WORKERS:
        for label in labels:
            vals = [metric(reps[f'{label}:{w}']) for reps in by.values() if f'{label}:{w}' in reps]
            if vals:
                out.append(f'| {label} | {w} | {len(vals)} | {statistics.median(vals):.3f} | {min(vals):.3f} | '
                           f'{max(vals):.3f} |')
    out.append('')
    out.append('| ratio | workers | n | paired median [95%] | isolates |')
    out.append('|---|---:|---:|---:|---|')
    for num, den, what in cells:
        for w in WORKERS:
            a, b = f'{num}:{w}', f'{den}:{w}'
            ratios = [metric(reps[a]) / metric(reps[b]) for _, reps in sorted(by.items()) if a in reps and b in reps]
            if ratios:
                lo, hi = interval(ratios)
                out.append(f'| {num} ÷ {den} | {w} | {len(ratios)} | {statistics.median(ratios):.3f} '
                           f'[{lo:.3f}, {hi:.3f}] | {what} |')
    out.append('')


def ab_tables(directory, out):
    base = _module('m32baseline_summary', ROOT / 'research/m32-baseline/summarize.py')
    for title, d in (('#939 original (load 18–20, 2026-11-19)', ROOT / 'research/m32-baseline'),
                     ('#964 quiet re-read (this session)', directory)):
        if not (d / 'ab.jsonl.gz').exists():
            continue
        c = base.cohort(d, 'ab')
        section = []
        base.ab(c, section)
        section[0] = f'## {title}: split build ÷ instrument build (paired, median [95%])\n'
        loads = [r['load_start'] for r in load(d / 'ab.jsonl.gz')]
        section.insert(1, f'Load at child start {min(loads):.2f}–{max(loads):.2f} (median {statistics.median(loads):.2f}).\n')
        out.extend(section)


def main(argv):
    directory = Path(argv[0])
    out = ['# #958 / #964 tables (generated by summarize.py; do not edit)\n']
    if (directory / 'gap.jsonl.gz').exists():
        gap(load(directory / 'gap.jsonl.gz'), out,
            '#958 `gap`: katsura-9 / 2⁶⁴−353, `--engine entry`, median warm call per process')
    if (directory / 'alloc.jsonl.gz').exists():
        gap(load(directory / 'alloc.jsonl.gz'), out, '#958 `alloc`: why `--repeat` is slower (diagnostic, n = 11)',
            ALLOC_LABELS, ALLOC_CELLS)
    ab_tables(directory, out)
    print('\n'.join(out).rstrip())


if __name__ == '__main__':
    main(sys.argv[1:])
