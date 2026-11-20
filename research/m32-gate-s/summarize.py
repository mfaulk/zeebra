#!/usr/bin/env python3
"""#940 Gate S tables from this directory's records. Every attempt is counted; only complete ones
are timed. Head ÷ base ratios are paired per repetition (M31's `median_interval`: median of the
per-repetition ratios, 95% percentile bootstrap, 20,000 draws). The precision rule (plan §10.3):
a cell is readable when its interval half-width is at most half the distance from its threshold
to 1.0.

    python3 research/m32-gate-s/summarize.py research/m32-gate-s > research/m32-gate-s/tables.md
"""
import importlib.util
import statistics
import sys
import zlib
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def _module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


M0 = _module('m31summary', ROOT / 'research/m31-baseline/summarize.py')
campaign = _module('m32gates', HERE / 'campaign.py')
STAGES = ('symbolic', 'elimination', 'bookkeeping', 'interreduction')


class Cohort:
    """(row, arm) → rep → complete record, per suite; and every attempt's failure, if any."""

    def __init__(self, records):
        self.runs = defaultdict(dict)
        self.attempts = defaultdict(int)
        self.failures = defaultdict(list)
        for r in records:
            key = (r['suite'], r['row'], r['arm'])
            self.attempts[key] += 1
            if M0.complete(r):
                self.runs[key][r['rep']] = r
            else:
                self.failures[key].append((r.get('report') or {}).get('status', f"rc={r['returncode']}"))

    def values(self, suite, row, arm, read):
        return {k: read(r) for k, r in self.runs[(suite, row, arm)].items()}

    def ratio(self, suite, row, a, b, read):
        values = M0.paired(self.values(suite, row, a, read), self.values(suite, row, b, read))
        return M0.median_interval(values, zlib.crc32(f'{suite} {row} {a} {b}'.encode())) if values else None

    def median(self, suite, row, arm, read):
        values = list(self.values(suite, row, arm, read).values())
        return statistics.median(values) if values else None


def wall(r):
    return r['process_wall_ns'] / 1e9


def call(r):
    return r['report']['call_ns'] / 1e9


def rss(r):
    return r['report']['peak_rss_bytes']


def stage(name):
    return lambda r: r['report']['statistics'][f'{name}_ns'] / 1e9


def fmt(cell, digits=3):
    return '—' if cell is None else f'{cell[0]:.{digits}f} [{cell[1]:.{digits}f}, {cell[2]:.{digits}f}]'


def precise(cell, threshold):
    """Plan §10.3: half-width ≤ half the distance from the threshold to 1.0."""
    return cell is not None and (cell[2] - cell[1]) / 2 <= abs(threshold - 1.0) / 2


def verdict(cell, passes, threshold):
    if cell is None:
        return 'no data'
    if not precise(cell, threshold):
        return 'imprecise'
    return 'met' if passes(cell) else 'missed'


def gate_table(c):
    out = ['## Gate S (plan §8.2)', '',
           '| Criterion | Cell | Threshold | Half-width | Result |', '|---|---|---|---:|---|']
    t1 = c.ratio('gate', campaign.ECO, 'b-cl:16', 'h-cl:16', stage('symbolic'))
    t2 = c.ratio('gate', campaign.ECO, 'h-en:16', 'b-en:16', wall)
    rows = [('T1 Eco-12 symbolic, base ÷ head, cl:16', t1, 'median ≥ 1.5, lower ≥ 1.4',
             lambda x: x[0] >= 1.5 and x[1] >= 1.4, 1.4),
            ('T2 Eco-12 process wall, head ÷ base, en:16', t2, 'median ≤ 0.90, upper ≤ 0.92',
             lambda x: x[0] <= 0.90 and x[2] <= 0.92, 0.92)]
    for name, cell, text, passes, threshold in rows:
        half = '—' if cell is None else f'{(cell[2] - cell[1]) / 2:.3f}'
        out.append(f'| {name} | {fmt(cell)} | {text} | {half} | {verdict(cell, passes, threshold)} |')
    return '\n'.join(out)


def dev_table(c):
    out = ['## Dev corpus: head ÷ base, `en` (process wall; in-process call time under 50 ms)', '',
           '| Row | W | Read | n | Head ÷ base [95%] | Upper ≤ 1.05 | RSS head ÷ base | RSS ≤ 1.10 |',
           '|---|---:|---|---:|---|---|---:|---|']
    rows = ([('gate', campaign.ECO, w) for w in (1, 16)]
            + [('gate', r, w) for r in campaign.LARGE for w in (1, 16)]
            + [('mq10', r, w) for r in campaign.MQ10 for w in (1, 16)]
            + [('small', r, w) for r in campaign.SMALL for w in (1, 16)])
    for suite, row, w in rows:
        read = call if suite == 'small' else wall
        a, b = f'h-en:{w}', f'b-en:{w}'
        cell = c.ratio(suite, row, a, b, read)
        n = len(M0.paired(c.values(suite, row, a, read), c.values(suite, row, b, read)))
        ra, rb = c.median(suite, row, a, rss), c.median(suite, row, b, rss)
        rr = None if ra is None or rb is None else ra / rb
        regress = verdict(cell, lambda x: x[2] <= 1.05, 1.05)
        memory = '—' if rr is None else ('met' if rr <= 1.10 else 'missed')
        rtext = '—' if rr is None else f'{rr:.3f}'
        out.append(f'| {row} | {w} | {"call" if suite == "small" else "wall"} | {n} | {fmt(cell)} | {regress} '
                   f'| {rtext} | {memory} |')
    return '\n'.join(out)


def curve_table(c):
    out = ['## Worker curve, `cl` (medians, ms; symbolic speed-up is base ÷ head, paired)', '',
           '| Row | W | Build | Wall | Symbolic | Elimination | Bookkeeping | Interreduction | Symbolic base ÷ head |',
           '|---|---:|---|---:|---:|---:|---:|---:|---|']
    for row, _ in campaign.SUITES['curve']:
        for w in (1, 2, 4, 8, 16):
            for build in ('b', 'h'):
                arm = f'{build}-cl:{w}'
                med = [c.median('curve', row, arm, f) for f in [wall] + [stage(s) for s in STAGES]]
                cells = ' | '.join('—' if m is None else f'{m * 1e3:,.1f}' for m in med)
                speed = fmt(c.ratio('curve', row, f'b-cl:{w}', f'h-cl:{w}', stage('symbolic'))) if build == 'h' else ''
                out.append(f'| {row} | {w} | {build} | {cells} | {speed} |')
    return '\n'.join(out)


def mq10_table(c):
    out = ['## MQ10 re-read (for #927): medians, ms; ratios paired', '',
           '| Row | W | head `en` | base `en` | head `f4` | `en` head ÷ base | head `en` ÷ head `f4` |',
           '|---|---:|---:|---:|---:|---|---|']
    for row in campaign.MQ10:
        for w in (1, 4, 8, 16):
            med = [c.median('mq10', row, a, wall) for a in (f'h-en:{w}', f'b-en:{w}', f'h-f4:{w}')]
            cells = ' | '.join('—' if m is None else f'{m * 1e3:,.1f}' for m in med)
            out.append(f'| {row} | {w} | {cells} | {fmt(c.ratio("mq10", row, f"h-en:{w}", f"b-en:{w}", wall))} '
                       f'| {fmt(c.ratio("mq10", row, f"h-en:{w}", f"h-f4:{w}", wall))} |')
    return '\n'.join(out)


def attempts_table(c):
    out = ['## Attempts', '', '| Suite | Row | Arm | Attempts | Complete | Failures |', '|---|---|---|---:|---:|---|']
    for (suite, row, arm), n in sorted(c.attempts.items()):
        fails = '; '.join(sorted(set(c.failures[(suite, row, arm)])))[:80] or '—'
        out.append(f'| {suite} | {row} | {arm} | {n} | {len(c.runs[(suite, row, arm)])} | {fails} |')
    return '\n'.join(out)


def main(directory):
    paths = [str(p) for p in sorted(Path(directory).glob('*.jsonl*'))]
    c = Cohort(M0.load(paths))
    print('# #940 Gate S tables\n\nGenerated by `summarize.py` from this directory\'s records.\n')
    for table in (gate_table, dev_table, curve_table, mq10_table, attempts_table):
        print(table(c))
        print()


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else HERE)
