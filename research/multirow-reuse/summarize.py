#!/usr/bin/env python3
"""Summarize the #715 cohort: per-cell medians, per-repeat paired ratios and the reuse census."""
import importlib.util
import json
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('study_artifacts', ROOT / 'tools/external/study_artifacts.py')
storage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(storage)

ARMS = ('stock', 'single', 'band4', 'lanes4')


def summary(path):
    attempts = [a for a in storage.iter_attempts(path) if a['status'] == 'verified']
    cells = {}
    for a in attempts:
        s = a['raw']['statistics']
        cells.setdefault((a['problem'], a['modulus']), {}).setdefault(a['arm'], []).append(dict(
            repeat=a['repeat'], wall_ms=a['process_wall_ns'] / 1e6, f4_ms=a['raw']['f4_call_ns'] / 1e6,
            forward_ms=s['forward_ns'] / 1e6, backward_ms=s['backward_ns'] / 1e6,
            rss_mib=a['raw']['peak_rss_bytes'] / 2**20, observed_rss_mib=a['observed_peak_rss_bytes'] / 2**20, load=a['load_before'], census=a['census'],
            row_operations=s['row_operations']))
    rows = []
    for (problem, modulus), arms in sorted(cells.items()):
        single = {r['repeat']: r for r in arms.get('single', [])}
        for arm in ARMS:
            runs = sorted(arms.get(arm, []), key=lambda r: r['repeat'])
            if not runs:
                continue
            row = dict(problem=problem, modulus=modulus, arm=arm, n=len(runs),
                       loads=[r['load'] for r in runs])
            for key in ('wall_ms', 'f4_ms', 'forward_ms', 'backward_ms', 'rss_mib'):
                values = [r[key] for r in runs]
                row[key] = dict(median=statistics.median(values), min=min(values), max=max(values))
            ratios = [r['forward_ms'] / single[r['repeat']]['forward_ms'] for r in runs if r['repeat'] in single]
            walls = [r['wall_ms'] / single[r['repeat']]['wall_ms'] for r in runs if r['repeat'] in single]
            row['forward_vs_single'] = dict(median=statistics.median(ratios), min=min(ratios), max=max(ratios))
            row['wall_vs_single'] = dict(median=statistics.median(walls), min=min(walls), max=max(walls))
            census = runs[0]['census']
            if census and census['matrices']:
                if any(r['census'] != census for r in runs):
                    raise ValueError('census differs between repetitions')
                row['census'] = census
            rows.append(row)
    return rows


def table(rows):
    lines = ['| problem | p | arm | forward ms (median, range) | F4 ms | process wall ms | peak RSS MiB | forward / single (paired median, range) |',
             '|---|---:|---|---:|---:|---:|---:|---:|']
    for r in rows:
        f, q = r['forward_ms'], r['forward_vs_single']
        lines.append(f"| {r['problem']} | {r['modulus']} | {r['arm']} | {f['median']:.1f} ({f['min']:.1f}–{f['max']:.1f}) | "
                     f"{r['f4_ms']['median']:.1f} | {r['wall_ms']['median']:.1f} | {r['rss_mib']['median']:.1f} | "
                     f"{q['median']:.3f} ({q['min']:.3f}–{q['max']:.3f}) |")
    lines += ['', '| problem | p | eligible rows | applications | distinct reads | reuse | entries applied | entries read | read saving | lanes4 products / scalar | reads by sharing lanes 1/2/3/4 | intra-band pivot uses | partial bands | scratch bytes |',
              '|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|---:|---:|']
    lanes = {(r['problem'], r['modulus']): r['census'] for r in rows if r['arm'] == 'lanes4' and 'census' in r}
    for r in rows:
        if r['arm'] != 'band4' or 'census' not in r:
            continue
        c, l = r['census'], lanes.get((r['problem'], r['modulus']))
        lines.append(f"| {r['problem']} | {r['modulus']} | {c['eligible_rows']} | {c['pivot_applications']} | {c['pivot_reads']} | "
                     f"{c['pivot_applications'] / c['pivot_reads']:.2f} | {c['entries_applied']} | {c['entries_read']} | "
                     f"{c['entries_applied'] / c['entries_read']:.2f}x | "
                     f"{(l['lane_products'] / c['lane_products']) if l else float('nan'):.3f} | "
                     f"{'/'.join(str(x) for x in c['reads_by_lanes'][1:])} | {c['intra_band_pivots']} | {c['partial_bands']} | "
                     f"{c['max_scratch_bytes']} |")
    return '\n'.join(lines) + '\n'


def activation(path):
    """Per-matrix shapes from one band4 response per cell; the census is deterministic."""
    seen, lines = set(), ['| problem | p | matrix | rows | columns | eligible rows | mean target entries | mean pivot entries | grobx gate (>=64) | reuse | read saving |',
                          '|---|---:|---:|---:|---:|---:|---:|---:|---|---:|---:|']
    for a in storage.iter_attempts(path):
        key = (a['problem'], a['modulus'])
        if a['status'] != 'verified' or a['arm'] != 'band4' or key in seen:
            continue
        seen.add(key)
        for index, m in enumerate(a['raw']['multirow']['matrices']):
            eligible = m['rows'] - m['first']
            if not m['pivot_reads']:
                continue
            mean_target = m['target_entries'] / eligible
            lines.append(f"| {a['problem']} | {a['modulus']} | {index} | {m['rows']} | {m['columns']} | {eligible} | "
                         f"{mean_target:.1f} | {m['entries_applied'] / m['pivot_applications']:.1f} | "
                         f"{'yes' if mean_target >= 64 else 'no'} | {m['pivot_applications'] / m['pivot_reads']:.2f} | "
                         f"{m['entries_applied'] / m['entries_read']:.2f}x |")
    return '\n'.join(lines) + '\n'


def main():
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / 'native.json.gz'
    rows = summary(path)
    (HERE / 'summary.json').write_text(json.dumps(rows, indent=1) + '\n')
    text = table(rows) + '\n' + activation(path)
    (HERE / 'table.md').write_text(text)
    print(text)


if __name__ == '__main__':
    main()
