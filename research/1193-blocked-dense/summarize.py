#!/usr/bin/env python3
"""#1193 development tables from the campaign's JSON lines.

    summarize.py campaign-<commit>.jsonl [counts.jsonl]

Medians and minima over the reps of each arm, the ratios built from the medians, and the load
range each figure was taken under. Laptop, unpinned: development figures that decide nothing.
"""
import json
import statistics
import sys
from collections import defaultdict


def name(record):
    archive = record['archive'].rsplit('/', 1)[-1]
    field, row, batch = archive.removesuffix('.zmat').split('__')
    return f"{field} {row.removeprefix('mq-dense-').split('-')[0]} {batch}"


def main(path, counts_path=None):
    runs = defaultdict(lambda: defaultdict(list))
    shape = {}
    loads = defaultdict(list)
    for line in open(path):
        r = json.loads(line)
        key = name(r)
        loads[key] += [r['load_before'], r['load_after']]
        if r['arm'] == 'lane':
            runs[key]['lane'].append(r['forward_seconds'])
        else:
            for k in ('sweep_seconds', 'blocked_seconds', 'lane_residual_forward_seconds',
                      'lane_residual_backward_seconds'):
                runs[key][k].append(r[k])
            assert r['lane_residual_agrees']
            shape[key] = r

    print('| Batch | D\' rows × columns | density | span fraction | rank | blocked products |')
    print('|---|---|---|---|---|---|')
    for key, r in shape.items():
        print(f"| {key} | {r['residual_rows']} × {r['free_columns']} | {r['residual_density']:.3f} "
              f"| {r['residual_span_fraction']:.3f} | {r['rank']} | {r['products']:,} |")
    print()
    print('Seconds, median [min] of the reps; load is the 1-minute range over the session.')
    print()
    print('| Batch | lane, whole batch | f64 sweep | blocked RREF of D\' | lane forward on D\' '
          '| lane back-sub on D\' | kernel ratio | matrix ratio | reps | load |')
    print('|---|---|---|---|---|---|---|---|---|---|')
    for key, arms in runs.items():
        med = {k: statistics.median(v) for k, v in arms.items()}
        low = {k: min(v) for k, v in arms.items()}
        cell = lambda k: f"{med[k]:.2f} [{low[k]:.2f}]"
        kernel = med['lane_residual_forward_seconds'] / med['blocked_seconds']
        matrix = med['lane'] / (med['sweep_seconds'] + med['blocked_seconds'])
        reps = min(len(v) for v in arms.values())
        print(f"| {key} | {cell('lane')} s | {cell('sweep_seconds')} s | {cell('blocked_seconds')} s "
              f"| {cell('lane_residual_forward_seconds')} s | {cell('lane_residual_backward_seconds')} s "
              f"| {kernel:.2f} | {matrix:.2f} | {reps} | {min(loads[key]):.1f}–{max(loads[key]):.1f} |")
    if counts_path:
        print()
        print('| Batch | forward products | against reducers | against discovered pivots '
              '| sweep products | forward products on D\' | D\' share of FL products |')
        print('|---|---|---|---|---|---|---|')
        for line in open(counts_path):
            r = json.loads(line)
            fl = r['sweep_products'] + r['residual_forward_products']
            print(f"| {name(r)} | {r['forward_products']:,} | {r['inherited_products']:,} "
                  f"| {r['discovered_products']:,} | {r['sweep_products']:,} "
                  f"| {r['residual_forward_products']:,} | {r['residual_forward_products'] / fl:.3f} |")


if __name__ == '__main__':
    main(*sys.argv[1:])
