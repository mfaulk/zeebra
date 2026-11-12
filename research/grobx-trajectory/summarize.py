#!/usr/bin/env python3
"""Recompute work and wall/RSS tables from retained full-answer attribution attempts."""
import argparse
from collections import defaultdict
import csv
import gzip
import json
from pathlib import Path
from statistics import median

ROOT = Path(__file__).resolve().parents[2]


def add(phases):
    total = defaultdict(int)
    for phase in phases:
        for key, value in phase.items():
            if type(value) is int:
                total[key] += value
    return dict(sorted(total.items()))


def validate(cohort):
    import importlib.util
    path = ROOT / 'tools/external/grobx-work-study.py'
    spec = importlib.util.spec_from_file_location('study_validation', path)
    study = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(study)
    refs = study.references(ROOT / 'research/competitive/results/grobx-683.json.gz')
    paths = {}
    for attempt in cohort['attempts']:
        if attempt['status'] != 'verified':
            raise ValueError('failed/stopped attempt retained: no clean timing summary')
        modulus, arm, raw = attempt['modulus'], attempt['arm'], attempt['raw']
        if attempt['digest'] != refs[modulus]['digest']:
            raise ValueError('cohort digest drift')
        if arm.startswith('grobx'):
            request = dict(refs[modulus]['request'])
            if not arm.endswith('stock'):
                request['research_work'] = arm.endswith('on')
            study.validate_driver(raw, refs[modulus], request)
            path = study.structural(study.sibling('grobx-trajectory').parse_report(raw['report']))
        else:
            study.sibling('mq10-profile').check_answer(raw, refs[modulus])
            path = {k: v for k, v in raw['statistics'].items() if not k.endswith('_ns') and k != 'full_statistics'}
        key = (arm.split('-')[0], modulus)
        if paths.setdefault(key, path) != path:
            raise ValueError('passive observer changed trajectory')
    if len(cohort['attempts']) != 12 * cohort['repetitions']:
        raise ValueError('incomplete six-arm two-field cohort')


def summarize(cohort):
    grouped = defaultdict(list)
    for attempt in cohort['attempts']:
        if attempt['status'] != 'verified':
            raise ValueError('failed/stopped attempts cannot become a clean timing summary')
        grouped[attempt['modulus'], attempt['arm']].append(attempt)
    result = {'schema': 1, 'measured_commit': cohort['commit'], 'cells': [], 'work': {}}
    for (modulus, arm), attempts in sorted(grouped.items()):
        walls = [a['process_wall_ns'] / 1e6 for a in attempts]
        rss = [a['peak_rss_bytes'] / 1024**2 for a in attempts]
        result['cells'].append({'modulus': modulus, 'arm': arm, 'repetitions': len(attempts),
                               'wall_median_ms': median(walls), 'wall_range_ms': [min(walls), max(walls)],
                               'rss_median_mib': median(rss), 'rss_range_mib': [min(rss), max(rss)]})
        if not arm.endswith('on'):
            continue
        work = attempts[0]['raw']['work']
        if any(a['raw']['work'] != work for a in attempts):
            raise ValueError('work census changes across fixed-input repetitions')
        if arm.startswith('zeebra'):
            matrices = work['batches']
            phases = [m[p] for m in matrices for p in ('forward', 'backward')]
            total = add(phases)
            if total['pivot_applications'] != attempts[0]['raw']['statistics']['row_operations']:
                raise ValueError('Zeebra batch pivot count does not reconcile with F4 statistics')
            result['work'][str(modulus) + ':zeebra'] = {
                'batch_totals': total,
                'forward': add(m['forward'] for m in matrices),
                'backward': add(m['backward'] for m in matrices),
                'outside_batch': add(work['outside_batch'][p] for p in ('forward', 'backward')),
                'matrices': matrices,
                'outside_matrix': work['outside_batch'],
            }
        else:
            matrices = work['matrices']
            phases = [m[p] for m in matrices for p in ('forward', 'backsub', 'combination')]
            result['work'][str(modulus) + ':grobx'] = {
                'all_matrix_totals': add(phases),
                'forward': add(m['forward'] for m in matrices),
                'backward': add(m['backsub'] for m in matrices),
                'combination': add(m['combination'] for m in matrices),
                'outside_matrix': work['outside_matrix'],
                'matrices': matrices,
            }
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=ROOT / 'research/competitive/results/grobx-trajectory-native.json.gz')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('summary.json'))
    args = parser.parse_args()
    with gzip.open(args.input, 'rt') as stream:
        cohort = json.load(stream)
    validate(cohort)
    result = summarize(cohort)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    csv_path = args.output.with_suffix('.csv')
    with csv_path.open('w') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(result['cells'][0]))
        writer.writeheader()
        writer.writerows(result['cells'])
    print('verified attempts', len(cohort['attempts']), 'cells', len(result['cells']))


if __name__ == '__main__':
    main()
