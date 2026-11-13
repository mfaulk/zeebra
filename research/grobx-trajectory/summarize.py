#!/usr/bin/env python3
"""Recompute work and wall/RSS tables from retained full-answer attribution attempts."""
import argparse
from collections import defaultdict
import csv
import json
import sys
from pathlib import Path
from statistics import median

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/external'))
from study_artifacts import load_study


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
    result = {'schema': 1, 'measured_commit': cohort['commit'], 'cells': [], 'work': {}, 'stock_first_trajectories': {}}
    for (modulus, arm), attempts in sorted(grouped.items()):
        walls = [a['process_wall_ns'] / 1e6 for a in attempts]
        rss = [a['peak_rss_bytes'] / 1024**2 for a in attempts]
        result['cells'].append({'modulus': modulus, 'arm': arm, 'repetitions': len(attempts),
                               'wall_median_ms': median(walls), 'wall_range_ms': [min(walls), max(walls)],
                               'rss_median_mib': median(rss), 'rss_range_mib': [min(rss), max(rss)]})
        if arm == 'grobx-stock':
            result['stock_first_trajectories'][str(modulus)] = attempts[0]['trajectory']
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
            reported = [r for run in attempts[0]['trajectory']['runs']
                        for r in run['rounds'] + ([run['inter']] if 'inter' in run else [])]
            if len(reported) != len(matrices):
                raise ValueError('grobx passive matrix count differs from report')
            for matrix, report in zip(matrices, reported):
                if (matrix['rows'], matrix['columns'], matrix['initial_entries']) != (report['rows'], report['columns'], report['entries']):
                    raise ValueError('grobx passive matrix dimensions differ from report')
            charged = sum(m[p]['subtracted_entry_charges'] for m in matrices for p in ('forward', 'backsub'))
            total = attempts[0]['trajectory']['totals']
            if charged != total['subtracted_entry_charges'] + total['interreduction_subtracted_entry_charges']:
                raise ValueError('grobx matrix charges do not reconcile with report')
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
    cohort = load_study(args.input)
    validate(cohort)
    result = summarize(cohort)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    csv_path = args.output.with_suffix('.csv')
    with csv_path.open('w') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(result['cells'][0]), lineterminator='\n')
        writer.writeheader()
        writer.writerows(result['cells'])
    round_rows = []
    for modulus in (32003, 2147483647):
        for engine in ('zeebra', 'grobx'):
            work = result['work'][str(modulus) + ':' + engine]
            if engine == 'grobx':
                labels = [(r['config']['engine'], b.get('number', 'inter'), dict(b, native_mode=r['config'].get('reduce')))
                          for r in result['stock_first_trajectories'][str(modulus)]['runs']
                          for b in r['rounds'] + ([r['inter']] if 'inter' in r else [])]
            for index, matrix in enumerate(work['matrices']):
                phase, number, report = labels[index] if engine == 'grobx' else ('f4', index + 1, matrix)
                fwd, back = matrix['forward'], matrix['backward' if engine == 'zeebra' else 'backsub']
                product = 'coefficient_products' if engine == 'zeebra' else 'executed_lane_products'
                round_rows.append({
                    'field': modulus, 'engine': engine, 'phase': phase, 'round': number,
                    'degree': report.get('degree'), 'pairs_native': report.get('pairs'),
                    'rows': matrix['rows'], 'columns': matrix['columns'],
                    'given_rows_native': matrix.get('given', matrix['rows'] - matrix.get('reducer_rows', 0)),
                    'mode': report.get('native_mode', 'deterministic structured/Adaptive'),
                    'initial_entries': matrix['initial_entries'],
                    'initial_density': matrix['initial_entries'] / (matrix['rows'] * matrix['columns']) if matrix['rows'] * matrix['columns'] else 0,
                    'rank_or_new_pivots': report.get('rank', report.get('pivots')),
                    'rank_semantics': 'full rank' if engine == 'zeebra' else 'new pivots',
                    'zero_native': report.get('zero_rows', report.get('zero')),
                    'zero_semantics': 'input rows' if engine == 'zeebra' else 'reductions including combination/tests when active',
                    'known_zero_rows_native': report.get('zero-rows', report.get('zero_rows')),
                    'forward_products': fwd[product], 'back_products': back[product],
                    'peak_stored_sparse_entries': matrix.get('peak_sparse_live_entries', matrix.get('peak_stored_sparse_entries')),
                })
    with args.output.with_name(args.output.stem + '-rounds.csv').open('w') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(round_rows[0]), lineterminator='\n')
        writer.writeheader()
        writer.writerows(round_rows)
    print('verified attempts', len(cohort['attempts']), 'cells', len(result['cells']))


if __name__ == '__main__':
    main()
