#!/usr/bin/env python3
"""Revalidate every answer and regenerate the isolated-policy wall/RSS/work tables."""
import argparse
from collections import defaultdict
import csv
import importlib.util
import json
from pathlib import Path
from statistics import median
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/external'))
from study_artifacts import iter_attempts, _PROOFS

spec = importlib.util.spec_from_file_location('randomization_study', ROOT / 'tools/external/grobx-randomization-study.py')
study = importlib.util.module_from_spec(spec)
spec.loader.exec_module(study)


def counter_sum(phases):
    total = defaultdict(int)
    for phase in phases:
        for key, value in phase.items():
            if type(value) is int:
                total[key] += value
    return dict(sorted(total.items()))


def summarize(path):
    header = _PROOFS.load_cohort(path)
    expected = study.plan(5)
    if header['attempt_plan'] != expected or len(header['attempts']) != len(expected):
        raise ValueError('incomplete or changed declared campaign')
    refs = study.BASE.references(ROOT / 'research/competitive/results/grobx-683.json.gz')
    groups, paths = defaultdict(list), {}
    failures = []
    for number, (attempt, planned) in enumerate(zip(iter_attempts(path), expected)):
        if any(attempt[key] != value for key, value in planned.items()):
            raise ValueError('attempt order or identity differs from declared plan')
        if attempt['status'] != 'verified':
            failures.append({k: attempt.get(k) for k in ('arm', 'modulus', 'seed', 'stop', 'failure')})
            continue
        raw, request = attempt['raw'], attempt['request']
        p, arm = attempt['modulus'], attempt['arm']
        if attempt['digest'] != refs[p]['digest']:
            raise ValueError('input digest changed')
        study.BASE.validate_driver(raw, refs[p], request)
        study.validate_policy(raw, request)
        trajectory = study.sibling('grobx-trajectory').parse_report(raw['report'])
        study.validate_activation(raw, request, trajectory)
        if trajectory != attempt['trajectory']:
            raise ValueError('retained report decoder output changed')
        comparison = 'native-control' if arm in ('stock', 'native-on', 'native-off') else arm.removesuffix('-off')
        key = (p, comparison, attempt['seed'])
        structural = study.BASE.structural(trajectory)
        if paths.setdefault(key, structural) != structural:
            raise ValueError('same-policy observation control changed trajectory')
        work = raw.get('work')
        matrix_totals = validation = None
        if work:
            matrices = work['matrices']
            reports = [r for run in trajectory['runs']
                       for r in run['rounds'] + ([run['inter']] if 'inter' in run else [])]
            if len(matrices) != len(reports):
                raise ValueError('matrix/report count differs')
            for matrix, report in zip(matrices, reports):
                if (matrix['rows'], matrix['columns'], matrix['initial_entries']) != (report['rows'], report['columns'], report['entries']):
                    raise ValueError('matrix/report dimensions differ')
            matrix_totals = counter_sum(m[phase] for m in matrices for phase in ('forward', 'backsub', 'combination'))
            validation = counter_sum(m['validation'] for m in matrices)
            charged = sum(m[phase]['subtracted_entry_charges'] for m in matrices for phase in ('forward', 'backsub', 'validation'))
            totals = trajectory['totals']
            if charged != totals['subtracted_entry_charges'] + totals['interreduction_subtracted_entry_charges']:
                raise ValueError('matrix and report subtraction charges do not reconcile')
        checks = raw.get('research_audit', [])
        events = raw.get('research_events', [])
        groups[attempt['cohort'], p, arm, attempt['seed']].append({
            'wall_ms': attempt['process_wall_ns'] / 1e6,
            'rss_mib': attempt['peak_rss_bytes'] / 1024**2,
            'validation_ms': sum(c['nanoseconds'] for c in checks) / 1e6 if checks else None,
            'validation_rows': sum(c['rows'] for c in checks) if checks else None,
            'matrix_work': matrix_totals, 'validation_work': validation,
            'plain_blocks': sum(e['kind'] == 'plain-block' for e in events) if work else None,
            'signature_groups': sum(e['kind'] == 'signature-group' for e in events) if work else None,
            'signature_passed_rows': sum(e['rows'] for e in events if e['kind'] == 'signature-group' and e['passed']) if work else None,
            'engines': [r['config']['engine'] for r in trajectory['runs']],
            'reduction_modes': [r['config']['reduce'] for r in trajectory['runs']],
            'signature_rounds': sum(len(r['rounds']) for r in trajectory['runs'] if r['config']['engine'] == 'signature'),
        })
        print(number, arm, p, 'reverified', flush=True)
    if failures:
        raise ValueError('failed/stopped attempts remain; no complete performance summary: ' + repr(failures))
    result = {'schema': 1, 'measurement_commit': header['commit'], 'cells': [], 'sensitivity': []}
    for (cohort, p, arm, seed), attempts in sorted(groups.items()):
        count = 5 if cohort == 'primary' else 1
        if len(attempts) != count:
            raise ValueError('missing declared repetition')
        first = attempts[0]
        stable = [k for k in first if k not in ('wall_ms', 'rss_mib', 'validation_ms')]
        if any(any(a[k] != first[k] for k in stable) for a in attempts):
            raise ValueError('fixed-seed work/activation census changed')
        row = {'modulus': p, 'arm': arm, 'seed': seed, 'repetitions': count}
        for metric in ('wall_ms', 'rss_mib', 'validation_ms'):
            values = [a[metric] for a in attempts if a[metric] is not None]
            row[metric + '_median'] = median(values) if values else None
            row[metric + '_range'] = [min(values), max(values)] if values else None
        row.update({k: first[k] for k in stable})
        result['cells' if cohort == 'primary' else 'sensitivity'].append(row)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path(__file__).with_name('cohort.json.gz'))
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('summary.json'))
    args = parser.parse_args()
    result = summarize(args.input)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    rows = [{key: row[key] for key in ('modulus', 'arm', 'seed', 'repetitions', 'wall_ms_median', 'wall_ms_range', 'rss_mib_median', 'rss_mib_range', 'validation_ms_median', 'validation_ms_range', 'plain_blocks', 'signature_groups', 'signature_passed_rows')} for row in result['cells']]
    with args.output.with_suffix('.csv').open('w') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator='\n')
        writer.writeheader()
        writer.writerows(rows)


if __name__ == '__main__':
    main()
