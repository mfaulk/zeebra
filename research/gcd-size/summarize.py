#!/usr/bin/env python3
"""Regenerate size/overhead tables while rechecking every complete retained GCD."""
import csv
import gzip
import importlib.util
import json
from pathlib import Path
import statistics
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
spec = importlib.util.spec_from_file_location('gcd_size_study', ROOT / 'tools/external/gcd-size-study.py')
study = importlib.util.module_from_spec(spec)
spec.loader.exec_module(study)


def summarize(cohort):
    answers, groups, profiles = {}, {}, {}
    for attempt in cohort['attempts']:
        key = tuple(attempt[k] for k in ('field', 'arity', 'shape', 'route', 'arm', 'diagnostic'))
        groups.setdefault(key, []).append(attempt)
        if attempt['status'] in ('completed', 'refused'):
            raw = attempt['raw']
            study.validate(raw, answers, key[:3], attempt['arm'] == 'on', attempt['route'])
            if raw.get('profile') is not None:
                pkey = key[:4] + (key[-1],)
                if profiles.setdefault(pkey, raw['profile']) != raw['profile']:
                    raise ValueError('size profile differs across fixed-input repetitions')
    rows = []
    for key, attempts in groups.items():
        row = dict(zip(('field', 'arity', 'shape', 'route', 'arm', 'diagnostic'), key))
        row['outcomes'] = {status: sum(a['status'] == status for a in attempts)
                           for status in ('completed', 'refused', 'stopped', 'failed')}
        complete = [a for a in attempts if a['status'] == 'completed']
        # A stopped attempt contributes no censored wall time to a completed-run median.
        if complete:
            for label, values in [
                ('process_wall_ns', [a['process_wall_ns'] for a in complete]),
                ('peak_rss_bytes', [a['peak_rss_bytes'] for a in complete]),
                ('elapsed_ns', [a['raw']['elapsed_ns'] for a in complete]),
            ]:
                row[label] = {'median': statistics.median(values), 'min': min(values), 'max': max(values)}
            row['input_sha256'] = complete[0]['raw']['input_sha256']
            row['profile'] = complete[0]['raw'].get('profile')
        rows.append(row)
    return {'source_commit': cohort['commit'], 'completed_plan': cohort.get('completed_plan', False),
            'refusal': cohort.get('refusal'), 'attempts': len(cohort['attempts']), 'rows': rows}


def main():
    source = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE / 'cohort.json.gz'
    with gzip.open(source, 'rt') as stream:
        cohort = json.load(stream)
    summary = summarize(cohort)
    (HERE / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    fields = ['field', 'arity', 'shape', 'route', 'arm', 'diagnostic', 'completed', 'refused', 'stopped', 'failed',
              'elapsed_ns', 'process_wall_ns', 'peak_rss_bytes', 'prs_terms', 'prs_coefficient_degree',
              'raw_terms', 'raw_coefficient_degree', 'image_terms', 'image_coefficient_degree',
              'interpolant_terms', 'interpolant_coefficient_degree', 'content_calls', 'gcd_calls', 'local_degree_bound']
    with (HERE / 'summary.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        for row in summary['rows']:
            flat = {name: row[name] for name in fields[:6]}
            flat.update(row['outcomes'])
            if 'elapsed_ns' in row:
                flat.update({name: row[name]['median'] for name in ('elapsed_ns', 'process_wall_ns', 'peak_rss_bytes')})
            profile = row.get('profile')
            if profile:
                for prefix, phase in [('prs', 'prs_entries'), ('raw', 'raw_remainders'),
                                      ('image', 'brown_images'), ('interpolant', 'brown_interpolants')]:
                    flat[prefix + '_terms'] = profile[phase]['max_terms']
                    flat[prefix + '_coefficient_degree'] = profile[phase]['max_coefficient_degree']
                flat.update(content_calls=profile['content_calls'], gcd_calls=profile['gcd_calls'],
                            local_degree_bound=profile['max_subresultant_degree_bound'])
            writer.writerow(flat)
    print(f"validated {summary['attempts']} retained attempts in {len(summary['rows'])} groups")


if __name__ == '__main__':
    main()
