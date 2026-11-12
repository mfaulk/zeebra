#!/usr/bin/env python3
"""Reject incomplete or mismatched cohorts before regenerating the published figures."""
import csv
import gzip
import json
from pathlib import Path
import re
from statistics import median

ROOT = Path(__file__).resolve().parent


def load(name, count):
    with gzip.open(ROOT / 'results' / (name + '.json.gz'), 'rt') as stream:
        cohort = json.load(stream)
    rows = cohort['attempts']
    if len(rows) != count or any(r['exit'] or r['stop'] for r in rows):
        raise ValueError('incomplete successful cohort: ' + name)
    return rows


def structural(report):
    stats = report['statistics']
    if isinstance(stats, dict):
        return {k: v for k, v in stats.items() if not k.endswith('_ns') and k != 'full_statistics'}
    return dict(re.findall(r'^\s*(\w+): (\d+),?$', stats, re.MULTILINE))


def paired(rows, time):
    if len(rows) != 2 * len({r['repeat'] for r in rows}):
        raise ValueError('duplicate or incomplete paired attempts')
    arms = {arm: [r for r in rows if r['arm'] == arm] for arm in ('baseline', 'candidate')}
    pairs = []
    for repeat in sorted({r['repeat'] for r in rows}):
        pair = {r['arm']: r for r in rows if r['repeat'] == repeat}
        if set(pair) != set(arms):
            raise ValueError('missing paired attempt')
        pairs.append(time(pair['candidate']['report']) / time(pair['baseline']['report']))
    return dict(baseline_ms=median(time(r['report']) for r in arms['baseline']) / 1e6,
                candidate_ms=median(time(r['report']) for r in arms['candidate']) / 1e6,
                paired_ratio=median(pairs), paired_min=min(pairs), paired_max=max(pairs),
                baseline_rss_mib=max(r['report']['peak_rss_bytes'] for r in arms['baseline']) / 2**20,
                candidate_rss_mib=max(r['report']['peak_rss_bytes'] for r in arms['candidate']) / 2**20)


def main():
    solves, pilot = load('solves', 120), load('pilot', 30)
    curves, arithmetic = load('curves', 540), load('arithmetic', 7)
    regions, diagnostics = load('region-fixed', 3), load('diagnostic', 6)
    work = load('work', 8)
    for label in {r['label'] for r in solves}:
        for repeat in range(5):
            pair = [r['report'] for r in solves if r['label'] == label and r['repeat'] == repeat]
            a, b = pair
            for key in ('modulus', 'digest'):
                if a[key] != b[key]:
                    raise ValueError('solve input mismatch')
            if sorted(a['basis']) != sorted(b['basis']) or structural(a) != structural(b):
                raise ValueError('solve arithmetic/work mismatch')
    output = dict(source='6578c0ab; delayed.patch e057dd71136cfb39de009bbb215eac1fb833686b435e64a7fc966d8f93a5bc0e',
                  arithmetic={key: median(r['report'][key] / r['report']['entries'] for r in arithmetic)
                              for key in ('generic_ns', 'delayed_ns', 'canonical_pilot_ns')},
                  solves={}, pilot={}, counters={}, diagnostic={})
    for label in dict.fromkeys(r['label'] for r in solves):
        rows = [r for r in solves if r['label'] == label]
        output['solves'][label] = paired(rows, lambda r: r.get('f4_call_ns', r.get('wall_ns')))
    for shape in ('k7', 'c6', 'k6lex'):
        output['pilot'][shape] = paired([r for r in pilot if r['cell'][1] == shape], lambda r: r['elimination_ns'])
        # Capture can run earlier pilot batches; the final diagnostic line is the selected replay.
        row = next(r for r in diagnostics if r['arm'] == 'candidate' and r['cell'][1] == shape)
        line = row['stderr'].strip().splitlines()[-1]
        output['diagnostic'][shape] = {key: int(value) for key, value in re.findall(r'(\w+)=(\d+)', line)}
    with (ROOT / 'curves.csv').open('w') as stream:
        columns = ('field', 'shape', 'eighths', 'rows', 'columns', 'density_pct', 'rank', 'peak_nonzeros',
                   'sparse_forward_ms', 'dense_forward_ms', 'adaptive_forward_ms',
                   'sparse_total_ms', 'dense_total_ms', 'adaptive_total_ms', 'peak_rss_mib')
        writer = csv.DictWriter(stream, fieldnames=columns, lineterminator='\n')
        writer.writeheader()
        for field in ('m31', 'p64', 'bn254'):
            for shape in ('k7', 'c6', 'k6lex'):
                densities, dense_ratios, adaptive_ratios = [], [], []
                for eighths in (1, 2, 4, 8):
                    rows = [r['report'] for r in curves if r['cell'][:3] == [field, shape, eighths]]
                    first = rows[0]
                    for row in rows:
                        for key in ('source', 'input_hash', 'rref_hash', 'rank', 'peak_nonzeros', 'row_operations'):
                            if row[key] != first[key]:
                                raise ValueError('curve mismatch: ' + key)
                    result = {key: first[key] for key in ('rows', 'columns', 'rank', 'peak_nonzeros')}
                    result.update(field=field, shape=shape, eighths=eighths,
                                  density_pct=100 * first['initial_nonzeros'] / (first['rows'] * first['columns']),
                                  peak_rss_mib=max(r['peak_rss_bytes'] for r in rows) / 2**20)
                    for backend in ('sparse', 'dense', 'adaptive'):
                        group = [r for r in rows if r['backend'].lower() == backend]
                        if len(group) != 5:
                            raise ValueError('curve coverage differs')
                        result[backend + '_forward_ms'] = median(r['forward_ns'] for r in group) / 1e6
                        result[backend + '_total_ms'] = median(r['elimination_ns'] for r in group) / 1e6
                    writer.writerow(result)
                    densities.append(f"{result['density_pct']:.2f}")
                    dense_ratios.append(f"{result['dense_forward_ms']/result['sparse_forward_ms']:.2f}")
                    adaptive_ratios.append(f"{result['adaptive_forward_ms']/result['sparse_forward_ms']:.2f}")
                print(f"| {field}/{shape} | {' / '.join(densities)} | {' / '.join(dense_ratios)} | {' / '.join(adaptive_ratios)} |")
    events = [r['events'] for r in regions]
    output['counters'] = {key: median(r[key] for r in events) for key in events[0]}
    output['counters']['elimination_ms'] = median(r['report']['elimination_ns'] for r in regions) / 1e6
    output['counters']['read_fill_gb_s'] = median(
        64 * (r['events']['ls_any_fills_from_sys.mem_io_local:u'] + r['events']['ls_any_fills_from_sys.mem_io_remote:u'])
        / r['report']['elimination_ns'] for r in regions)
    row = next(r['report'] for r in work if r['arm'] == 'baseline' and r['report']['label'].startswith('mq-random-10'))
    counts = [row['scaffold_pivot_targets'], row['new_pivot_targets']]
    operations = 2 * sum(r['pivot_terms'] for r in counts)
    traffic = sum(r['own_terms'] - r['prefix_terms'] + r['pivot_terms'] + 3 * (r['output_terms'] - r['prefix_terms']) for r in counts) * row['bytes_per_entry']
    output['logical_back_substitution'] = dict(field_operations=operations, tuple_bytes=traffic,
                                             field_operations_per_byte=operations / traffic)
    (ROOT / 'summary.json').write_text(json.dumps(output, indent=2) + '\n')
    for label, result in output['solves'].items():
        print(f"| {label} | {result['baseline_ms']:.3f} → {result['candidate_ms']:.3f} | {result['paired_ratio']:.3f} ({result['paired_min']:.3f}–{result['paired_max']:.3f}) | {result['baseline_rss_mib']:.2f} → {result['candidate_rss_mib']:.2f} |")


if __name__ == '__main__':
    main()
