#!/usr/bin/env python3
"""Verify retained full answers and regenerate the pivot study's tables."""
from collections import defaultdict
import csv
import importlib.util
import json
from pathlib import Path
import statistics

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def tool(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT / 'tools/external' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def spread(values):
    values = list(values)
    return dict(median=statistics.median(values), minimum=min(values), maximum=max(values))


def write_csv(name, rows):
    if not rows:
        return
    with (HERE / name).open('w') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator='\n')
        writer.writeheader()
        writer.writerows(rows)


def main():
    storage = tool('study_artifacts')
    driver = tool('pivot-discovery-study')
    refs = tool('grobx-work-study').references(ROOT / 'research/competitive/results/grobx-683.json.gz')
    check = tool('mq10-profile').check_answer
    census = storage.load_study(HERE / 'census.json.gz')
    assert len(census['attempts']) == 40 and 'refusal' not in census
    grouped = defaultdict(list)
    matrix_rows = []
    for attempt in census['attempts']:
        assert attempt['status'] == 'verified' and attempt['exit'] == 0 and attempt['stop'] is None
        raw = attempt['raw']
        check(raw, refs[attempt['modulus']])
        grouped[(attempt['modulus'], attempt['arm'])].append(attempt)
        if attempt['arm'] == 'discovery':
            summaries = [driver.census(batch['discovery']) for batch in raw['work']['batches']]
            assert summaries == attempt['census']
            for index, (batch, summary) in enumerate(zip(raw['work']['batches'], summaries)):
                assert summary['inherited_products'] + summary['discovered_products'] == batch['forward']['coefficient_products']
                assert summary['new_rank'] + batch['reducer_rows'] == batch['rank']
                assert summary['zero_rows'] == batch['zero_rows']
                if attempt['repeat'] == 0:
                    matrix_rows.append(dict(modulus=attempt['modulus'], batch=index, degree=batch['degree'],
                        columns=batch['columns'], reducers=batch['reducer_rows'], **summary))
    census_summary = []
    for (modulus, arm), attempts in sorted(grouped.items()):
        assert len(attempts) == 5
        row = dict(modulus=modulus, arm=arm, process_wall_ms=spread(a['process_wall_ns']/1e6 for a in attempts),
                   rss_mib=spread(a['peak_rss_bytes']/1024**2 for a in attempts))
        if arm == 'discovery':
            row['forward_share'] = spread(sum(b['row_sum_ns'] for b in a['census'])/a['raw']['statistics']['total_ns'] for a in attempts)
        census_summary.append(row)
    interrupted = storage.load_study(HERE / 'census-interrupted.json.gz')
    assert interrupted['refusal']['reason'] == 'load' and len(interrupted['attempts']) == 7
    for attempt in interrupted['attempts']:
        assert attempt['status'] == 'verified' and attempt['exit'] == 0 and attempt['stop'] is None
        check(attempt['raw'], refs[attempt['modulus']])
    summary = dict(census_commit=census['commit'], census=census_summary,
                   separately_retained_interrupted_attempts=len(interrupted['attempts']))
    write_csv('matrix-census.csv', matrix_rows)
    parallel_path = HERE / 'parallel.json.gz'
    if parallel_path.exists():
        parallel = storage.load_study(parallel_path)
        assert len(parallel['attempts']) == 310 and len(parallel['dispatch']) == 35 and 'refusal' not in parallel
        groups, batch_groups = defaultdict(list), defaultdict(list)
        digests = {}
        for attempt in parallel['attempts']:
            assert attempt['status'] == 'verified' and attempt['stop'] is None and attempt['exit'] == 0
            raw = attempt['raw']
            check(raw, refs[attempt['modulus']])
            groups[(attempt['modulus'], attempt['arm'])].append(attempt)
            if raw.get('parallel'):
                for batch in raw['parallel']['batches']:
                    batch_groups[(attempt['modulus'], attempt['arm'], batch['batch_index'])].append(batch)
                    if attempt['arm'].endswith('-on'):
                        key = (attempt['modulus'], batch['batch_index'])
                        assert digests.setdefault(key, batch['input_matrix_digest']) == batch['input_matrix_digest']
                        assert batch['products'] == batch['work']['coefficient_products'] == batch['inherited_products'] + batch['discovered_products']
                        assert sum(batch['worker_rows']) == batch['rows'] - batch['split']
        rows = []
        for (modulus, arm), attempts in sorted(groups.items()):
            assert len(attempts) == 5
            row = dict(modulus=modulus, arm=arm, process_wall_ms=spread(a['process_wall_ns']/1e6 for a in attempts),
                f4_call_ms=spread(a['raw']['f4_call_ns']/1e6 for a in attempts),
                cpu_seconds=spread(a['cpu_seconds'] for a in attempts),
                rss_mib=spread(max(a['observed_peak_rss_bytes'], a['raw']['peak_rss_bytes'] or 0)/1024**2 for a in attempts))
            if arm.startswith(('dynamic-', 'static-')):
                schedule, workers, counters = arm.split('-')
                workers = int(workers)
                baseline = statistics.median(a['process_wall_ns'] for a in groups[(modulus, 'stock')])
                serial = statistics.median(a['process_wall_ns'] for a in groups[(modulus, schedule+'-1-'+counters)])
                wall = row['process_wall_ms']['median'] * 1e6
                row.update(stock_speedup=baseline/wall, same_algorithm_speedup=serial/wall,
                           efficiency=serial/wall/workers,
                           forward_ms=spread(sum(b['forward_ns'] for b in a['raw']['parallel']['batches'])/1e6 for a in attempts),
                           backward_ms=spread(sum(b['backward_ns'] for b in a['raw']['parallel']['batches'])/1e6 for a in attempts),
                           products=spread(sum(b['products'] for b in a['raw']['parallel']['batches']) for a in attempts),
                           retries=spread(sum(b['retries'] for b in a['raw']['parallel']['batches']) for a in attempts),
                           retry_products=spread(sum(b['retry_products'] for b in a['raw']['parallel']['batches']) for a in attempts),
                           workspace_bytes=max(b['workspace_bytes'] for a in attempts for b in a['raw']['parallel']['batches']),
                           reservation_entries=max(b['peak_reserved_entries'] for a in attempts for b in a['raw']['parallel']['batches']),
                           fallbacks=sum(a['raw']['parallel']['fallbacks'] for a in attempts))
            rows.append(row)
        summary.update(parallel_commit=parallel['commit'], parallel=rows)
        write_csv('parallel.csv', [dict(modulus=r['modulus'], arm=r['arm'], wall_ms=r['process_wall_ms']['median'],
            wall_min_ms=r['process_wall_ms']['minimum'], wall_max_ms=r['process_wall_ms']['maximum'],
            rss_mib=r['rss_mib']['median'], cpu_seconds=r['cpu_seconds']['median'],
            stock_speedup=r.get('stock_speedup', ''), same_algorithm_speedup=r.get('same_algorithm_speedup', ''),
            efficiency=r.get('efficiency', '')) for r in rows])
        batch_rows = []
        for (modulus, arm, index), batches in sorted(batch_groups.items()):
            schedule, workers, counters = arm.split('-')
            serial = batch_groups[(modulus, schedule+'-1-'+counters, index)]
            wall = statistics.median(b['forward_ns'] for b in batches)
            speedup = statistics.median(b['forward_ns'] for b in serial)/wall
            batch_rows.append(dict(modulus=modulus, arm=arm, batch=index, rows=batches[0]['rows'], columns=batches[0]['columns'],
                active_workers=len(batches[0]['worker_rows']), forward_ms=wall/1e6, speedup=speedup, efficiency=speedup/int(workers)))
        write_csv('matrix-scaling.csv', batch_rows)
        dispatch = []
        for workers in driver.WORKERS:
            attempts = [a for a in parallel['dispatch'] if a['workers'] == workers]
            assert len(attempts) == 5 and all(a['exit'] == 0 and a['stop'] is None for a in attempts)
            reports = [json.loads(a['stdout']) for a in attempts]
            assert all(report['workers'] == workers and len(report['samples_ns']) == 16 for report in reports)
            samples = [n/1000 for report in reports for n in report['samples_ns']]
            dispatch.append(dict(workers=workers, **spread(samples)))
        summary['scoped_dispatch_us'] = dispatch
        write_csv('dispatch.csv', dispatch)
    controls_path = HERE / 'controls.json.gz'
    if controls_path.exists():
        controls = storage.load_study(controls_path)
        assert len(controls['attempts']) == 300 and 'refusal' not in controls
        classical = tool('row-merge-study').references()
        groups = defaultdict(list)
        for attempt in controls['attempts']:
            assert attempt['status'] == 'verified'
            name, modulus = attempt['problem'], attempt['modulus']
            reference = classical[(name, modulus)] if name == 'cyclic-5' else controls['references'][f'{name}/{modulus}']
            if name != 'cyclic-5':
                assert '@match 1\n' in reference['singular']['stdout'] and reference['singular']['exit'] == 0
            check(attempt['raw'], reference)
            groups[(name, modulus, attempt['schedule'], attempt['workers'])].append(attempt)
        rows = []
        for (name, modulus, schedule, workers), attempts in sorted(groups.items()):
            assert len(attempts) == 5
            baseline = statistics.median(a['raw']['f4_call_ns'] for a in groups[(name, modulus, 'serial', 1)])
            process_baseline = statistics.median(a['process_wall_ns'] for a in groups[(name, modulus, 'serial', 1)])
            duration = spread(a['raw']['f4_call_ns']/1e6 for a in attempts)
            rows.append(dict(problem=name, modulus=modulus, schedule=schedule, workers=workers,
                f4_ms=duration['median'], f4_min_ms=duration['minimum'], f4_max_ms=duration['maximum'],
                serial_speedup=baseline/(duration['median']*1e6),
                process_serial_speedup=process_baseline/statistics.median(a['process_wall_ns'] for a in attempts),
                cpu_seconds=statistics.median(a['cpu_seconds'] for a in attempts),
                process_wall_ms=statistics.median(a['process_wall_ns']/1e6 for a in attempts),
                rss_mib=statistics.median(max(a['observed_peak_rss_bytes'], a['raw']['peak_rss_bytes'] or 0)/1024**2 for a in attempts)))
        assert len(controls['probes']) == 4
        summary.update(controls=rows, probes=[{key: probe[key] for key in (
            'problem', 'modulus', 'digest', 'schedule', 'workers', 'status', 'exit', 'stop',
            'process_wall_ns', 'observed_peak_rss_bytes', 'stderr')} for probe in controls['probes']])
        write_csv('controls.csv', rows)
    (HERE / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')


if __name__ == '__main__':
    main()
