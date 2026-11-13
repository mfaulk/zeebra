#!/usr/bin/env python3
import argparse
from collections import defaultdict
import hashlib
import importlib.util
import json
from pathlib import Path
from statistics import median

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WORKERS = (1, 2, 4, 8, 16, 32, 64)


def load_module(path):
    spec = importlib.util.spec_from_file_location(path.stem.replace('-', '_'), path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def ceiling(total, backward, workers):
    if total <= 0 or not 0 <= backward < total or (workers is not None and workers < 1):
        raise ValueError('invalid elapsed boundary or worker count')
    return total / (total - backward + (backward / workers if workers else 0))


def reservation(resident, output_bound, columns, workers):
    if min(resident, output_bound, columns) < 0 or workers < 1:
        raise ValueError('invalid reservation dimensions')
    return resident + output_bound + workers * columns


def workspace(columns, field_bytes, workers):
    if columns < 0 or field_bytes < 1 or workers < 1:
        raise ValueError('invalid workspace dimensions')
    return columns * (workers * field_bytes + 8 + 1)


def spread(values):
    values = list(values)
    return dict(median=median(values), minimum=min(values), maximum=max(values))


def dispatch_rows(rows):
    result = [row for row in rows if row['phase'] == 'floor' and row['backend'] == 'parked'
              and row['case'] == ['0'] and row['workers'] in WORKERS]
    if sorted(row['workers'] for row in result) != list(WORKERS):
        raise ValueError('missing or duplicate empty-job dispatch cells')
    return sorted(result, key=lambda row: row['workers'])


def census(batches):
    if not batches:
        raise ValueError('empty work census')
    rows = []
    for index, batch in enumerate(batches):
        if not batch['completed'] or batch['columns'] < 1:
            raise ValueError('incomplete work batch')
        work = batch['backward']
        fields = ('rows_loaded', 'coefficient_products', 'pivot_applications', 'dense_load_entries', 'dense_gather_entries')
        if (any(work[key] < 0 for key in fields)
                or not 0 <= work['rows_loaded'] <= batch['rank'] <= batch['columns']
                or work['coefficient_products'] < work['pivot_applications']):
            raise ValueError('inconsistent backward work counts')
        rows.append(dict(batch=index, columns=batch['columns'], rank=batch['rank'],
                         targets=work['rows_loaded'], products=work['coefficient_products'],
                         applications=work['pivot_applications'], loads=work['dense_load_entries'],
                         gathers=work['dense_gather_entries'],
                         source_fanout_upper_bound=work['rows_loaded']))
    products = sum(row['products'] for row in rows)
    return dict(targets=sum(row['targets'] for row in rows), products=products,
                applications=sum(row['applications'] for row in rows),
                largest_batch_product_fraction=max(row['products'] for row in rows) / products if products else 0,
                batches=rows)


def summarize():
    storage = load_module(ROOT / 'tools/external/study_artifacts.py')
    driver = load_module(ROOT / 'tools/external/selective-backward-study.py')
    selective = load_module(ROOT / 'research/selective-backward/summarize.py')
    adoption = load_module(ROOT / 'research/candidate-adoption/summary.py')
    refs = driver.references()
    native = selective.validate_cohort(storage.load_study(ROOT / 'research/selective-backward/native.json.gz'), 'native', refs)
    work = selective.validate_cohort(storage.load_study(ROOT / 'research/selective-backward/work.json.gz'), 'work', refs)
    phases = ('adoption', 'adoption-work', 'adoption-off')
    current = {phase: storage.load_study(ROOT / 'research/candidate-adoption' / (phase + '.json.gz')) for phase in phases}
    adoption.summarize(current, refs)
    groups = defaultdict(list)
    for attempt in native['attempts']:
        if attempt['arm'] != 'dense-selected':
            continue
        raw = attempt['raw']
        backward = sum(batch['backward_ns'] for batch in raw['backward']['batches'])
        groups[(attempt['problem'], attempt['modulus'])].append((raw['f4_call_ns'], backward))
    timing = []
    for (problem, modulus), samples in sorted(groups.items()):
        timing.append(dict(problem=problem, modulus=modulus,
                           f4_ms=spread(total / 1e6 for total, _ in samples),
                           backward_ms=spread(backward / 1e6 for _, backward in samples),
                           backward_fraction=spread(backward / total for total, backward in samples),
                           ideal_unbounded_speedup=spread(ceiling(total, backward, None) for total, backward in samples),
                           ideal_speedup={str(p): spread(ceiling(total, backward, p) for total, backward in samples) for p in WORKERS}))
    production = []
    for modulus in (32003, 2147483647):
        attempts = [a for a in current['adoption-work']['attempts'] if a['arm'] == 'production-on' and a['modulus'] == modulus]
        counts = [census(a['raw']['work']['batches']) for a in attempts]
        if len(counts) != 5 or any(count != counts[0] for count in counts):
            raise ValueError('production census differs across repetitions')
        historical = [census(a['raw']['work']['batches']) for a in work['attempts'] if a['arm'] == 'dense-selected-on' and a['modulus'] == modulus]
        if len(historical) != 5 or any(count != counts[0] for count in historical):
            raise ValueError('historical and production backward batch work differ')
        stats = attempts[0]['raw']['statistics']['candidate_reduction']
        if counts[0]['products'] != stats['coefficient_products'] or counts[0]['targets'] != stats['targets'] or stats['fallback_batches']:
            raise ValueError('production census contradicts its output contract')
        production.append(dict(modulus=modulus, **counts[0]))
    # The worker-pool validator recomputes dispatch medians from its retained complete cohort.
    worker = load_module(ROOT / 'tools/external/worker-pool-study.py')
    import gzip
    cohort = json.loads(gzip.decompress((ROOT / 'research/worker-pool/results.json.gz').read_bytes()))
    dispatch = dispatch_rows(worker.summarize(cohort))
    source_paths = ['research/selective-backward/native.json.gz', 'research/selective-backward/work.json.gz',
                    'research/worker-pool/results.json.gz'] + ['research/candidate-adoption/' + phase + '.json.gz' for phase in phases]
    return dict(schema=1, interpretation='historical same-attempt elapsed ceilings; production count reconciliation, not production backward timing',
                source_archives={path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in source_paths},
                historical_source=native['identity'], production_source=current['adoption-work']['identity'],
                worker_pool_source=cohort['source'], timing=timing, production=production,
                dispatch=dispatch,
                workspace_model_bytes={str(size): {str(p): workspace(12020, size, p) for p in WORKERS} for size in (4, 8, 32)})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    encoded = json.dumps(summarize(), indent=2) + '\n'
    destination = HERE / 'summary.json'
    if args.check:
        if destination.read_text() != encoded:
            raise ValueError('retained residual model differs')
    else:
        destination.write_text(encoded)
    print('verified historical timer ceilings and five matching production work censuses per prime')


if __name__ == '__main__':
    main()
