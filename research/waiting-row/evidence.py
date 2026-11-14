#!/usr/bin/env python3
from collections import defaultdict
import hashlib
import json
from pathlib import Path
from statistics import median
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/external'))
from study_artifacts import load_study


def diagnostic(batches):
    for batch in batches:
        counts = [batch[key] for key in ('products', 'inherited_products', 'discovered_products',
                  'rows', 'split')]
        counts += batch['worker_rows'] + batch['worker_ns']
        counts += [batch.get(key, 0) for key in ('retry_products', 'retries', 'scheduling_ns',
                   'publication_ns', 'peak_reserved_entries', 'workspace_bytes')]
        if any(not isinstance(value, int) or value < 0 for value in counts):
            raise ValueError('invalid observation counter')
        if batch.get('retry_products', 0) > batch['products']:
            raise ValueError('invalid post-loss subset')
        if (batch['products'] != batch['inherited_products'] + batch['discovered_products']
                or sum(batch['worker_rows']) != batch['rows'] - batch['split']
                or len(batch['worker_rows']) != len(batch['worker_ns'])):
            raise ValueError('inconsistent product or worker aggregation')
    dominant = max(batches, key=lambda b: b['products'])
    clocks = dominant['worker_ns']
    products = sum(b['products'] for b in batches)
    if products <= 0 or not clocks or max(clocks) <= 0:
        raise ValueError('missing work observations')
    post_loss = sum(b['retry_products'] for b in batches)
    if not 0 <= post_loss <= products:
        raise ValueError('invalid post-loss subset')
    return dict(products=products, lost_publications=sum(b['retries'] for b in batches),
                post_loss_products=post_loss, post_loss_product_fraction=post_loss/products,
                scheduling_worker_sum_ns=sum(b['scheduling_ns'] for b in batches),
                publication_worker_sum_ns=sum(b['publication_ns'] for b in batches),
                dominant_batch=dominant.get('batch_index'),
                worker_duration_balance=sum(clocks)/(len(clocks)*max(clocks)),
                peak_reserved_entries=max(b['peak_reserved_entries'] for b in batches),
                workspace_bytes=max(b['workspace_bytes'] for b in batches))


def timing(wall_ns, batches):
    forward = sum(b['forward_ns'] for b in batches)
    if wall_ns <= 0 or not 0 <= forward < wall_ns:
        raise ValueError('invalid same-attempt timer boundary')
    return dict(process_ms=wall_ns/1e6, forward_ms=forward/1e6,
                remove_all_forward_ceiling=wall_ns/(wall_ns-forward),
                required_forward_saving_for_10pct=.1*wall_ns/forward if forward else None)


def spread(rows):
    result = {}
    for key in rows[0]:
        values = [row[key] for row in rows]
        if key != 'dominant_batch' and all(value is not None for value in values):
            result[key] = dict(median=median(values), minimum=min(values), maximum=max(values))
    return result


def main():
    sources = [('concurrent', 'research/concurrent-pivots/parallel.json.gz'),
               ('selected-work', 'research/selective-backward/cross-work.json.gz'),
               ('selected-native', 'research/selective-backward/cross-native.json.gz')]
    result = dict(sources=[], diagnostics=[], timing=[])
    for name, path in sources:
        cohort = load_study(ROOT/path)
        expected_count = {'concurrent': 310, 'selected-work': 12, 'selected-native': 140}[name]
        if len(cohort['attempts']) != expected_count:
            raise ValueError('unexpected cohort size')
        if 'refusal' in cohort:
            raise ValueError('incomplete cohort')
        result['sources'].append(dict(name=name, path=path,
            sha256=hashlib.sha256((ROOT/path).read_bytes()).hexdigest(),
            source=cohort.get('identity', {}).get('binary_source_commit', cohort.get('commit')),
            attempts=len(cohort['attempts'])))
        grouped = defaultdict(list)
        for a in cohort['attempts']:
            if a['status'] != 'verified' or a['exit'] or a['stop']:
                raise ValueError('unverified or incomplete attempt')
            if not a['raw'].get('parallel'):
                continue
            arm = a['arm']
            if name == 'concurrent' and (not arm.endswith('-on') or arm.split('-')[1] not in ('1', '4', '16', '64')):
                continue
            if name != 'concurrent' and a['problem'] != 'mq-random-10':
                continue
            grouped[(a['modulus'], arm)].append(a)
        arms = ({f'{schedule}-{workers}-on' for schedule in ('dynamic', 'static')
                 for workers in (1, 4, 16, 64)} if name == 'concurrent' else
                {'one-full', 'one-selected', 'parallel-full', 'parallel-selected'})
        if set(grouped) != {(modulus, arm) for modulus in (32003, 2147483647) for arm in arms}:
            raise ValueError('incomplete cell coverage')
        for (modulus, arm), attempts in sorted(grouped.items()):
            expected = 1 if name == 'selected-work' else 5
            if len(attempts) != expected or {a['repeat'] for a in attempts} != set(range(expected)):
                raise ValueError('unexpected repetition coverage')
            batches = [a['raw']['parallel']['batches'] for a in attempts]
            rows = ([timing(a['process_wall_ns'], b) for a, b in zip(attempts, batches)]
                    if name == 'selected-native' else [diagnostic(b) for b in batches])
            result['timing' if name == 'selected-native' else 'diagnostics'].append(
                dict(cohort=name, modulus=modulus, arm=arm, repetitions=expected, **spread(rows)))
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
