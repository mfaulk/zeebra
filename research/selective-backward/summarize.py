#!/usr/bin/env python3
"""Recheck complete native/work cohorts and regenerate the selective-backward tables."""
from collections import defaultdict
import csv
import hashlib
import importlib.util
import json
from pathlib import Path
from statistics import median

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def tool(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT/'tools/external'/(name+'.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def spread(values):
    values = list(values)
    return dict(median=median(values), minimum=min(values), maximum=max(values))


def validate_cohort(cohort, phase, refs):
    study = tool('selective-backward-study')
    expected = list(study.plan(phase))
    if not cohort['identity'].get('compiler_gate'):
        raise ValueError('accepted cohort lacks compiler gates')
    observed = [(a['repeat'], a['problem'], a['modulus'], a['arm']) for a in cohort['attempts']]
    if observed != expected or 'refusal' in cohort:
        raise ValueError('incomplete, repeated or reordered campaign cells')
    trajectories = {}
    digests, forwards = {}, {}
    for a in cohort['attempts']:
        if a['status'] != 'verified' or a['exit'] != 0 or a['stop'] is not None:
            raise ValueError('nonverified attempt in accepted cohort')
        if a.get('compiler_before') or a.get('compiler_after'):
            raise ValueError('ambient compiler in accepted attempt')
        raw = a['raw']
        if raw['f4_call_ns'] <= 0 or a['process_wall_ns'] < raw['f4_call_ns'] or raw['peak_rss_bytes'] <= 0:
            raise ValueError('missing or invalid time/RSS evidence')
        mode = a['arm'].removesuffix('-on').removesuffix('-off')
        study.validate(raw, refs[(a['problem'], a['modulus'])], mode, a['problem'])
        key = (a['problem'], a['modulus'])
        trajectories.setdefault(key, raw)
        study.check_trajectory(raw, trajectories[key])
        if phase == 'work' and a['arm'].endswith('-on'):
            batches = raw['work']['batches']
            observed_batches = raw['backward']['batches']
            if len(batches) != len(observed_batches) or not batches:
                raise ValueError('work and observer batch counts differ')
            for index, (batch, observed) in enumerate(zip(batches, observed_batches)):
                key = (a['modulus'], index)
                digest = observed['input_matrix_digest']
                if not digest:
                    raise ValueError('work matrix identity absent')
                digests.setdefault(key, digest)
                forwards.setdefault(key, batch['forward'])
                if digests[key] != digest or forwards[key] != batch['forward']:
                    raise ValueError('forward matrix or work drift')
                if observed['details'] is not None:
                    if observed['details']['products'] != batch['backward']['coefficient_products']:
                        raise ValueError('direct products disagree with passive counters')
    return cohort


def main():
    if (HERE/'inventory.json').exists():
        inventory = json.loads((HERE/'inventory.json').read_text())
        if any(hashlib.sha256((HERE/p).read_bytes()).hexdigest() != digest for p, digest in inventory.items()):
            raise ValueError('retained artifact differs from SHA256 inventory')
    storage, driver = tool('study_artifacts'), tool('selective-backward-study')
    refs = driver.references()
    cohorts = {phase: validate_cohort(storage.load_study(HERE/(phase+'.json.gz')), phase, refs)
               for phase in ('native', 'work')}
    native, work = [], []
    for phase, cohort in cohorts.items():
        groups = defaultdict(list)
        for attempt in cohort['attempts']:
            groups[(attempt['problem'], attempt['modulus'], attempt['arm'])].append(attempt)
        for (problem, modulus, arm), attempts in sorted(groups.items()):
            raw = [a['raw'] for a in attempts]
            row = dict(problem=problem, modulus=modulus, arm=arm,
                f4_ms=spread(r['f4_call_ns']/1e6 for r in raw),
                process_ms=spread(a['process_wall_ns']/1e6 for a in attempts),
                self_peak_mib=max(r['peak_rss_bytes'] for r in raw)/1024**2,
                tree_peak_mib=max(a['observed_peak_rss_bytes'] for a in attempts)/1024**2,
                cpu_ms=spread(a['cpu_seconds']*1000 for a in attempts),
                load=spread(a['load'] for a in attempts),
                stages_ms={k: spread(r['statistics'][k]/1e6 for r in raw) for k in
                    ('symbolic_ns', 'construction_ns', 'elimination_ns', 'extraction_ns', 'interreduction_ns', 'other_ns')})
            if phase == 'native':
                native.append(row)
            else:
                work.append(row)
                if arm.endswith('-on'):
                    totals = [{direction: {name: sum(b[direction][name] for b in r['work']['batches'])
                        for name in r['work']['batches'][0][direction]} for direction in ('forward', 'backward')} for r in raw]
                    if any(t != totals[0] for t in totals):
                        raise ValueError('work changed across repeats')
                    row['totals'] = totals[0]
                    details = [b['details'] for b in raw[0]['backward']['batches'] if b['details'] is not None]
                    if details:
                        row['targets'] = sum(d['targets'] for d in details)
                        row['workspace_bytes'] = max(d['workspace_bytes'] for d in details)
                        row['peak_entries'] = max(d['peak_entries'] for d in details)
                        row['peak_sparse_capacity_entries'] = max(d['peak_capacity_entries'] for d in details)
                        row['kernel_allocations'] = sum(2 + d['targets'] for d in details)
    summary = dict(source=cohorts['native']['identity'], native_attempts=len(cohorts['native']['attempts']),
        work_attempts=len(cohorts['work']['attempts']), native=native, work=work)
    (HERE/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    with (HERE/'native.csv').open('w') as stream:
        writer = csv.DictWriter(stream, fieldnames=['problem', 'modulus', 'arm', 'f4_median_ms', 'f4_min_ms',
            'f4_max_ms', 'process_median_ms', 'self_peak_mib', 'tree_peak_mib'], lineterminator='\n')
        writer.writeheader()
        for row in native:
            writer.writerow(dict(problem=row['problem'], modulus=row['modulus'], arm=row['arm'],
                f4_median_ms=row['f4_ms']['median'], f4_min_ms=row['f4_ms']['minimum'],
                f4_max_ms=row['f4_ms']['maximum'], process_median_ms=row['process_ms']['median'],
                self_peak_mib=row['self_peak_mib'], tree_peak_mib=row['tree_peak_mib']))
    paths = sorted(HERE.glob('*-proofs/*')) + [HERE/(p+'.json.gz') for p in ('native', 'work')]
    inventory = {str(p.relative_to(HERE)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    (HERE/'inventory.json').write_text(json.dumps(inventory, indent=2)+'\n')


if __name__ == '__main__':
    main()
