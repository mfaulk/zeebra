#!/usr/bin/env python3
"""Verify the forward/backward crossing independently of the earlier serial cohort."""
from collections import defaultdict
import importlib.util
import json
from pathlib import Path
from statistics import median

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
spec = importlib.util.spec_from_file_location('cross', HERE/'cross.py')
cross = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cross)


def spread(values):
    values = list(values)
    return dict(median=median(values), minimum=min(values), maximum=max(values))


def validate(cohort, phase, refs):
    expected = list(cross.plan(phase))
    observed = [(a['repeat'], a['problem'], a['modulus'], a['arm']) for a in cohort['attempts']]
    if expected != observed or 'refusal' in cohort or not cohort['identity'].get('compiler_gate'):
        raise ValueError('incomplete or ungated combined cohort')
    trajectories = {}
    matrix_digests = {}
    for a in cohort['attempts']:
        if a.get('compiler_before') or a.get('compiler_after'):
            raise ValueError('compiler activity in combined cohort')
        if phase == 'probe':
            if a['status'] not in ('incomplete-unverified', 'completed-needs-independent-reference'):
                raise ValueError('unexpected probe classification')
            if a['status'] == 'completed-needs-independent-reference':
                raw = a['raw']
                expected_digest = {32003: '4e440cfac84262260736a2368f43c7a96181986ca5bc108517299520d56f8795',
                    2147483647: '029def705543e29b9f0648d3fa21a87be32358b79c3e64bb6dd222fa432c439d'}[a['modulus']]
                if raw['digest'] != expected_digest or raw['problem'] != 'mq-random-14' or len(raw['input']['variables']) != 14:
                    raise ValueError('probe input identity differs')
            continue
        if a['status'] != 'verified' or a['exit'] or a['stop']:
            raise ValueError('nonverified combined answer')
        raw = a['raw']
        if raw['f4_call_ns'] <= 0 or raw['peak_rss_bytes'] <= 0 or a['process_wall_ns'] < raw['f4_call_ns']:
            raise ValueError('invalid time or RSS')
        cross.validate(raw, refs[(a['problem'], a['modulus'])], a['arm'], a['problem'])
        key = (a['problem'], a['modulus'])
        trajectories.setdefault(key, raw)
        cross.driver.check_trajectory(raw, trajectories[key])
        if phase == 'work' and not raw['work']:
            raise ValueError('work diagnostic has no counters')
        if phase == 'work' and raw['parallel']:
            batches = raw['parallel']['batches']
            if len(batches) != len(raw['work']['batches']):
                raise ValueError('worker/passive batch counts differ')
            for index, (batch, passive) in enumerate(zip(batches, raw['work']['batches'])):
                if batch['products'] != batch['work']['coefficient_products']:
                    raise ValueError('worker products disagree with passive counters')
                if sum(batch['worker_rows']) != batch['rows'] - batch['split']:
                    raise ValueError('worker row aggregation is incomplete')
                key = (a['modulus'], index)
                digest = batch['input_matrix_digest']
                matrix_digests.setdefault(key, digest)
                if not digest or digest != matrix_digests[key]:
                    raise ValueError('combined input matrix drift')
                if batch['backward_details'] and batch['backward_details']['products'] != passive['backward']['coefficient_products']:
                    raise ValueError('combined direct/passive backward counts differ')
    return cohort


def main():
    storage = cross.driver.load('study_artifacts')
    refs = cross.driver.references()
    cohorts = {phase: validate(storage.load_study(HERE/name), phase, refs)
        for phase, name in [('native', 'cross-native.json.gz'), ('work', 'cross-work.json.gz'), ('probe', 'probes.json.gz')]}
    groups = defaultdict(list)
    for a in cohorts['native']['attempts']:
        groups[(a['problem'], a['modulus'], a['arm'])].append(a)
    rows = []
    for (problem, modulus, arm), attempts in sorted(groups.items()):
        raw = [a['raw'] for a in attempts]
        row = dict(problem=problem, modulus=modulus, arm=arm,
            f4_ms=spread(r['f4_call_ns']/1e6 for r in raw),
            process_ms=spread(a['process_wall_ns']/1e6 for a in attempts),
            cpu_ms=spread(a['cpu_seconds']*1000 for a in attempts),
            self_peak_mib=max(r['peak_rss_bytes'] for r in raw)/1024**2,
            tree_peak_mib=max(a['observed_peak_rss_bytes'] for a in attempts)/1024**2,
            load=spread(a['load'] for a in attempts),
            stages_ms={k: spread(r['statistics'][k]/1e6 for r in raw) for k in (
                'symbolic_ns', 'construction_ns', 'elimination_ns', 'extraction_ns', 'interreduction_ns', 'other_ns')})
        for direction in ('forward', 'backward'):
            row[direction+'_ms'] = spread(sum(b[direction+'_ns'] for b in (r['parallel'] or r['backward'])['batches'])/1e6 for r in raw)
        rows.append(row)
    work = []
    for a in cohorts['work']['attempts']:
        r = a['raw']
        backward = {key: sum(b['backward'][key] for b in r['work']['batches'])
                    for key in r['work']['batches'][0]['backward']}
        row = dict(modulus=a['modulus'], arm=a['arm'], backward=backward)
        if r['parallel']:
            row['forward_products'] = sum(b['products'] for b in r['parallel']['batches'])
            row['forward_retry_products'] = sum(b['retry_products'] for b in r['parallel']['batches'])
            row['worker_rows'] = [b['worker_rows'] for b in r['parallel']['batches']]
            row['workspace_bytes'] = max(b['workspace_bytes'] for b in r['parallel']['batches'])
            row['peak_reserved_entries'] = max(b['peak_reserved_entries'] for b in r['parallel']['batches'])
            for b, passive in zip(r['parallel']['batches'], r['work']['batches']):
                if b['backward_details'] and b['backward_details']['products'] != passive['backward']['coefficient_products']:
                    raise ValueError('combined direct/passive backward counts differ')
        else:
            row['forward_products'] = sum(b['forward']['coefficient_products'] for b in r['work']['batches'])
        work.append(row)
    probes = []
    for a in cohorts['probe']['attempts']:
        reason = a['stop'] or ('solver-refusal' if a['exit'] else 'completed-unverified')
        requested_digest = {32003: '4e440cfac84262260736a2368f43c7a96181986ca5bc108517299520d56f8795',
            2147483647: '029def705543e29b9f0648d3fa21a87be32358b79c3e64bb6dd222fa432c439d'}[a['modulus']]
        probes.append(dict(modulus=a['modulus'], arm=a['arm'], status=a['status'], reason=reason,
            requested_digest=requested_digest,
            exit=a['exit'], process_wall_seconds=a['process_wall_ns']/1e9,
            observed_peak_mib=a['observed_peak_rss_bytes']/1024**2, stderr=a['stderr']))
    summary = dict(identities={p: c['identity'] for p,c in cohorts.items()},
        accepted_native_attempts=len(cohorts['native']['attempts']), work_attempts=len(work), native=rows, work=work, probes=probes)
    (HERE/'combined-summary.json').write_text(json.dumps(summary, indent=2)+'\n')


if __name__ == '__main__': main()
