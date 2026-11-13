#!/usr/bin/env python3
"""Validate retained production-adoption attempts without executing a solver."""
from collections import defaultdict
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
from statistics import median

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def tool(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT / 'tools/external' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def summarize(cohorts, refs):
    study = tool('selective-backward-study')
    result = dict(source={phase: c['identity'] for phase, c in cohorts.items()}, rows=[])
    for phase, cohort in cohorts.items():
        identity = cohort['identity']
        if (identity.get('phase') != phase or not identity.get('compiler_gate') or not identity.get('baseline_commit')
                or not identity.get('build_commit') or 'refusal' in cohort):
            raise ValueError('incomplete provenance or refused campaign')
        for name in ('stock','binary','production'):
            digest=identity.get('binaries',{}).get(name,{}).get('sha256','')
            if len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest):
                raise ValueError('missing executable identity')
        attempts = cohort['attempts']
        if [(a['repeat'], a['problem'], a['modulus'], a['arm']) for a in attempts] != list(study.plan(phase)):
            raise ValueError('incomplete, reordered or duplicate cells')
        trajectories, groups = {}, defaultdict(list)
        for a in attempts:
            raw = a['raw']
            if (a['status'] != 'verified' or a['exit'] != 0 or a['stop'] is not None
                    or a.get('compiler_before') or a.get('compiler_after')):
                raise ValueError('unverified or contaminated attempt')
            if (raw['f4_call_ns'] <= 0 or a['process_wall_ns'] < raw['f4_call_ns']
                    or raw['peak_rss_bytes'] <= 0 or a['observed_peak_rss_bytes'] <= 0):
                raise ValueError('missing or invalid timing/RSS')
            mode = a['arm'].removesuffix('-on').removesuffix('-off')
            if a['arm'] == 'feature-off':
                mode = 'production'
            key = (a['problem'], a['modulus'])
            study.validate(raw, refs[key], mode, a['problem'])
            trajectories.setdefault(key, raw)
            study.check_trajectory(raw, trajectories[key])
            if mode == 'production' and a['arm'].endswith('-on'):
                products = sum(b['backward']['coefficient_products'] for b in raw['work']['batches'])
                if products != raw['statistics']['candidate_reduction']['coefficient_products']:
                    raise ValueError('direct/passive products differ')
            groups[(a['problem'], a['modulus'], a['arm'])].append(a)
        for (problem, modulus, arm), attempts in sorted(groups.items()):
            raws = [a['raw'] for a in attempts]
            ms = [r['f4_call_ns'] / 1e6 for r in raws]
            row = dict(phase=phase, problem=problem, modulus=modulus, arm=arm,
                       f4_ms=dict(median=median(ms), minimum=min(ms), maximum=max(ms)),
                       process_ms=median(a['process_wall_ns'] / 1e6 for a in attempts),
                       cpu_ms=median(a['cpu_seconds'] * 1000 for a in attempts),
                       self_peak_mib=max(r['peak_rss_bytes'] for r in raws) / 1024**2,
                       tree_peak_mib=max(a['observed_peak_rss_bytes'] for a in attempts) / 1024**2,
                       stages_ms={key: (None if phase == 'adoption-off' else median(r['statistics'][key] / 1e6 for r in raws)) for key in
                                  ('symbolic_ns', 'construction_ns', 'elimination_ns', 'extraction_ns',
                                   'interreduction_ns', 'other_ns')})
            if arm in ('production', 'feature-off', 'production-on'):
                row['candidate_reduction'] = raws[0]['statistics']['candidate_reduction']
                if any(r['statistics']['candidate_reduction'] != row['candidate_reduction'] for r in raws):
                    raise ValueError('production work/reservation drift')
            if phase == 'adoption-work':
                row['work'] = {direction: sum(b[direction]['coefficient_products'] for b in raws[0]['work']['batches'])
                               for direction in ('forward', 'backward')}
            result['rows'].append(row)
    work_rows=[r for r in result['rows'] if r['phase']=='adoption-work']
    for row in work_rows:
        other=next(r for r in work_rows if r['problem']==row['problem'] and r['modulus']==row['modulus'] and r['arm']!=row['arm'])
        if row['work']['forward'] != other['work']['forward']:
            raise ValueError('forward work changed across backward policies')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    storage, driver = tool('study_artifacts'), tool('selective-backward-study')
    paths = sorted(HERE.rglob('*.gz')) + sorted(HERE.glob('*.log'))
    inventory = {str(p.relative_to(HERE)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    cohorts = {phase: storage.load_study(HERE / (phase + '.json.gz')) for phase in ('adoption', 'adoption-work', 'adoption-off')}
    result = summarize(cohorts, driver.references())
    for name, value in [('summary.json', result), ('inventory.json', inventory)]:
        encoded = json.dumps(value, indent=2) + '\n'
        if args.check:
            if (HERE / name).read_text() != encoded:
                raise ValueError('retained derived artifact differs: ' + name)
        else:
            (HERE / name).write_text(encoded)
    print('verified', sum(len(c['attempts']) for c in cohorts.values()), 'independent full bases')


if __name__ == '__main__':
    main()
