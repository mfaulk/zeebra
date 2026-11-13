#!/usr/bin/env python3
"""Bounded fresh-process GCD size observations, using the existing study process/RSS guard."""
import argparse
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
PHASES = ('prs_entries', 'raw_remainders', 'brown_images', 'brown_interpolants')
CASES = ((2, 0), (3, 3), (3, 6), (4, 3), (4, 4))
FIELDS = ('koalabear', 'goldilocks', 'bn254')
ROUTES = ('subresultant', 'primitive', 'brown')
ARMS = ('stock', 'off', 'on')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sibling(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), Path(__file__).with_name(name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate(raw, answers, case, observed):
    if digest(raw['input'].encode()) != raw['input_sha256']:
        raise ValueError('input digest mismatch')
    if raw['observed'] != observed:
        raise ValueError('observer setting changed')
    if raw['status'] == 'refused':
        if not raw.get('refusal'):
            raise ValueError('missing refusal reason')
        return
    if raw['status'] != 'completed' or not raw.get('gcd'):
        raise ValueError('missing complete GCD')
    answer = (raw['input_sha256'], raw['gcd'])
    if answers.setdefault(case, answer) != answer:
        raise ValueError('complete GCD differs across routes or observer modes')
    if not raw.get('peak_rss_bytes'):
        raise ValueError('missing process RSS')
    if observed:
        profile = raw.get('profile')
        if not isinstance(profile, dict):
            raise ValueError('missing size profile')
        if profile.get('subresultant_bound_violations') != 0:
            raise ValueError('local subresultant degree bound violated')
        for name in PHASES:
            for field in ('observations', 'max_terms', 'max_coefficient_degree'):
                value = profile[name][field]
                if type(value) is not int or value < 0:
                    raise ValueError('invalid size counter')
    elif raw.get('profile') is not None:
        raise ValueError('disabled profile unexpectedly present')


def write(path, cohort):
    path.write_bytes(gzip.compress((json.dumps(cohort, indent=2) + '\n').encode(), mtime=0))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stock', type=Path, required=True)
    parser.add_argument('--observed', type=Path, required=True)
    parser.add_argument('--scratch', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--max-load', type=float, default=4)
    parser.add_argument('--campaign-seconds', type=int, default=600)
    args = parser.parse_args()
    started = time.monotonic()
    if args.campaign_seconds < 1:
        parser.error('positive campaign ceiling required')
    affinity = ','.join(map(str, sorted(os.sched_getaffinity(0))))
    if not os.environ.get('ZEEBRA_MACHINE') or os.environ.get('ZEEBRA_AFFINITY') != affinity:
        parser.error('declare machine and inherited exact CPU affinity; run under benchlock')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        parser.error('commit the instrument before measuring')
    if args.output.exists():
        parser.error('output exists; never overwrite a retained attempt')
    args.scratch.mkdir(parents=True, exist_ok=False)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    binaries = {name: path.resolve() for name, path in [('stock', args.stock), ('observed', args.observed)]}
    cohort = {
        'issue': 652, 'schema': 1,
        'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'rustc': subprocess.check_output(['rustc', '-vV'], text=True),
        'lockfile_sha256': digest((ROOT / 'Cargo.lock').read_bytes()),
        'machine': os.environ['ZEEBRA_MACHINE'], 'affinity': affinity, 'workers': 1,
        'cpu': next(line.split(':', 1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines()
                    if line.startswith('model name')),
        'binaries': {name: {'path': str(path), 'sha256': digest(path.read_bytes())} for name, path in binaries.items()},
        'build': 'release;fat LTO;one codegen unit;x86-64-v3;RUSTC_WRAPPER=;stock default features;observed adds research-work',
        'limits': {'child_seconds': 10, 'child_rss_bytes': 512 * 1024**2, 'campaign_seconds': args.campaign_seconds,
                   'campaign_boundary': 'checked before each child; at most one bounded child plus artifact writing beyond ceiling'},
        'plan': {'fields': FIELDS, 'cases': CASES, 'routes': ROUTES, 'arms': ARMS, 'repetitions': 5,
                 'diagnostic': 'one bounded attempt per arm/route/field at omitted historical shape arity4,index6; no repeated timing claim'},
        'timing_boundary': 'child spawn-to-reap includes input generation, result checks and JSON; elapsed_ns excludes those but includes profile scans in on mode; no stage/wall quotients',
        'attempts': [],
    }
    answers = {}
    guard = sibling('grobx-work-study').guarded

    def attempt(field, arity, shape, route, arm, repeat, diagnostic=False):
        if time.monotonic() - started >= args.campaign_seconds:
            cohort['refusal'] = {'reason': 'campaign-wall', 'next': [field, arity, shape, route, arm, repeat]}
            write(args.output, cohort)
            raise RuntimeError('campaign ceiling reached; partial cohort retained')
        load = os.getloadavg()[0]
        if load > args.max_load:
            cohort['refusal'] = {'reason': 'ambient-load', 'observed': load, 'limit': args.max_load,
                                 'next': [field, arity, shape, route, arm, repeat]}
            write(args.output, cohort)
            raise RuntimeError('ambient load exceeded declared gate; partial cohort retained')
        binary = binaries['stock' if arm == 'stock' else 'observed']
        command = [str(binary), '--case', field, str(arity), str(shape), route, 'on' if arm == 'on' else 'off']
        result = guard(command, args.scratch / str(len(cohort['attempts'])), 10, 512 * 1024**2)
        result.update(field=field, arity=arity, shape=shape, route=route, arm=arm, repeat=repeat,
                      diagnostic=diagnostic, load_before=load, load_after=os.getloadavg()[0], status='failed')
        if result['exit'] == 0 and result['stop'] is None:
            try:
                raw = json.loads(result['stdout'])
                validate(raw, answers, (field, arity, shape), arm == 'on')
                result['raw'] = raw
                result['peak_rss_bytes'] = max(result['observed_peak_rss_bytes'], raw['peak_rss_bytes'])
                if result['peak_rss_bytes'] > 512 * 1024**2:
                    raise ValueError('reported RSS exceeds declared child cap')
                result['status'] = raw['status']
            except (ValueError, KeyError, TypeError) as error:
                result['failure'] = str(error)
        elif result['stop'] is not None:
            result['status'] = 'stopped'
        cohort['attempts'].append(result)
        write(args.output, cohort)
        print(len(cohort['attempts']), field, arity, shape, route, arm, result['status'], flush=True)

    for repeat in range(5):
        for field in FIELDS:
            for arity, shape in CASES:
                for route in ROUTES if repeat % 2 == 0 else tuple(reversed(ROUTES)):
                    for arm in ARMS if repeat % 2 == 0 else tuple(reversed(ARMS)):
                        attempt(field, arity, shape, route, arm, repeat)
    for field in FIELDS:
        for route in ROUTES:
            for arm in ARMS:
                attempt(field, 4, 6, route, arm, 0, diagnostic=True)
    cohort['completed_plan'] = True
    cohort['all_completed_answers_agree'] = not any(a['status'] == 'failed' for a in cohort['attempts'])
    write(args.output, cohort)
    if not cohort['all_completed_answers_agree']:
        raise RuntimeError('failed attempts retained; inspect all outcomes')


if __name__ == '__main__':
    main()
