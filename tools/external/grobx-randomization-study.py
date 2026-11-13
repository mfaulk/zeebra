#!/usr/bin/env python3
"""Isolated feature ablations using the existing MQ10 corpus, watchdog and answer checker."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

import importlib.util

ROOT = Path(__file__).resolve().parents[2]


def sibling(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), Path(__file__).with_name(name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


BASE = sibling('grobx-work-study')
MODULI = BASE.MODULI
ARMS = {
    'stock': {},
    'native-off': {'research_work': False},
    'native-on': {'research_work': True},
    'no-plain': {'research_work': True, 'research_policy': 'no-plain'},
    'no-signature': {'research_work': True, 'research_policy': 'no-signature'},
    'none': {'research_work': True, 'research_policy': 'none'},
    'plain-only': {'research_work': True, 'research_signatures': False},
    'plain-only-no-combinations': {'research_work': True, 'research_signatures': False, 'research_policy': 'no-plain'},
    'plain-only-validated': {'research_work': True, 'research_signatures': False, 'research_validate': True},
    'certified': {'research_work': True, 'mode': 'certified'},
}
# Every changed policy has a same-binary observer-off timing control.
for name, options in list(ARMS.items()):
    if options.get('research_work') is True and name != 'native-on':
        ARMS[name + '-off'] = dict(options, research_work=False)


def plan(repeats):
    result = []
    for repeat in range(repeats):
        for modulus in MODULI if repeat % 2 == 0 else reversed(MODULI):
            for arm in ARMS if repeat % 2 == 0 else reversed(ARMS):
                result.append(dict(cohort='primary', repeat=repeat, modulus=modulus, arm=arm, seed=0))
    for seed in (1, 2):
        for modulus in MODULI:
            for arm in ('native-on', 'plain-only', 'plain-only-no-combinations'):
                result.append(dict(cohort='sensitivity', repeat=0, modulus=modulus, arm=arm, seed=seed))
    return result


def validate_policy(raw, request):
    if 'research_work' not in request:
        return
    expected = {'plain': request.get('research_policy', 'native') not in ('no-plain', 'none'),
                'signature_tests': request.get('research_policy', 'native') not in ('no-signature', 'none'),
                'validate': request.get('research_validate', False),
                'signatures': request.get('research_signatures', True),
                'seed': request.get('research_seed', 0)}
    if raw.get('research_policy') != expected:
        raise ValueError('executed research policy differs from requested policy')
    if (raw.get('work') is not None) != request['research_work']:
        raise ValueError('work collection does not match request')
    if expected['validate']:
        checks = raw.get('research_audit')
        if not checks or any(check.get('valid') is not True for check in checks):
            raise ValueError('incomplete or failed residual validation')
    if request['mode'] == 'certified' and (raw.get('certified') is not True or raw.get('flaw') is not None):
        raise ValueError('exact checker did not admit the basis')


def validate_activation(raw, request, trajectory):
    plain = request.get('research_policy', 'native') not in ('no-plain', 'none')
    signature = request.get('research_policy', 'native') not in ('no-signature', 'none')
    for run in trajectory['runs']:
        config = run['config']
        tracked = config.get('cofactors') == 'on'
        if config['engine'] == 'signature':
            if not request.get('research_signatures', True):
                raise ValueError('signature engine unexpectedly activated')
            expected = 'tests' if signature and not tracked else 'rows'
        elif config['engine'] == 'plain':
            expected = 'combinations' if plain and not tracked and request['modulus'] >= 46341 else 'rows'
        else:
            raise ValueError('unexpected engine in experiment')
        if config['reduce'] != expected:
            raise ValueError('actual reduction mode differs from isolated policy')
    events = raw.get('research_events', [])
    if not plain and any(e['kind'] == 'plain-block' for e in events):
        raise ValueError('disabled plain combinations executed')
    if not signature and any(e['kind'] == 'signature-group' for e in events):
        raise ValueError('disabled signature tests executed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('grobx-stock', 'grobx-research', 'scratch', 'output'):
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--max-load', type=float, default=8)
    args = parser.parse_args()
    if args.repeats != 5:
        parser.error('the declared primary campaign requires exactly five repetitions')
    affinity = ','.join(map(str, sorted(os.sched_getaffinity(0))))
    if not os.environ.get('ZEEBRA_MACHINE') or os.environ.get('ZEEBRA_AFFINITY') != affinity:
        parser.error('set machine and exact inherited affinity; run under benchlock')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        parser.error('commit the experimental sources before measuring')
    refs = BASE.references(ROOT / 'research/competitive/results/grobx-683.json.gz')
    decoder = sibling('grobx-trajectory')
    storage = sibling('study_artifacts')
    binaries = {'stock': args.grobx_stock.resolve(), 'research': args.grobx_research.resolve()}
    identities = {key: {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                       'version': json.loads(subprocess.check_output([str(path), '--version'], text=True))}
                  for key, path in binaries.items()}
    args.scratch.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    cohort = {'schema': 1, 'issue': 714, 'attempt_plan': plan(args.repeats), 'attempts': [],
              'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'rustc': subprocess.check_output(['rustc', '-vV'], text=True),
              'cpu': next(line.split(':', 1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')),
              'machine': os.environ['ZEEBRA_MACHINE'], 'affinity': affinity, 'workers': 1,
              'build': 'release;fat LTO;one codegen unit;x86-64-v3;upstream grobx allocator',
              'limits': {'child_wall_seconds': 60, 'child_rss_bytes': 2 * 1024**3,
                         'outer_campaign_seconds': 1800, 'max_load': args.max_load},
              'reference_sha256': hashlib.sha256((ROOT / 'research/competitive/results/grobx-683.json.gz').read_bytes()).hexdigest(),
              'binaries': identities,
              'storage': 'lossless existing SHA256 response sidecars, packed after each attempt outside process timing',
              'campaign_extension': 'one full restart after an 18-attempt diagnostic cohort exposed certified-report decoding and large-certificate storage limitations; all initial outcomes retained separately; no additional extensions',
              'objective_note': 'Raw ablations share parameters except named flags. Certified mode is a separate changed-trajectory exact objective, not an isolated validation or randomization control.',
              'timing_boundary': 'fresh process spawn to reap, full output included; independent reference validation afterwards; native residual guard and certified checker charged inside their own process wall'}
    paths = {}
    for item in cohort['attempt_plan']:
        load = os.getloadavg()[0]
        if load > args.max_load:
            cohort['refusal'] = dict(reason='ambient-load', value=load, next=item)
            BASE.write(args.output, cohort)
            raise RuntimeError('load gate exceeded; partial campaign retained')
        key = 'stock' if item['arm'] == 'stock' else 'research'
        version = identities[key]['version']
        request = dict(refs[item['modulus']]['request'])
        request.update(ARMS[item['arm']])
        request.update(wall_ns=60000000000, rss_bytes=2 * 1024**3, workers=1)
        if item['seed']:
            request['research_seed'] = item['seed']
        stem = args.scratch / str(len(cohort['attempts']))
        request_path = stem.with_suffix('.input.json')
        request_path.write_text(json.dumps(request))
        result = BASE.guarded([str(binaries[key]), str(request_path)], stem, 60, 2 * 1024**3)
        result.update(item, digest=BASE.DIGESTS[item['modulus']], request=request,
                      load_before=load, load_after=os.getloadavg()[0], status='failed')
        try:
            if result['exit'] != 0 or result['stop'] is not None:
                raise ValueError('process failed or stopped')
            raw = json.loads(result['stdout'])
            result['raw'] = raw
            peak = max(result['observed_peak_rss_bytes'], raw.get('kernel_peak_rss_bytes') or 0)
            result['peak_rss_bytes'] = peak
            if not peak or peak > 2 * 1024**3:
                raise ValueError('unavailable or over-budget process RSS')
            if raw['build'] != version['build'] or raw['revision'] != version['revision']:
                raise ValueError('driver identity changed after probing')
            BASE.validate_driver(raw, refs[item['modulus']], request)
            validate_policy(raw, request)
            result['trajectory'] = decoder.parse_report(raw['report'])
            validate_activation(raw, request, result['trajectory'])
            shape = BASE.structural(result['trajectory'])
            comparison = 'native-control' if item['arm'] in ('stock', 'native-off', 'native-on') else item['arm'].removesuffix('-off')
            index = (item['modulus'], comparison, item['seed'])
            if shape != paths.setdefault(index, shape):
                raise ValueError('same seed/policy produced a different structural trajectory')
            result.update(status='verified', verification='every coefficient matches independently Singular-verified full basis')
        except (ValueError, KeyError, TypeError) as error:
            result['failure'] = str(error)
        if result.get('raw') is not None:
            result = storage.pack_attempt(result, args.output, keys=('cofactors', 'basis'))
        raw = None
        cohort['attempts'].append(result)
        BASE.write(args.output, cohort)
        print(len(cohort['attempts'])-1, item['arm'], item['modulus'], item['seed'], result['status'],
              round(result['process_wall_ns'] / 1e6, 2), 'ms', flush=True)
    if any(a['status'] != 'verified' for a in cohort['attempts']):
        raise RuntimeError('failed outcomes retained; campaign is not clean adoption evidence')


if __name__ == '__main__':
    main()
