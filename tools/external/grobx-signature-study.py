#!/usr/bin/env python3
"""#716 signature attribution: grobx default, signatures off, and signatures without handover.

Every attempt is a fresh direct-driver process under the existing tree watchdog. Work counts come
from grobx's own per-round report (the same `subtracted` charges M29-C1 used), so no observer is
switched on in timed runs. Answers are checked coefficient for coefficient against the retained
Singular-verified MQ10 references or the multi-engine-agreed wide-corpus answers.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

import importlib.util

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'research/m30-signature'


def sibling(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), Path(__file__).with_name(name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


BASE = sibling('grobx-work-study')
WIDE = sibling('wide-corpus')
TRAJECTORY = sibling('grobx-trajectory')
STORAGE = sibling('study_artifacts')

# Order is the plan's (§6.1): the two gate instances first, then MQ10, then the held-out pair.
CASES = {
    'mq11-goldilocks': {'wide': ('goldilocks', 'mq-random-11')},
    'eco12-wide64': {'wide': ('wide64', 'eco-12'), 'crossed': True},
    'mq10-32003': {'mq10': 32003},
    'mq10-m31': {'mq10': 2147483647, 'crossed': True},
    'katsura11-goldilocks': {'wide': ('goldilocks', 'katsura-11'), 'held_out': True},
    'cyclic7-goldilocks': {'wide': ('goldilocks', 'cyclic-7'), 'held_out': True},
}
BASE_ARMS = {
    'stock': {},
    'default': {},
    'sig-off': {'research_signatures': False},
    'no-handover': {'research_handover': False},
}
CROSSED_ARMS = {name + '-nocomb': dict(options, research_policy='none')
                for name, options in BASE_ARMS.items() if name != 'stock'}
# Declared before the primary cohort from the retained pilot; the contract's 60 s / 2 GiB stands
# except where the pilot showed an arm needs more, which is itself reported as a result.
CAPS = {'default': (60, 2 * 1024**3)}


def arms(case):
    names = list(BASE_ARMS)
    if CASES[case].get('crossed'):
        names += list(CROSSED_ARMS)
    return names


def options(arm):
    return BASE_ARMS.get(arm, CROSSED_ARMS.get(arm))


def cap(case, arm):
    return CAPS.get((case, arm), CAPS['default'])


def plan(repeats, cases):
    """Fresh, rotated, alternately reversed order: no arm or case always runs first or warm."""
    result = []
    for repeat in range(repeats):
        order = cases[repeat % len(cases):] + cases[:repeat % len(cases)]
        for case in order if repeat % 2 == 0 else reversed(order):
            names = arms(case)
            names = names[repeat % len(names):] + names[:repeat % len(names)]
            for arm in names if repeat % 2 == 0 else reversed(names):
                result.append(dict(repeat=repeat, case=case, arm=arm))
    return result


def canonical_digest(basis, modulus, variables):
    polys = sorted(WIDE.canonical_polynomial(p, modulus, variables) for p in basis)
    return hashlib.sha256(json.dumps(polys).encode()).hexdigest()


def prepare(path):
    """Freeze each wide case's request and the canonical digest every agreeing engine returned."""
    cases = {(c['field'], c['name']): c for c in json.loads((ROOT / 'research/wide-corpus/cases.json').read_text())}
    wanted = {spec['wide']: key for key, spec in CASES.items() if 'wide' in spec}
    found = {key: [] for key in wanted.values()}
    for attempt in WIDE.load(ROOT / 'research/wide-corpus/campaign.json.gz')['attempts']:
        key = wanted.get((attempt['field'], attempt['name']))
        if key and WIDE.completed(attempt):
            found[key].append(attempt)
    refs = {}
    for (field, name), key in wanted.items():
        c = cases[(field, name)]
        attempts = found[key]
        WIDE.verify_bases(attempts)
        engines = sorted({a['engine'] for a in attempts})
        if len([e for e in engines if e != 'grobx']) < 2:
            raise ValueError(f'{key}: fewer than two independent agreeing engines')
        r = attempts[0]['report']
        digests = {canonical_digest(a['report']['basis'], int(c['modulus']), c['variables']) for a in attempts}
        if len(digests) != 1:
            raise ValueError(f'{key}: agreeing bases canonicalize differently')
        refs[key] = dict(field=field, name=name, digest=c['digest'], modulus=int(c['modulus']),
                         variables=c['variables'], generators=c['generators'],
                         canonical_basis_sha256=digests.pop(), elements=len(r['basis']),
                         agreeing_engines=engines)
    path.write_text(json.dumps(refs, indent=2, sort_keys=True) + '\n')


def request_for(case, refs, mq10):
    spec = CASES[case]
    if 'mq10' in spec:
        return dict(mq10[spec['mq10']]['request'])
    r = refs[case]
    return dict(variables=r['variables'], modulus=r['modulus'], order='grevlex', workers=1,
                generators=r['generators'], mode='raw')


def verify(case, raw, request, refs, mq10, seen):
    if raw.get('stopped') is not None or raw.get('flaw') is not None:
        raise ValueError('driver stopped or rejected the result')
    if raw.get('input') != request:
        raise ValueError('driver input echo differs from request')
    spec = CASES[case]
    if 'mq10' in spec:
        BASE.validate_driver(raw, mq10[spec['mq10']], request)
        return 'every coefficient matches the independently Singular-verified full basis'
    text = hashlib.sha256(raw['basis'].encode()).hexdigest()
    echoes = hashlib.sha256(json.dumps([raw.get('generator_echoes'), raw.get('input_sha256')]).encode()).hexdigest()
    if (case, text) not in seen:
        # The full parse canonicalizes every polynomial; byte-identical answers reuse its verdict.
        if WIDE.validate_native(raw, request, 'grobx') is None:
            raise ValueError('stopped')
        r = refs[case]
        digest = canonical_digest(BASE.basis_list(raw['basis']), r['modulus'], r['variables'])
        if digest != r['canonical_basis_sha256']:
            raise ValueError('full reduced basis differs from the agreed reference')
        seen[(case, text)] = echoes
    elif seen[(case, text)] != echoes or raw.get('generator_echoes') != raw.get('checker_echoes') \
            or hashlib.sha256(raw.get('input_text', '').encode()).hexdigest() != raw.get('input_sha256'):
        raise ValueError('input echo differs from the verified attempt with the same answer')
    return 'every coefficient matches the complete basis agreed by ' + ', '.join(refs[case]['agreeing_engines'])


def expected_route(raw, request, trajectory):
    signatures = request.get('research_signatures', True)
    handover = request.get('research_handover', True)
    runs = trajectory['runs']
    if 'research_policy' in raw:
        policy = request.get('research_policy', 'native')
        if raw['research_policy'] != {'plain': policy not in ('no-plain', 'none'),
                                      'signature_tests': policy not in ('no-signature', 'none'),
                                      'validate': False, 'signatures': signatures, 'seed': 0}:
            raise ValueError('executed research policy differs')
        if raw['research_signature']['handover'] != handover:
            raise ValueError('executed handover switch differs')
    if not signatures:
        if [r['config']['engine'] for r in runs] != ['plain']:
            raise ValueError('signatures-off ran a signature engine')
    elif not handover:
        if len(runs) != 1 or runs[0]['config']['engine'] != 'signature' or runs[0]['config'].get('handover') != 'off':
            raise ValueError('handover-off run handed over or was not a signature run')
    elif runs[0]['config']['engine'] != 'signature':
        raise ValueError('default did not start with signatures')


def ledger(trajectory):
    """Per-run and whole-call counters, keeping discarded signature rounds separate."""
    runs = []
    for run in trajectory['runs']:
        rounds = run['rounds']
        s = run['summary']
        runs.append(dict(
            engine=run['config']['engine'], reduce=run['config']['reduce'], outcome=s['outcome'],
            rounds=len(rounds), reductions=s['reduced'], zero_reductions=s['zero'],
            zero_rows=sum(r.get('zero-rows', 0) for r in rounds),
            rounds_without_zero_rows=sum('zero-rows' not in r for r in rounds), rows=sum(r['rows'] for r in rounds),
            given=sum(r['given'] for r in rounds), pivots=sum(r['pivots'] for r in rounds),
            entries=sum(r['entries'] for r in rounds),
            max_rows=max((r['rows'] for r in rounds), default=0),
            max_columns=max((r['columns'] for r in rounds), default=0),
            round_subtracted=sum(r['subtracted'] for r in rounds),
            echelon_subtracted=run.get('echelon', {}).get('subtracted', 0),
            inter_subtracted=run.get('inter', {}).get('subtracted', 0),
            pair_decisions={k: s[k] for k in ('considered', 'equal', 'high', 'low', 'syzygy', 'koszul', 'queued') if k in s},
            stage_seconds={k: sum(r['stages_seconds'][k] for r in rounds) for k in TRAJECTORY.STAGES},
            run_seconds=s.get('time')))
    total = sum(r['round_subtracted'] + r['echelon_subtracted'] + r['inter_subtracted'] for r in runs)
    discarded = sum(r['round_subtracted'] + r['echelon_subtracted'] for r in runs if r['outcome'] == 'handover')
    return dict(runs=runs, subtracted_total=total, subtracted_discarded=discarded)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare', action='store_true', help='freeze wide references, then exit')
    for name in ('grobx-stock', 'grobx-research', 'scratch', 'output'):
        parser.add_argument('--' + name, type=Path)
    parser.add_argument('--cohort', choices=('pilot', 'primary'), default='primary')
    parser.add_argument('--cases', default=','.join(CASES))
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--max-load', type=float, default=8)
    args = parser.parse_args()
    refs_path = OUT / 'references.json'
    if args.prepare:
        prepare(refs_path)
        return
    if args.cohort == 'primary' and args.repeats < 5:
        parser.error('the primary cohort needs at least five repetitions per arm')
    if args.cohort == 'pilot' and args.repeats != 1:
        parser.error('the pilot is one attempt per arm')
    cases = args.cases.split(',')
    if any(c not in CASES for c in cases):
        parser.error('unknown case')
    affinity = ','.join(map(str, sorted(os.sched_getaffinity(0))))
    if not os.environ.get('ZEEBRA_MACHINE') or os.environ.get('ZEEBRA_AFFINITY') != affinity:
        parser.error('set ZEEBRA_MACHINE and the exact inherited ZEEBRA_AFFINITY; run under benchlock')
    if not args.scratch or str(args.scratch.resolve()).startswith(str(Path.home())):
        parser.error('--scratch must be on /buildcache')
    if subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=ROOT, text=True).strip():
        parser.error('commit the experimental sources before measuring')
    refs = json.loads(refs_path.read_text())
    mq10 = BASE.references(ROOT / 'research/competitive/results/grobx-683.json.gz')
    binaries = {'stock': args.grobx_stock.resolve(), 'research': args.grobx_research.resolve()}
    identities = {key: {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                        'version': json.loads(subprocess.check_output([str(path), '--version'], text=True))}
                  for key, path in binaries.items()}
    args.scratch.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    cohort = {'schema': 1, 'issue': 716, 'cohort': args.cohort, 'attempt_plan': plan(args.repeats, cases),
              'attempts': [], 'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'rustc': subprocess.check_output(['rustc', '-vV'], text=True),
              'cpu': next(line.split(':', 1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')),
              'machine': os.environ['ZEEBRA_MACHINE'], 'affinity': affinity, 'workers': 1, 'seed': 0,
              'build': 'release;fat LTO;one codegen unit;x86-64-v3;upstream grobx allocator',
              'caps': {f'{k[0]}/{k[1]}' if isinstance(k, tuple) else k: v for k, v in CAPS.items()},
              'max_load': args.max_load, 'binaries': identities,
              'references_sha256': hashlib.sha256(refs_path.read_bytes()).hexdigest(),
              'timing_boundary': 'fresh process spawn to reap, full answer encoding included; verification afterwards, outside the timed process'}
    seen = {}
    for item in cohort['attempt_plan']:
        load = os.getloadavg()[0]
        if load > args.max_load:
            cohort['refusal'] = dict(reason='ambient-load', value=load, next=item)
            BASE.write(args.output, cohort)
            raise RuntimeError('load gate exceeded; partial cohort retained')
        case, arm = item['case'], item['arm']
        key = 'stock' if arm == 'stock' else 'research'
        wall, rss = cap(case, arm)
        request = request_for(case, refs, mq10)
        request.update(options(arm))
        request.update(wall_ns=wall * 10**9, rss_bytes=rss, workers=1)
        stem = args.scratch / f'{args.cohort}-{len(cohort["attempts"])}'
        request_path = stem.with_suffix('.input.json')
        request_path.write_text(json.dumps(request))
        result = BASE.guarded([str(binaries[key]), str(request_path)], stem, wall, rss)
        result.update(item, request=request, binary=key, wall_cap_s=wall, rss_cap_bytes=rss,
                      load_before=load, load_after=os.getloadavg()[0], status='failed')
        try:
            if result['stop'] is not None:
                result['status'] = 'resource-limited'
                raise ValueError(f'watchdog stop: {result["stop"]}')
            if result['exit'] != 0:
                raise ValueError('process failed')
            raw = json.loads(result['stdout'])
            result['raw'] = raw
            if raw.get('stopped') is not None:
                result['status'] = 'resource-limited'
                raise ValueError('engine stop: ' + str(raw['stopped']))
            version = identities[key]['version']
            if raw['build'] != version['build'] or raw['revision'] != version['revision']:
                raise ValueError('driver identity changed after probing')
            result['peak_rss_bytes'] = max(result['observed_peak_rss_bytes'], raw.get('kernel_peak_rss_bytes') or 0)
            trajectory = TRAJECTORY.parse_report(raw['report'])
            expected_route(raw, request, trajectory)
            result['ledger'] = ledger(trajectory)
            result['plain_pairs'] = raw.get('research_signature', {}).get('plain_pairs')
            result['solve_ns'] = raw.get('solve_ns')
            result['basis_text_sha256'] = hashlib.sha256(raw['basis'].encode()).hexdigest()
            result['verification'] = verify(case, raw, request, refs, mq10, seen)
            result['status'] = 'verified'
        except (ValueError, KeyError, TypeError) as error:
            result['failure'] = str(error)
        # Every returned answer is kept, deduplicated by content, whatever the verdict.
        if result.get('raw') is not None and isinstance(result['raw'].get('basis'), str):
            result = STORAGE.pack_attempt(result, args.output, keys=('basis',))
        cohort['attempts'].append(result)
        BASE.write(args.output, cohort)
        print(len(cohort['attempts']) - 1, case, arm, result['status'],
              round(result['process_wall_ns'] / 1e6, 1), 'ms', flush=True)


if __name__ == '__main__':
    main()
