#!/usr/bin/env python3
"""Bounded MQ10 attribution using existing guards, input artifacts and fully verified bases."""
import argparse
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
MODULI = (32003, 2147483647)
DIGESTS = {
    32003: '16422dafcdb6487ea541f976f7754112b811c85af2b3537ed10fe4ef9c8f3d7f',
    2147483647: '72d0ad315fc25409792625465578d18329597d3ee183e75f257774d9215803b2',
}


def sibling(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), Path(__file__).with_name(name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def basis_list(text):
    text = text.strip()
    if not text.endswith(':'):
        raise ValueError('truncated basis')
    text = text[:-1].strip()
    if not (text.startswith('[') and text.endswith(']')):
        raise ValueError('malformed basis')
    if not text[1:-1].strip():
        return []
    result = [p.strip() for p in text[1:-1].split(',')]
    if any(not p or any(c in p for c in '[]:') for p in result):
        raise ValueError('malformed polynomial list')
    return result


def validate_driver(raw, reference, request):
    if raw.get('stopped') is not None or raw.get('flaw') is not None:
        raise ValueError('driver stopped or rejected the result')
    if raw.get('input') != request:
        raise ValueError('driver input echo differs from request')
    for key in ('input_text', 'input_sha256', 'generator_echoes', 'checker_echoes'):
        if raw.get(key) != reference[key]:
            raise ValueError(f'driver {key} differs from verified input')
    basis = basis_list(raw['basis'])
    sibling('mq10-profile').check_answer(
        {'digest': reference['digest'], 'modulus': reference['modulus'], 'basis': basis}, reference)
    return basis


def structural(value):
    ignored = {'elapsed_seconds', 'stages_seconds', 'events',
               'process-rss-start', 'process-rss-peak', 'process-rss-grown'}
    clocks = {'select', 'symbolic', 'encode', 'reduce', 'backsub', 'record',
              'decode', 'update', 'read', 'time'}
    if isinstance(value, dict):
        return {k: structural(v) for k, v in value.items()
                if k not in ignored and not (k in clocks and isinstance(v, (int, float)))}
    if isinstance(value, list):
        return [structural(v) for v in value]
    return value


def references(path):
    with gzip.open(path, 'rt') as stream:
        cohort = json.load(stream)
    result = {}
    for attempt in cohort['attempts']:
        row = attempt['rows'][0]
        if (row['problem'], row['library'], row['outcome']) != ('mq-random-10', 'grobx', 'verified'):
            continue
        artifacts = attempt['artifacts']
        raw = json.loads(artifacts['raw_output'])
        modulus = artifacts['modulus']
        if artifacts['digest'] != DIGESTS[modulus] or row['problem_digest'] != DIGESTS[modulus]:
            raise ValueError('reference digest mismatch')
        ref = {k: artifacts[k] for k in ('digest', 'modulus', 'basis')}
        ref.update({k: raw[k] for k in ('input_text', 'input_sha256', 'generator_echoes', 'checker_echoes')})
        ref.update(request=raw['input'], verification=row['verification'])
        if hashlib.sha256(ref['input_text'].encode()).hexdigest() != ref['input_sha256']:
            raise ValueError('retained input text hash mismatch')
        validate_driver(raw, ref, ref['request'])
        if modulus in result and result[modulus] != ref:
            raise ValueError('retained verified references disagree')
        result[modulus] = ref
    if set(result) != set(MODULI):
        raise ValueError('missing independently verified reference')
    return result


def guarded(command, stem, wall, rss, env=None):
    guard = sibling('mq10-profile')
    started = time.monotonic_ns()
    peak, stop = 0, None
    with stem.with_suffix('.stdout').open('w') as stdout, stem.with_suffix('.stderr').open('w') as stderr:
        process = subprocess.Popen(command, stdout=stdout, stderr=stderr, start_new_session=True, env=env)
        try:
            while process.poll() is None:
                peak = max(peak, guard.tree_hwm(process.pid))
                if peak > rss or time.monotonic_ns() - started > wall * 1e9:
                    stop = 'rss' if peak > rss else 'wall'
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                    break
                time.sleep(.002)
        finally:
            if process.poll() is None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
    return {'command': command, 'process_wall_ns': time.monotonic_ns() - started,
            'observed_peak_rss_bytes': peak, 'stop': stop, 'exit': process.returncode,
            'stdout': stem.with_suffix('.stdout').read_text(),
            'stderr': stem.with_suffix('.stderr').read_text()}


def write(path, cohort):
    path.write_bytes(gzip.compress((json.dumps(cohort, indent=2) + '\n').encode(), mtime=0))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ('zeebra-stock', 'zeebra-work', 'grobx-stock', 'grobx-work', 'scratch', 'output'):
        parser.add_argument('--' + flag, required=True, type=Path)
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--max-load', type=float, default=4.0)
    args = parser.parse_args()
    affinity = ','.join(map(str, sorted(os.sched_getaffinity(0))))
    if not os.environ.get('ZEEBRA_MACHINE') or os.environ.get('ZEEBRA_AFFINITY') != affinity:
        parser.error('set machine and exact actual affinity, and launch under benchlock')
    if args.repeats < 1:
        parser.error('positive repetitions required')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        parser.error('commit the instrument before measuring')
    refs = references(ROOT / 'research/competitive/results/grobx-683.json.gz')
    report_parser = sibling('grobx-trajectory')
    args.scratch.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    binaries = {k: getattr(args, k.replace('-', '_')).resolve()
                for k in ('zeebra-stock', 'zeebra-work', 'grobx-stock', 'grobx-work')}
    identity = {}
    for key, binary in binaries.items():
        identity[key] = {'path': str(binary), 'sha256': hashlib.sha256(binary.read_bytes()).hexdigest()}
        if key.startswith('grobx'):
            version = subprocess.check_output([str(binary), '--version'], text=True)
            identity[key]['version'] = json.loads(version)
    cohort = {
        'schema': 1, 'issue': 713, 'repetitions': args.repeats,
        'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'rustc': subprocess.check_output(['rustc', '-vV'], text=True),
        'cpu': next(l.split(':', 1)[1].strip() for l in Path('/proc/cpuinfo').read_text().splitlines() if l.startswith('model name')),
        'machine': os.environ['ZEEBRA_MACHINE'], 'affinity': affinity, 'workers': 1,
        'build': 'release;fat LTO;codegen-units=1;x86-64-v3;RUSTC_WRAPPER=;system allocator Zeebra;upstream allocator grobx',
        'limits': {'wall_seconds': 60, 'rss_bytes': 2 * 1024**3, 'historical_nested_parent_watchdog_seconds': 185},
        'guard_boundary': 'existing descendant-RSS observation; direct solver child killed at 60s/2GiB, with no profiler or nested verifier in timed group; tighter than historical 185s outer watchdog',
        'reference_cohort_sha256': hashlib.sha256((ROOT / 'research/competitive/results/grobx-683.json.gz').read_bytes()).hexdigest(),
        'binaries': identity, 'attempts': [],
        'timing_boundary': 'fresh process spawn to reap including input parsing/generation and full basis JSON encoding; verification afterwards; no cross-engine stage/wall ratios',
    }
    paths = {}
    arms = ('zeebra-stock', 'grobx-stock', 'zeebra-off', 'grobx-off', 'zeebra-on', 'grobx-on')
    for repeat in range(args.repeats):
        for modulus in MODULI:
            for arm in (arms if repeat % 2 == 0 else tuple(reversed(arms))):
                load = os.getloadavg()[0]
                if load > args.max_load:
                    cohort['refusal'] = {'reason': 'ambient-load', 'load': load, 'limit': args.max_load,
                                         'next': [repeat, modulus, arm]}
                    write(args.output, cohort)
                    raise RuntimeError('ambient load exceeds declared gate; partial cohort retained')
                index = len(cohort['attempts'])
                stem = args.scratch / str(index)
                key = arm if arm.endswith('stock') else arm.rsplit('-', 1)[0] + '-work'
                command = [str(binaries[key])]
                request = dict(refs[modulus]['request'])
                if arm.startswith('zeebra'):
                    command += [str(modulus), '--stages'] + (['--work'] if arm.endswith('on') else [])
                else:
                    if not arm.endswith('stock'):
                        request['research_work'] = arm.endswith('on')
                    stem.with_suffix('.input.json').write_text(json.dumps(request))
                    command.append(str(stem.with_suffix('.input.json')))
                result = guarded(command, stem, 60, 2 * 1024**3)
                result.update(repeat=repeat, modulus=modulus, digest=DIGESTS[modulus], arm=arm,
                              load_before=load, load_after=os.getloadavg()[0], status='failed')
                try:
                    if result['exit'] != 0 or result['stop'] is not None:
                        raise ValueError('process failed or stopped')
                    raw = json.loads(result['stdout'])
                    result['raw'] = raw
                    peak = max(result['observed_peak_rss_bytes'], raw.get('kernel_peak_rss_bytes') or raw.get('peak_rss_bytes') or 0)
                    result['peak_rss_bytes'] = peak
                    if not peak or peak > 2 * 1024**3:
                        result['stop'] = 'rss' if peak else 'rss-unavailable'
                        raise ValueError('missing or over-budget process RSS')
                    if arm.startswith('zeebra'):
                        sibling('mq10-profile').check_answer(raw, refs[modulus])
                        path = {k: v for k, v in raw['statistics'].items() if not k.endswith('_ns') and k != 'full_statistics'}
                    else:
                        validate_driver(raw, refs[modulus], request)
                        result['trajectory'] = report_parser.parse_report(raw['report'])
                        path = structural(result['trajectory'])
                        version = identity[key]['version']
                        if raw['build'] != version['build'] or raw['revision'] != version['revision']:
                            raise ValueError('driver build changed after probing')
                    engine = arm.split('-')[0]
                    control = paths.setdefault((engine, modulus), path)
                    if path != control:
                        raise ValueError('passive observation changed structural trajectory')
                    if arm.endswith('on') and raw.get('work') is None:
                        raise ValueError('requested work counters absent')
                    if not arm.endswith('on') and raw.get('work') is not None:
                        raise ValueError('disabled work counters unexpectedly present')
                    result.update(status='verified', verification='full-basis-match-to-retained-independent-Singular-reference')
                except (ValueError, KeyError, TypeError) as error:
                    result['failure'] = str(error)
                cohort['attempts'].append(result)
                write(args.output, cohort)
                print(index, arm, modulus, result['status'], round(result['process_wall_ns']/1e6, 2), 'ms', flush=True)
    if any(a['status'] != 'verified' for a in cohort['attempts']):
        raise RuntimeError('failed attempts retained; do not publish as clean timing evidence')


if __name__ == '__main__':
    main()
