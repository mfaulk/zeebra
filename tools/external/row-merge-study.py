#!/usr/bin/env python3
"""Alternate frozen native builds; retain failures and assert complete arithmetic identities."""
import argparse
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
BINARIES = ('row_merge_study', 'public_corpus', 'mq10_profile')
MATRICES = ('katsura-7/grevlex/m31/default', 'cyclic-6/grevlex/m31/default',
            'katsura-6/lex/m31/baseline', 'katsura-7/grevlex/p64/default',
            'cyclic-6/grevlex/p64/default', 'katsura-6/lex/p64/baseline',
            'katsura-6/grevlex/bn254/default', 'cyclic-5/grevlex/bn254/baseline')
MQ = 'mq-random-10/grevlex/p31x64/default'
spec = importlib.util.spec_from_file_location('guard', ROOT / 'tools/external/mq10-profile.py')
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_answer(report, reference):
    if report.get('status') not in ('complete', 'verified'):
        raise ValueError('solver did not complete')
    for key in ('digest', 'modulus'):
        if report[key] != reference[key]:
            raise ValueError('input identity differs: ' + key)
    if sorted(report['basis']) != sorted(reference['basis']):
        raise ValueError('complete reduced basis differs')


def check_matrix(report, reference):
    for key in ('fingerprint', 'rank', 'rref_hash'):
        if report[key] != reference[key]:
            raise ValueError('matrix differs: ' + key)


def check_binary(path, digest):
    if sha(path) != digest:
        raise ValueError('executable differs from frozen build: ' + str(path))


def snapshot(args):
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        raise ValueError('commit the instrument before snapshotting a build')
    args.snapshot.mkdir(parents=True, exist_ok=False)
    binaries = {}
    for name in BINARIES:
        source = args.target / 'release/examples' / name
        shutil.copy2(source, args.snapshot / name)
        binaries[name] = sha(source)
    metadata = dict(commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                    rustc=subprocess.check_output(['rustc', '-vV'], text=True), binaries=binaries,
                    build='cargo build --release; fat LTO; codegen-units=1; x86-64-v3; system allocator')
    (args.snapshot / 'build.json').write_text(json.dumps(metadata, indent=2) + '\n')


def references():
    rows = {}
    for name in ('grobx-683', 'grobx-683-small'):
        with gzip.open(ROOT / f'research/competitive/results/{name}.json.gz', 'rt') as stream:
            for attempt in json.load(stream)['attempts']:
                row = attempt['rows'][0]
                if row['library'] == 'grobx' and row['outcome'] == 'verified':
                    key = (row['problem'], row['field']['characteristic'])
                    rows[key] = attempt['artifacts']
    return rows


def cells(phase):
    if phase in ('all', 'solves'):
        for name in ('public-eco-4', 'public-noon-3', 'public-reimer-3',
                     'public-eco-8', 'public-noon-6', 'public-reimer-5'):
            yield name, 'public_corpus', ['--row', name, '--engine', 'zeebra'], None
        for p in (32003, 2147483647):
            yield f'mq10/{p}', 'mq10_profile', [str(p), '--stages'], ('mq-random-10', p)
            for name in ('cyclic-5', 'katsura-4'):
                yield f'{name}/{p}', 'row_merge_study', ['--mode', 'solve', '--row', name, '--modulus', str(p)], (name, p)
    if phase in ('all', 'matrices'):
        for label in MATRICES:
            for backend in ('sparse', 'dense', 'adaptive'):
                yield label + '/' + backend, 'row_merge_study', ['--matrix', label, '--backend', backend], None
        yield MQ + '/adaptive', 'row_merge_study', ['--matrix', MQ, '--backend', 'adaptive'], None
    if phase in ('all', 'work'):
        for label in (MQ, MATRICES[0], MATRICES[3], MATRICES[6]):
            yield label + '/work', 'row_merge_study', ['--matrix', label, '--mode', 'work'], None


def attempt(command, stem):
    started, peak, stop = time.monotonic_ns(), 0, None
    with stem.with_suffix('.stdout').open('w') as out, stem.with_suffix('.stderr').open('w') as err:
        process = subprocess.Popen(command, stdout=out, stderr=err, start_new_session=True)
        while process.poll() is None:
            peak = max(peak, guard.tree_hwm(process.pid))
            if peak > 2 * 1024**3 or time.monotonic_ns() - started > 185_000_000_000:
                stop = 'rss' if peak > 2 * 1024**3 else 'wall'
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                break
            time.sleep(0.002)
    result = dict(exit=process.returncode, stop=stop, process_wall_ns=time.monotonic_ns()-started,
                  observed_tree_peak_bytes=peak, stderr=stem.with_suffix('.stderr').read_text())
    raw = stem.with_suffix('.stdout').read_text()
    try:
        result['report'] = json.loads(raw)
    except ValueError:
        result['stdout'] = raw
    return result


def write(path, data):
    temp = path.with_suffix('.tmp')
    temp.write_bytes(gzip.compress(json.dumps(data, separators=(',', ':')).encode(), mtime=0))
    temp.replace(path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--snapshot', type=Path, help='freeze binaries built from this clean checkout, then exit')
    parser.add_argument('--target', type=Path, help='private CARGO_TARGET_DIR used by the completed release build')
    parser.add_argument('--baseline', type=Path)
    parser.add_argument('--candidate', type=Path)
    parser.add_argument('--phase', choices=('all', 'solves', 'matrices', 'work'), default='all')
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--scratch', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.snapshot:
        if not args.target:
            parser.error('--snapshot requires --target')
        snapshot(args)
        return
    if not all((args.baseline, args.candidate, args.scratch, args.output)) or args.repeats < 1:
        parser.error('measurement requires baseline, candidate, scratch, output and positive repeats')
    affinity = ','.join(str(c) for c in sorted(os.sched_getaffinity(0)))
    if not os.environ.get('ZEEBRA_MACHINE') or os.environ.get('ZEEBRA_AFFINITY') != affinity:
        parser.error('set ZEEBRA_MACHINE and explicit actual ZEEBRA_AFFINITY; run under benchlock')
    builds = {}
    for arm in ('baseline', 'candidate'):
        directory = getattr(args, arm)
        builds[arm] = json.loads((directory / 'build.json').read_text())
        for name, digest in builds[arm]['binaries'].items():
            check_binary(directory / name, digest)
    refs, matrices, public = references(), {}, {}
    args.scratch.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    cohort = dict(schema=1, builds=builds, machine=os.environ['ZEEBRA_MACHINE'], affinity=affinity,
                  workers=1, phase=args.phase, policy='fresh process/cell; alternating arms; 185s/2GiB tree guard; retain every failure',
                  runner_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(), attempts=[])
    failures = 0
    for repeat in range(args.repeats):
        for label, binary, arguments, refkey in cells(args.phase):
            for arm in (('baseline', 'candidate') if repeat % 2 == 0 else ('candidate', 'baseline')):
                result = attempt([str(getattr(args, arm) / binary), *arguments], args.scratch / str(len(cohort['attempts'])))
                result.update(repeat=repeat, label=label, arm=arm, binary=binary)
                try:
                    if result['exit'] or result['stop'] or 'report' not in result:
                        raise ValueError('guarded process failed')
                    report = result['report']
                    if refkey:
                        check_answer(report, refs[refkey])
                    elif binary == 'public_corpus':
                        if report['status'] != 'verified':
                            raise ValueError('public full-reference check failed')
                        public.setdefault(label, report)
                        check_answer(report, public[label])
                    else:
                        key = report['label']
                        matrices.setdefault(key, report)
                        check_matrix(report, matrices[key])
                    result['verification'] = 'complete-basis-or-RREF-match'
                except (ValueError, KeyError) as error:
                    result['verification'] = str(error)
                    failures += 1
                cohort['attempts'].append(result)
                write(args.output, cohort)
                print(repeat, label, arm, result['verification'], flush=True)
    if failures:
        raise SystemExit(f'{failures} failed attempts retained')


if __name__ == '__main__':
    main()
