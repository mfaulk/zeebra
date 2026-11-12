#!/usr/bin/env python3
"""Freeze source-bound executables and retain every guarded matrix attempt."""
import argparse
import gzip
import hashlib
import importlib.util
import itertools
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('rowmerge', ROOT / 'tools/external/row-merge-study.py')
rowmerge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rowmerge)
IDENTITY = ('field', 'shape', 'eighths', 'source', 'input_hash', 'rref_hash', 'rows', 'columns',
            'initial_nonzeros', 'rank', 'zero_rows', 'peak_nonzeros', 'final_nonzeros',
            'row_operations', 'entry_allowance')
BINARIES = (*rowmerge.BINARIES, 'elimination_kernel_study')
EVENTS = ('cycles:u', 'instructions:u', 'ls_any_fills_from_sys.mem_io_local:u',
          'ls_any_fills_from_sys.mem_io_remote:u')
PATCH = ROOT / 'research/elimination-kernels/delayed.patch'


def curve_cells():
    return itertools.product(('m31', 'p64', 'bn254'), ('k7', 'c6', 'k6lex'), (1, 2, 4, 8),
                             ('sparse', 'dense', 'adaptive'))


def check_matrix(report, reference):
    for key in IDENTITY:
        if report[key] != reference[key]:
            raise ValueError('matrix identity/work differs: ' + key)


def check_rss(report):
    if not isinstance(report.get('peak_rss_bytes'), int) or report['peak_rss_bytes'] <= 0:
        raise ValueError('process RSS is missing or zero')


def freeze(target, destination):
    # The only permitted dirty source state is this exact isolated research overlay.
    changes = subprocess.check_output(['git', 'diff', '--binary'], cwd=ROOT)
    expected = PATCH.read_bytes()
    if changes not in (b'', expected):
        raise ValueError('commit the instrument; only the exact delayed.patch overlay may be dirty')
    if subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'], cwd=ROOT).strip():
        raise ValueError('commit all instrument sources before freezing')
    destination.mkdir(parents=True, exist_ok=False)
    digests = {}
    for name in BINARIES:
        path = target / 'release/examples' / name
        shutil.copy2(path, destination / name)
        digests[name] = rowmerge.sha(path)
    metadata = dict(commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                    rustc=subprocess.check_output(['rustc', '-vV'], text=True), binaries=digests,
                    overlay_sha256=hashlib.sha256(changes).hexdigest() if changes else None,
                    build='cargo build --release; repository config; fat LTO; codegen-units=1')
    (destination / 'build.json').write_text(json.dumps(metadata, indent=2)+'\n')


def read_events(raw):
    result = {}
    for line in raw.splitlines():
        parts = line.split(';')
        if len(parts) < 5 or parts[2] not in EVENTS:
            continue
        value, running = int(parts[0]), float(parts[4])
        if value < 0 or not 99 <= running <= 100:
            raise ValueError('negative or multiplexed counter')
        result[parts[2]] = value
    if set(result) != set(EVENTS) or result['cycles:u'] <= 0 or result['instructions:u'] <= 0:
        raise ValueError('incomplete hardware evidence')
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--freeze', type=Path)
    parser.add_argument('--target', type=Path)
    parser.add_argument('--baseline', type=Path)
    parser.add_argument('--candidate', type=Path)
    parser.add_argument('--phase', choices=('curves', 'arithmetic', 'pilot', 'region'), default='curves')
    parser.add_argument('--perf', type=Path)
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--scratch', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.freeze:
        if args.target is None:
            parser.error('--freeze requires --target')
        freeze(args.target, args.freeze)
        return
    if not all((args.baseline, args.scratch, args.output)) or args.repeats < 1:
        parser.error('baseline, scratch, output and positive repeats required')
    if args.phase == 'pilot' and not args.candidate:
        parser.error('pilot requires candidate')
    if args.phase == 'region' and not args.perf:
        parser.error('region requires --perf')
    affinity = ','.join(map(str, sorted(os.sched_getaffinity(0))))
    if not os.environ.get('ZEEBRA_MACHINE') or os.environ.get('ZEEBRA_AFFINITY') != affinity:
        parser.error('run under benchlock with ZEEBRA_MACHINE and actual ZEEBRA_AFFINITY')
    builds = {}
    for arm in ('baseline', 'candidate') if args.phase == 'pilot' else ('baseline',):
        directory = getattr(args, arm)
        builds[arm] = json.loads((directory/'build.json').read_text())
        for name, digest in builds[arm]['binaries'].items():
            rowmerge.check_binary(directory/name, digest)
    args.scratch.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    cohort = dict(schema=1, phase=args.phase, machine=os.environ['ZEEBRA_MACHINE'], affinity=affinity,
                  runner_commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                  perf_version=subprocess.check_output([str(args.perf), '--version'], text=True).strip() if args.perf else None,
                  builds=builds, policy='fresh process/cell; alternating arms/backends; 185s/2GiB tree guard', attempts=[])
    references, sources, failures = {}, {}, 0
    for repeat in range(args.repeats):
        if args.phase == 'curves':
            cells = list(curve_cells())
            if repeat % 2:
                cells.reverse()
        elif args.phase == 'pilot':
            cells = [('p15', shape, 8, 'adaptive') for shape in ('k7', 'c6', 'k6lex')]
        elif args.phase == 'region':
            cells = [('p31', 'mq10', 8, 'adaptive')]
        else:
            cells = [('--arithmetic',)]
        for cell in cells:
            arms = ('baseline', 'candidate') if args.phase == 'pilot' else ('baseline',)
            if repeat % 2:
                arms = arms[::-1]
            for arm in arms:
                command = [str(getattr(args, arm)/'elimination_kernel_study'), *map(str, cell)]
                stem = args.scratch/str(len(cohort['attempts']))
                if args.phase == 'region':
                    ctl, ack = stem.with_suffix('.ctl'), stem.with_suffix('.ack')
                    os.mkfifo(ctl)
                    os.mkfifo(ack)
                    command = [str(args.perf), 'stat', '--delay=-1', '--control', f'fifo:{ctl},{ack}',
                               '--no-big-num', '-x', ';', '-e', ','.join(EVENTS), '-o', str(stem.with_suffix('.perf')),
                               '--', 'env', f'ZEEBRA_PERF_CTL={ctl}', f'ZEEBRA_PERF_ACK={ack}', *command]
                result = rowmerge.attempt(command, stem)
                if args.phase == 'region':
                    result['perf_stat'] = stem.with_suffix('.perf').read_text() if stem.with_suffix('.perf').exists() else ''
                    ctl.unlink()
                    ack.unlink()
                result.update(repeat=repeat, cell=cell, arm=arm)
                try:
                    if result['exit'] or result['stop'] or 'report' not in result:
                        raise ValueError('guarded process failed')
                    report = result['report']
                    check_rss(report)
                    if args.phase == 'region':
                        if report.get('counter_scope') != 'elimination-region':
                            raise ValueError('hardware counters include capture')
                        result['events'] = read_events(result['perf_stat'])
                    if args.phase != 'arithmetic':
                        key = tuple(cell[:3])
                        references.setdefault(key, report)
                        check_matrix(report, references[key])
                        source_key = tuple(cell[:2])
                        sources.setdefault(source_key, report['source'])
                        if report['source'] != sources[source_key]:
                            raise ValueError('source changed across density masks')
                    result['verification'] = 'exact-match'
                except (KeyError, ValueError) as error:
                    result['verification'] = str(error)
                    failures += 1
                cohort['attempts'].append(result)
                rowmerge.write(args.output, cohort)
                print(repeat, cell, arm, result['verification'], flush=True)
    if failures:
        raise SystemExit(f'{failures} failed attempts retained')


if __name__ == '__main__':
    main()
