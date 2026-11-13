"""Capture the predeclared bounded serial caller cohort; invoke under benchlock."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import time

CASES = [('koala64-small', 'koalabear', 6561, 0x4b0a, 8),
         ('koala64-large', 'koalabear', 1594323, 0x4b0a, 8),
         ('koala32-large', 'koalabear32', 1594323, 0x4b32, 4)]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def hard_limit():
    limit = 2 * 1024**3
    resource.setrlimit(resource.RLIMIT_AS, (limit, limit))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--scratch', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    output = root / 'raw'
    if output.exists():
        raise SystemExit('raw/ exists; preserve it and use a fresh checkout for reruns')
    output.mkdir()
    args.scratch.mkdir(parents=True, exist_ok=True)
    metadata = {'binary_sha256': digest(args.binary), 'binary': str(args.binary),
                'utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                'load': os.getloadavg(), 'affinity': sorted(os.sched_getaffinity(0)),
                'cases': [], 'sources': {}}
    commands = {'rustc': ['rustc', '-Vv'], 'cargo': ['cargo', '-V'],
                'topology': ['lscpu', '-e=CPU,CORE,SOCKET,NODE,CACHE'],
                'cpu': ['lscpu'], 'source': ['git', 'rev-parse', 'HEAD'],
                'flags': ['cat', '.cargo/config.toml'],
                'diff': ['git', 'diff', '--', 'examples/graeffe_root.rs']}
    for name, command in commands.items():
        metadata[name] = subprocess.check_output(command, text=True)
    paths = ['Cargo.toml', 'Cargo.lock', 'examples/graeffe_root.rs',
             'src/poly/univariate/graeffe.rs', 'research/ntt-caller-gate/probe.patch']
    paths += [str(p) for p in Path('src/fft').glob('*.rs')]
    for path in paths:
        metadata['sources'][path] = digest(path)
    metadata['environment'] = {key: os.environ.get(key) for key in
                               ('RUSTFLAGS', 'RUSTC_WRAPPER', 'CARGO_TARGET_DIR', 'TMPDIR')}
    records = []
    for repeat in range(6):
        for case, selector, degree, seed, width in CASES:
            kind = 'identity' if repeat == 0 else 'timing'
            stem = f'{case}-{repeat}'
            stdout = output / f'{stem}.stdout'
            stderr = output / f'{stem}.stderr'
            timing = output / f'{stem}.time'
            env = os.environ.copy()
            input_path = args.scratch / f'{case}.coefficients'
            if kind == 'identity':
                env['ZEEBRA_NTT_GATE_INPUT'] = str(input_path)
            else:
                env.pop('ZEEBRA_NTT_GATE_INPUT', None)
            command = ['/usr/bin/time', '-f', '%e %U %S %M', '-o', str(timing),
                       'timeout', '--signal=INT', '--kill-after=5s', '60s',
                       str(args.binary), selector, f'degrees={degree}', 'no-comparand']
            with stdout.open('w') as out, stderr.open('w') as err:
                result = subprocess.run(command, stdout=out, stderr=err, env=env,
                                        preexec_fn=hard_limit, check=False)
            record = {'case': case, 'degree': degree, 'repeat': repeat, 'kind': kind,
                      'returncode': result.returncode, 'command': command,
                      'stdout': str(stdout.relative_to(root)),
                      'load_after': os.getloadavg(), 'sha256': {}}
            for path in (stdout, stderr, timing):
                record['sha256'][str(path.relative_to(root))] = digest(path)
            if result.returncode == 0:
                wall, user, system, rss = map(float, timing.read_text().split())
                record.update(wall_s=wall, cpu_s=user+system, rss_kib=int(rss))
            records.append(record)
            (root / 'records.json').write_text(json.dumps(records, indent=2) + '\n')
            if kind == 'identity' and input_path.exists():
                metadata['cases'].append(dict(case=case, characteristic=2130706433,
                    degree=degree, seed=seed ^ degree, element_bytes=width,
                    input_sha256=digest(input_path), input_bytes=input_path.stat().st_size,
                    coefficients=sum(1 for _ in input_path.open())))
                input_path.unlink()
            (root / 'manifest.json').write_text(json.dumps(metadata, indent=2) + '\n')
            print(f'{stem}: exit={result.returncode}', flush=True)
            if result.returncode:
                raise SystemExit('campaign stopped; failed attempt retained')


if __name__ == '__main__':
    main()
