"""Reuse the existing row runner/watchdog; invoke this bounded campaign under benchlock."""
import argparse
import gzip
import hashlib
import importlib.util
import json
import os
import re
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/external'))
spec = importlib.util.spec_from_file_location('guarded', ROOT / 'tools/external/grobx-cohort.py')
guarded = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guarded)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    data = (json.dumps(value, indent=2) + '\n').encode()
    with path.open('wb') as stream:
        with gzip.GzipFile(filename='', mode='wb', fileobj=stream, mtime=0) as zipped:
            zipped.write(data)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--scratch', type=Path, required=True)
    parser.add_argument('--runtime-packages', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    if (root / 'cohort.json.gz').exists():
        raise SystemExit('preserve the existing cohort; reproduce in a fresh checkout')
    args.scratch.mkdir(parents=True, exist_ok=False)
    cases = [(name, p) for p in (32003, 2147483647)
             for name in ('mq-random-10', 'katsura-11', 'cyclic-5')]
    metadata = dict(utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
                    load=os.getloadavg(), binary=str(args.binary), binary_sha256=digest(args.binary),
                    runtime_packages=json.loads(args.runtime_packages.read_text()), sources={})
    for name, command in dict(source=['git','rev-parse','HEAD'], rustc=['rustc','-Vv'],
                              topology=['lscpu','-e=CPU,CORE,SOCKET,NODE,CACHE'],
                              cpu=['lscpu'], status=['git','status','--short']).items():
        metadata[name] = subprocess.check_output(command, text=True)
    metadata['environment'] = {key: os.environ.get(key) for key in ('RUSTFLAGS','RUSTC_WRAPPER',
        'CARGO_TARGET_DIR','TMPDIR','LD_LIBRARY_PATH','ZEEBRA_GIAC','ZEEBRA_GIAC_LIBRARY_PATH','ZEEBRA_MACHINE','ZEEBRA_SINGULAR','SINGULAR_DATA_DIR')}
    library_env = dict(os.environ, LD_LIBRARY_PATH=os.environ['ZEEBRA_GIAC_LIBRARY_PATH'])
    metadata['giac_ldd'] = subprocess.check_output(['ldd', os.environ['ZEEBRA_GIAC']],
                                                 text=True, env=library_env)
    singular_binary = os.environ.get('ZEEBRA_SINGULAR', '/usr/bin/Singular')
    metadata['singular_ldd'] = subprocess.check_output(['ldd', singular_binary], text=True)
    metadata['giac_binary_sha256'] = digest(os.environ['ZEEBRA_GIAC'])
    metadata['singular_binary_sha256'] = digest(singular_binary)
    libraries = re.findall(r'=> (/\S+)', metadata['giac_ldd'] + metadata['singular_ldd'])
    metadata['runtime_library_sha256'] = {path: digest(path) for path in sorted(set(libraries))}
    for path in ['Cargo.toml','Cargo.lock','.cargo/config.toml','src/grobner/external/giac.rs',
                 'src/grobner/external/singular.rs','examples/groebner_comparison.rs',
                 'tools/external/grobx-cohort.py','research/giac/PLAN.md','research/giac/run.py']:
        metadata['sources'][path] = digest(ROOT / path)
    metadata['inputs'] = {f'{name}@{p}': subprocess.check_output([str(args.binary), '--list',
                          '--row',name,'--modulus',str(p)], text=True).strip()
                          for name,p in cases}
    (root / 'manifest.json').write_text(json.dumps(metadata, indent=2) + '\n')
    attempts = []
    for repetition in range(5):
        for name, p in cases:
            for workers in ((1,4) if repetition%2 == 0 else (4,1)):
                cpus = {2} if workers == 1 else {2,3,4,5}
                os.sched_setaffinity(0, cpus)
                os.environ['ZEEBRA_AFFINITY'] = ','.join(map(str, sorted(cpus)))
                attempt = guarded.run(args.binary,args.scratch,len(attempts),name,p,workers,'giac')
                attempt['repetition'] = repetition
                attempt['affinity'] = sorted(os.sched_getaffinity(0))
                attempt['load_after'] = os.getloadavg()
                attempts.append(attempt)
                write(root / 'cohort.json.gz', dict(attempts=attempts))
    os.sched_setaffinity(0,{2})
    os.environ['ZEEBRA_AFFINITY']='2'
    for name, p in [('mq-planted-wide-6',18446744073709551263),
                    ('groebner-rs-wide-control',18446744073709551557)]:
        attempts.append(guarded.run(args.binary,args.scratch,len(attempts),name,p,1,'giac'))
        write(root / 'cohort.json.gz', dict(attempts=attempts))
    metadata['load_final'] = os.getloadavg()
    (root / 'manifest.json').write_text(json.dumps(metadata, indent=2) + '\n')


if __name__ == '__main__':
    main()
