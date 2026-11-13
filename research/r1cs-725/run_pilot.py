#!/usr/bin/env python3
"""Run the ten declared importer cases under an external wall and virtual-memory ceiling."""
import argparse
import hashlib
import json
import os
import pathlib
import resource
import signal
import subprocess
import sys
import time

sys.dont_write_bytecode = True
from gate import encode, section


def hard_limit():
    ceiling = 512 * 1024 * 1024
    resource.setrlimit(resource.RLIMIT_AS, (ceiling, ceiling))


def run_child(command, wall):
    process = subprocess.Popen(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               start_new_session=True, preexec_fn=hard_limit)
    stop = None
    try:
        try:
            stdout, stderr = process.communicate(timeout=wall)
        except subprocess.TimeoutExpired:
            stop = 'timeout'
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
    except BaseException:
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGKILL)
        process.wait()
        raise
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr), stop


def sections(raw):
    import struct
    at = 12
    result = []
    for _ in range(int.from_bytes(raw[8:12], 'little')):
        kind, size = struct.unpack_from('<IQ', raw, at)
        at += 12
        result.append((kind, raw[at:at+size]))
        at += size
    return result


def rebuild(parts):
    import struct
    return b'r1cs' + struct.pack('<II', 1, len(parts)) + b''.join(section(kind, payload) for kind,payload in parts)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=pathlib.Path, required=True)
    parser.add_argument('--reader-repo', type=pathlib.Path, required=True)
    parser.add_argument('--output', type=pathlib.Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    root = pathlib.Path(__file__).resolve().parents[2]
    own = root / 'tests/fixtures/r1cs/multiplier.r1cs'
    public = args.reader_repo / 'test/testutils/example.r1cs'
    raw = own.read_bytes()
    gf7 = {'n8':8,'prime':'7','nWires':4,'nPublicOutputs':1,'nPublicInputs':1,'nPrivateInputs':1,'nLabels':4,'nConstraints':3,'map':[0,1,2,3],
           'constraints':[[{'1':'1'},{'2':'1'},{'3':'1'}],[{'0':'1'},{'1':'1'},{'1':'1'}],[{},{},{}]]}
    inputs = args.output / 'inputs'
    inputs.mkdir(exist_ok=True)
    (inputs / 'gf7.r1cs').write_bytes(encode(gf7))
    (inputs / 'truncated.r1cs').write_bytes(raw[:-1])
    for name, offset, replacement in [('wrong-modulus',4,b'\x02'),('too-many-wires',36,(101).to_bytes(4,'little')),('too-many-rows',60,(1001).to_bytes(4,'little'))]:
        parts = sections(raw)
        header = bytearray(next(payload for kind,payload in parts if kind == 1))
        header[offset:offset+len(replacement)] = replacement
        if name == 'too-many-wires':
            header[52:60] = (101).to_bytes(8,'little')
        (inputs / f'{name}.r1cs').write_bytes(rebuild([(kind,bytes(header) if kind==1 else payload) for kind,payload in parts]))
    cases = [
        ('producer-valid',own,'bn254',3,['--symbols',str(root/'tests/fixtures/r1cs/multiplier.sym'),'--assignment','1,15,3,5'],'complete',None),
        ('public-roundtrip',public,'bn254',6,[],'complete',None),
        ('gf7-valid',inputs/'gf7.r1cs','7',3,['--assignment','1,2,3,6'],'complete',None),
        ('capacity-refusal',own,'bn254',2,[],'refused','Arity'),
        ('wrong-modulus',inputs/'wrong-modulus.r1cs','bn254',3,[],'refused','FieldMismatch'),
        ('truncated',inputs/'truncated.r1cs','bn254',3,[],'refused','Truncated'),
        ('constant-wire-refusal',own,'bn254',3,['--assignment','0,15,3,5'],'refused','ConstantWire'),
        ('wire-limit',inputs/'too-many-wires.r1cs','bn254',3,[],'refused','Limit'),
        ('constraint-limit',inputs/'too-many-rows.r1cs','bn254',3,[],'refused','Limit'),
        ('expansion-limit',own,'bn254',3,['--max-products','0'],'refused','Limit'),
    ]
    manifest = {'source_commit':subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip(),
                'rustc':subprocess.check_output(['rustc','-Vv'],text=True),
                'binary_sha256':hashlib.sha256(args.binary.read_bytes()).hexdigest(),
                'cargo_lock_sha256':hashlib.sha256((root/'Cargo.lock').read_bytes()).hexdigest(),
                'build':'release, no-default-features, fat LTO, one codegen unit, x86-64-v3; RUSTC_WRAPPER empty',
                'cpu':subprocess.check_output(['lscpu'],text=True),
                'affinity':sorted(os.sched_getaffinity(0)), 'workers':1, 'seed':0,
                'limits':{'wall_seconds':60,'virtual_bytes':512*1024*1024,'wires':100,'constraints':1000},
                'scope':'import/model/evaluate only; no solve or recovery; one fresh process per case; no comparative speed claim',
                'attempts':[]}
    for name, filename, field, capacity, extra, expected, error_fragment in cases:
        command = [str(args.binary.resolve()),str(filename.resolve()),'--field',field,'--capacity',str(capacity),*extra]
        timing = args.output / f'{name}.time'
        at = time.perf_counter_ns()
        try:
            child, stop = run_child(['/usr/bin/time','-f','%M','-o',str(timing),*command],60)
            wall = time.perf_counter_ns()-at
            try:
                report = json.loads(child.stdout)
            except (ValueError, TypeError) as error:
                manifest['attempts'].append({'name':name,'command':command,
                    'input_sha256':hashlib.sha256(filename.read_bytes()).hexdigest(),
                    'outcome':'invalid-response','stop':stop,'returncode':child.returncode,
                    'harness_wall_ns':wall,'stdout_text':child.stdout,'stderr':child.stderr,
                    'detail':str(error)})
                (args.output / f'{name}.stdout.txt').write_text(child.stdout)
                (args.output / f'{name}.stderr.txt').write_text(child.stderr)
                raise RuntimeError('child failed to return JSON; raw outcome retained') from error
            peak = int(timing.read_text().strip().splitlines()[-1])*1024
            record = {'name':name,'command':command,'input_sha256':hashlib.sha256(filename.read_bytes()).hexdigest(),
                      'returncode':child.returncode,'stop':stop,'harness_wall_ns':wall,'process_peak_rss_bytes':peak,
                      'stdout':report,'stderr':child.stderr,'expected':expected}
            (args.output / f'{name}.stdout.json').write_text(child.stdout)
            (args.output / f'{name}.stderr.txt').write_text(child.stderr)
            manifest['attempts'].append(record)
            assert report['outcome'] == expected, record
            assert child.returncode == (0 if expected=='complete' else 1), record
            if error_fragment:
                assert error_fragment in report['error'],record
            if name == 'public-roundtrip':
                assert report['source_digest']==report['canonical_digest']=='8fdbe0d7cfd4379e36593ed9597889a3b7b750566d035c7cc805b9acaaf3d039'
            if name in ['producer-valid','gf7-valid']:
                assert report['evaluation_agrees'] and report['assignment_satisfies']
        finally:
            (args.output / 'pilot.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'attempts':len(manifest['attempts']),'all_expected_outcomes':True}))


if __name__ == '__main__':
    main()
