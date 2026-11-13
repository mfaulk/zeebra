#!/usr/bin/env python3
"""Bounded classical controls and a fixed-budget MQ14 probe for the pivot prototype."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import subprocess

ROOT = Path(__file__).resolve().parents[2]


def load(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT / 'tools/external' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


KATSURA = {32003: 'a7bd9edf654af9e9361f99ffd699974e5f5d9e352c42492097e200662262b33f',
           2147483647: 'aa992992dfe29a23237fe2cfbbb83ad2822313dbde1b19363b9476bd92109e8d'}
MQ14 = {32003: '4e440cfac84262260736a2368f43c7a96181986ca5bc108517299520d56f8795',
        2147483647: '029def705543e29b9f0648d3fa21a87be32358b79c3e64bb6dd222fa432c439d'}


def katsura_system(n=6):
    result = []
    for degree in range(n - 1):
        terms = [f'x{abs(i)+1}*x{abs(degree-i)+1}' for i in range(1-n, n)
                 if abs(degree-i) < n]
        result.append('+'.join(terms) + f'-x{degree+1}')
    result.append('+'.join(f'x{abs(i)+1}' for i in range(1-n, n)) + '-1')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('binary', 'scratch', 'output'):
        parser.add_argument('--' + name, type=Path, required=True)
    parser.add_argument('--max-load', type=float, default=4)
    parser.add_argument('--repeats', type=int, default=5)
    args = parser.parse_args()
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        parser.error('commit instruments before measuring')
    study = load('grobx-work-study')
    driver = load('pivot-discovery-study')
    refs = load('row-merge-study').references()
    topology = [tuple(map(int, line.split(','))) for line in subprocess.check_output(['lscpu', '-p=CPU,CORE,SOCKET'], text=True).splitlines() if not line.startswith('#')]
    cpus = driver.physical_cpus(topology, os.sched_getaffinity(0))
    if len(cpus) < 64 or args.repeats < 1:
        parser.error('64 physical cores and positive repetitions required')
    binary = args.binary.resolve()
    args.scratch.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    cohort = dict(schema=1, issue=728, commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                  binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                  singular_version=subprocess.check_output(['Singular', '--version'], text=True),
                  physical_cpus=cpus, limits=dict(wall_seconds=60, rss_bytes=2*1024**3, max_load=args.max_load),
                  policy='five controls per field/arm; one MQ14 refusal/frontier probe per field/arm, no speedup inferred from incomplete tasks',
                  references={}, attempts=[], probes=[])
    for repeat in range(args.repeats):
        for modulus in driver.sibling('grobx-work-study').MODULI:
            for name in ('cyclic-5', 'katsura-6'):
                arms = [('serial', 1)] + [(schedule, workers) for schedule in ('dynamic', 'static') for workers in driver.WORKERS]
                for schedule, workers in arms if repeat % 2 == 0 else reversed(arms):
                    if os.getloadavg()[0] > args.max_load:
                        cohort['refusal'] = dict(reason='load', repeat=repeat, name=name, modulus=modulus, schedule=schedule, workers=workers)
                        study.write(args.output, cohort)
                        raise RuntimeError('load gate refused; cohort retained')
                    command = ['taskset', '-c', ','.join(map(str, cpus[:workers])), str(binary), str(modulus), '--stages', '--problem='+name]
                    if schedule != 'serial': command += [f'--workers={workers}', '--schedule='+schedule]
                    before = resource.getrusage(resource.RUSAGE_CHILDREN)
                    result = study.guarded(command, args.scratch / str(len(cohort['attempts'])), 60, 2*1024**3)
                    after = resource.getrusage(resource.RUSAGE_CHILDREN)
                    result.update(repeat=repeat, problem=name, modulus=modulus, schedule=schedule, workers=workers,
                                  load=os.getloadavg()[0], affinity=cpus[:workers], status='failed',
                                  cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime)
                    try:
                        if result['exit'] or result['stop']: raise ValueError('child failed/refused')
                        raw = json.loads(result['stdout'])
                        result['raw'] = raw
                        key = f'{name}/{modulus}'
                        if name == 'cyclic-5':
                            reference = refs[(name, modulus)]
                        else:
                            if raw['digest'] != KATSURA[modulus]: raise ValueError('Katsura input digest changed')
                            if key not in cohort['references']:
                                script = ('option(redSB); ring r='+str(modulus)+',(x1,x2,x3,x4,x5,x6),dp; short=0;\n'
                                          +'ideal I='+','.join(katsura_system())+'; ideal G=std(I);\n'
                                          +'ideal B='+','.join(raw['basis'])+'; int ok=(ncols(B)==ncols(G)); int i,j,found;\n'
                                          +'for(i=1;i<=ncols(B);i++){found=0;for(j=1;j<=ncols(G);j++){if(B[i]==G[j]){found++;}}if(found!=1){ok=0;}}\n'
                                          +'print("@match "+string(ok)); for(i=1;i<=ncols(G);i++){print("@poly "+string(G[i]));} quit;\n')
                                path = args.scratch / f'{name}-{modulus}.sing'
                                path.write_text(script)
                                proof = study.guarded(['Singular', '-q', str(path)], args.scratch / f'proof-{modulus}', 60, 2*1024**3)
                                cohort['references'][key] = dict(modulus=modulus, digest=raw['digest'], basis=raw['basis'],
                                    singular=proof, script=script, script_sha256=hashlib.sha256(script.encode()).hexdigest())
                                if proof['exit'] or proof['stop'] or '@match 1\n' not in proof['stdout']:
                                    raise ValueError('independent Singular coefficient match failed')
                            reference = cohort['references'][key]
                        load('mq10-profile').check_answer(raw, reference)
                        result.update(status='verified', verification='complete-coefficient-match-to-independent-Singular-reference')
                    except (KeyError, ValueError, TypeError) as error:
                        result['failure'] = str(error)
                    if result['status'] == 'verified': result = load('study_artifacts').pack_attempt(result, args.output)
                    cohort['attempts'].append(result)
                    study.write(args.output, cohort)
                    print(repeat, name, modulus, schedule, workers, result['status'], flush=True)
                    if result['status'] != 'verified': raise RuntimeError('failed control retained')
    for modulus, digest in MQ14.items():
        for schedule, workers in [('serial', 1), ('dynamic', 4)]:
            command = ['taskset', '-c', ','.join(map(str, cpus[:workers])), str(binary), str(modulus), '--stages', '--problem=mq-random-14']
            if schedule != 'serial': command += ['--workers=4', '--schedule=dynamic']
            result = study.guarded(command, args.scratch / f'mq14-{modulus}-{schedule}', 60, 2*1024**3)
            result.update(problem='mq-random-14', modulus=modulus, digest=digest, schedule=schedule, workers=workers,
                          load=os.getloadavg()[0], status='incomplete-unverified')
            if result['exit'] == 0 and result['stop'] is None:
                result['raw'] = json.loads(result['stdout'])
                if result['raw']['digest'] != digest: raise ValueError('MQ14 identity mismatch')
                result['status'] = 'completed-needs-independent-reference'
            cohort['probes'].append(result)
            study.write(args.output, cohort)
            print('probe', modulus, schedule, result['status'], flush=True)


if __name__ == '__main__':
    main()
