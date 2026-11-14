#!/usr/bin/env python3
import argparse
from collections import defaultdict
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
from statistics import median
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
ARMS = ('stock', 'feature-off', 'original', 'order', 'dedup', 'both')
POLICIES = ARMS[2:]
CASES = tuple((p, m) for p in ('mq-random-10', 'cyclic-5', 'katsura-6') for m in (32003, 2147483647)) + tuple((p, 32003) for p in ('public-eco-4', 'public-noon-3', 'public-reimer-3'))


def load(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT / 'tools/external' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def plan():
    for phase, repetitions, cases, arms in [('native', 5, CASES, ARMS), ('work', 1, CASES, POLICIES), ('stage-off', 5, CASES[:2], POLICIES)]:
        for repeat in range(repetitions):
            for problem, modulus in cases:
                for arm in arms if repeat % 2 == 0 else reversed(arms):
                    yield phase, repeat, problem, modulus, arm


def references():
    refs = load('selective-backward-study').references()
    cohort = json.loads(gzip.decompress((ROOT / 'research/public-corpus/results/public-679.json.gz').read_bytes()))
    for problem, modulus in CASES:
        if not problem.startswith('public-'):
            continue
        rows = [a['report'] for a in cohort['attempts'] if a['engine'] == 'singular' and a['name'] == problem and not a['exit'] and not a['stop']]
        if len(rows) != 3 or any(r['status'] != 'complete' or '44105' not in r['version'] or r['modulus'] != modulus or hashlib.sha256(r['canonical'].encode()).hexdigest() != r['digest'] or r['basis'] != rows[0]['basis'] for r in rows):
            raise ValueError('independent public reference is missing or inconsistent')
        ref = dict(digest=rows[0]['digest'], modulus=modulus, basis=rows[0]['basis'])
        fixture = ROOT / 'src/grobner/external/public_corpus_references' / (problem + '.basis')
        if sorted(ref['basis']) != sorted(fixture.read_text().splitlines()):
            raise ValueError('public fixture differs from retained independent answer')
        refs[(problem, modulus)] = ref
    return refs


def validate(raw, reference, phase, problem, arm):
    load('mq10-profile').check_answer(raw, reference)
    if raw['problem'] != problem or raw.get('backward') is not None or raw.get('parallel') is not None:
        raise ValueError('task or elimination path differs')
    if raw['measured'] != (phase != 'stage-off') or (raw['work'] is not None) != (phase == 'work'):
        raise ValueError('observer/clock arm differs')
    stats = raw['statistics']
    if phase != 'stage-off':
        if min(stats['forward_ns'], stats['backward_ns']) < 0 or stats['forward_ns'] + stats['backward_ns'] > stats['elimination_ns']:
            raise ValueError('invalid production elimination timer refinements')
    elif any(stats[k] is not None for k in ('forward_ns', 'backward_ns', 'elimination_ns')):
        raise ValueError('disabled stage clocks were reported as measurements')
    if raw['statistics']['candidate_reduction']['batches'] != raw['statistics']['batches']:
        raise ValueError('shipping candidate output contract not used')
    policy = raw.get('symbolic')
    if arm in ('stock', 'feature-off'):
        if policy is not None:
            raise ValueError('inactive control unexpectedly selected a policy')
    elif (not policy or policy['mode'] != arm or policy['batches'] != raw['statistics']['batches']
          or not 0 <= policy['retained_seeds'] <= policy['offered_seeds']
          or (arm in ('original', 'order') and policy['retained_seeds'] != policy['offered_seeds'])):
        raise ValueError('symbolic policy metadata absent or inconsistent')


def check_plan(attempts):
    keys = [(a['phase'], a['repeat'], a['problem'], a['modulus'], a['arm']) for a in attempts]
    if keys != list(plan()):
        raise ValueError('incomplete or reordered campaign')


def summarize(cohort):
    refs = references()
    check_plan(cohort['attempts'])
    groups = defaultdict(list)
    trajectories = {}
    for a in cohort['attempts']:
        if a['status'] != 'verified' or a['exit'] or a['stop'] or a['compiler_before'] or a['compiler_after']:
            raise ValueError('incomplete, failed or compiler-contaminated attempt')
        validate(a['raw'], refs[(a['problem'], a['modulus'])], a['phase'], a['problem'], a['arm'])
        if not 0 < a['peak_rss_bytes'] <= 2 * 1024**3 or a['process_wall_ns'] <= 0 or a['cpu_seconds'] < 0:
            raise ValueError('invalid timing or RSS boundary')
        stats = {k: v for k, v in a['raw']['statistics'].items() if not k.endswith('_ns') and k != 'full_statistics'}
        identity = (a['problem'], a['modulus'], 'original' if a['arm'] in ('stock', 'feature-off') else a['arm'])
        if stats != trajectories.setdefault(identity, stats):
            raise ValueError('same-policy trajectory drifted across observation/repetition controls')
        groups[(a['phase'], a['problem'], a['modulus'], a['arm'])].append(a)
    rows = []
    for (phase, problem, modulus, arm), attempts in sorted(groups.items()):
        row = dict(phase=phase, problem=problem, modulus=modulus, arm=arm, repeats=len(attempts))
        for key, values in [('process_ms', [a['process_wall_ns']/1e6 for a in attempts]), ('f4_ms', [a['raw']['f4_call_ns']/1e6 for a in attempts]), ('rss_mib', [a['peak_rss_bytes']/1024**2 for a in attempts]), ('cpu_ms', [a['cpu_seconds']*1000 for a in attempts])]:
            row[key] = dict(median=median(values), minimum=min(values), maximum=max(values))
        if phase == 'work':
            raw = attempts[0]['raw']
            row['symbolic'] = raw['symbolic']
            row['statistics'] = raw['statistics']
            row['work'] = raw['work']
        rows.append(row)
    return dict(source=cohort['identity'], attempts=len(cohort['attempts']), rows=rows)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--stock', type=Path)
    parser.add_argument('--binary', type=Path)
    parser.add_argument('--scratch', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--replay', type=Path)
    args = parser.parse_args()
    storage, guard = load('study_artifacts'), load('grobx-work-study')
    if args.replay:
        summary = summarize(storage.load_study(args.replay / 'results.json.gz'))
        encoded = json.dumps(summary, indent=2) + '\n'
        if (args.replay / 'summary.json').read_text() != encoded:
            raise ValueError('derived symbolic summary differs')
        print('verified 346 complete reduced bases and the retained symbolic summaries')
        return
    if not all((args.stock, args.binary, args.scratch, args.output)):
        parser.error('provide stock, binary, scratch and output for a campaign')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        parser.error('commit the instrument before measurement')
    affinity = ','.join(map(str, sorted(os.sched_getaffinity(0))))
    if os.environ.get('ZEEBRA_AFFINITY') != affinity or not os.environ.get('ZEEBRA_MACHINE'):
        parser.error('declare actual machine and affinity, and use benchlock')
    args.scratch.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.output.exists():
        parser.error('output exists; retain it')
    binaries = dict(stock=args.stock.resolve(), binary=args.binary.resolve())
    cohort = dict(schema=1, identity=dict(commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(), binaries={k: dict(path=str(p), sha256=sha(p)) for k, p in binaries.items()}, machine=os.environ['ZEEBRA_MACHINE'], affinity=affinity, workers=1, cargo_lock_sha256=sha(ROOT/'Cargo.lock'), rustc=subprocess.check_output(['rustc', '-vV'], text=True), build='release;fat LTO;codegen-units=1;x86-64-v3;mold;system allocator;CARGO_INCREMENTAL=0;RUSTC_WRAPPER=', topology=subprocess.check_output(['lscpu', '-e=CPU,CORE,SOCKET,NODE,CACHE,ONLINE'], text=True)), limits=dict(child_seconds=60, parent_seconds=185, rss_bytes=2*1024**3, campaign_seconds=900, scratch_bytes=512*1024**2, repetitions=5), environment={k: os.environ.get(k) for k in ('RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','CARGO_INCREMENTAL','RUSTC_WRAPPER')}, cargo_config_sha256=sha(ROOT/'.cargo/config.toml'), reference_cohorts_sha256={str(p.relative_to(ROOT)): sha(p) for p in [ROOT/'research/competitive/results/grobx-683.json.gz', ROOT/'research/competitive/results/grobx-683-small.json.gz', ROOT/'research/concurrent-pivots/controls.json.gz', ROOT/'research/public-corpus/results/public-679.json.gz']}, references={f'{p}/{m}': dict(digest=r['digest'], basis_sha256=hashlib.sha256(('\n'.join(sorted(r['basis']))+'\n').encode()).hexdigest()) for (p,m),r in references().items() if (p,m) in CASES}, attempts=[])
    refs, start = references(), time.monotonic()
    for phase, repeat, problem, modulus, arm in plan():
        compilers = load('worker-pool-study').compiler_processes()
        if compilers or os.getloadavg()[0] > 4 or time.monotonic()-start > 900 or sum(p.stat().st_size for p in args.scratch.iterdir() if p.is_file()) > 512*1024**2:
            cohort['refusal'] = dict(reason='environment/aggregate-budget', compilers=compilers, load=os.getloadavg()[0], next=[phase,repeat,problem,modulus,arm])
            guard.write(args.output, cohort)
            raise RuntimeError('quiet/resource gate refused; prefix retained')
        key = 'stock' if arm == 'stock' else 'binary'
        if sha(binaries[key]) != cohort['identity']['binaries'][key]['sha256']:
            raise ValueError('frozen binary changed')
        command = [str(binaries[key]), str(modulus), '--problem='+problem]
        if phase != 'stage-off': command.append('--stages')
        if phase == 'work': command.append('--work')
        if arm in POLICIES: command.append('--symbolic='+arm)
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        result = guard.guarded(['timeout','--signal=KILL','185',*command], args.scratch/str(len(cohort['attempts'])), 60, 2*1024**3)
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        result.update(phase=phase, repeat=repeat, problem=problem, modulus=modulus, arm=arm, compiler_before=compilers, compiler_after=load('worker-pool-study').compiler_processes(), load_after=os.getloadavg()[0], cpu_seconds=after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime, status='failed')
        try:
            if result['exit'] or result['stop'] or result['compiler_after']:
                raise ValueError('child failed/refused or compiler contamination')
            raw = json.loads(result['stdout'])
            result['raw'] = raw
            result['peak_rss_bytes'] = max(result['observed_peak_rss_bytes'], raw.get('peak_rss_bytes') or 0)
            if not 0 < result['peak_rss_bytes'] <= 2*1024**3:
                raise ValueError('missing/over-budget RSS')
            validate(raw, refs[(problem,modulus)], phase, problem, arm)
            result['status'] = 'verified'
        except (ValueError, KeyError, TypeError) as error:
            result['failure'] = str(error)
        cohort['attempts'].append(storage.pack_attempt(result,args.output) if result['status']=='verified' else result)
        guard.write(args.output,cohort)
        print(phase,repeat,problem,modulus,arm,result['status'],flush=True)
        if result['status'] != 'verified':
            raise RuntimeError('failed attempt retained; no retries')
    summary = summarize(storage.load_study(args.output))
    (args.output.parent/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')


if __name__ == '__main__':
    main()
