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
        ref = dict(digest=rows[0]['digest'], modulus=modulus, variables=rows[0]['variables'], basis=rows[0]['basis'])
        fixture = ROOT / 'src/grobner/external/public_corpus_references' / (problem + '.basis')
        if sorted(ref['basis']) != sorted(fixture.read_text().splitlines()):
            raise ValueError('public fixture differs from retained independent answer')
        refs[(problem, modulus)] = ref
    return refs


def validate(raw, reference, phase, problem, arm):
    if reference.get('variables'):
        if raw['digest'] != reference['digest'] or raw['modulus'] != reference['modulus']:
            raise ValueError('input identity differs from independent public reference')
        canonical = load('wide-corpus').canonical_polynomial
        normalize = lambda basis: sorted(canonical(p, reference['modulus'], reference['variables']) for p in basis)
        if normalize(raw['basis']) != normalize(reference['basis']):
            raise ValueError('complete normalized coefficients differ from public reference')
    else:
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


def validate_attempt(a, refs):
    if a['status'] != 'verified' or a['exit'] or a['stop'] or a['compiler_before'] or a['compiler_after']:
        raise ValueError('incomplete, failed or compiler-contaminated attempt')
    validate(a['raw'], refs[(a['problem'], a['modulus'])], a['phase'], a['problem'], a['arm'])
    if not 0 < a['peak_rss_bytes'] <= 2 * 1024**3 or a['process_wall_ns'] <= 0 or a['cpu_seconds'] < 0:
        raise ValueError('invalid timing or RSS boundary')


def verify_prefix(cohort, identity, refs):
    if cohort['identity'] != identity or cohort.get('refusal', {}).get('reason') != 'environment' or len(cohort.get('resumptions', [])) >= 8 or not 0 <= cohort['active_wall_seconds'] < 900:
        raise ValueError('resumption requires immutable identities and a bounded pre-child environment hold')
    accepted_prefix(cohort, refs)


def accepted_prefix(cohort, refs):
    keys = [(a['phase'], a['repeat'], a['problem'], a['modulus'], a['arm']) for a in cohort['attempts']]
    expected = list(plan())
    if keys != expected[:len(keys)] or len(keys) >= len(expected):
        raise ValueError('accepted attempts are not the exact incomplete plan prefix')
    for a in cohort['attempts']:
        validate_attempt(a, refs)


def repair_signed_reference(cohort, audit, identity, refs):
    old = cohort['attempts'][-1]
    if (cohort.get('validator_repairs') or old != audit['original_failed_attempt']
            or old['status'] != 'failed' or old['exit'] or old['stop']
            or old['compiler_before'] or old['compiler_after']
            or old.get('failure') != 'full reduced basis differs from the verified reference'
            or not old['problem'].startswith('public-')
            or cohort['identity']['commit'] != audit['original_controller_commit']
            or hashlib.sha256(old['stdout'].encode()).hexdigest() != audit['stdout_sha256']
            or hashlib.sha256(json.dumps(old['raw'],sort_keys=True).encode()).hexdigest() != audit['raw_sha256']):
        raise ValueError('repair is not the single pinned signed-residue reference mismatch')
    if {k:v for k,v in cohort['identity'].items() if k != 'commit'} != {k:v for k,v in identity.items() if k != 'commit'}:
        raise ValueError('repair changed binary, reference, hardware or build identities')
    validate(old['raw'], refs[(old['problem'],old['modulus'])], old['phase'], old['problem'], old['arm'])
    # Raw response and original failure text remain intact; only its acceptance is adjudicated.
    old['status'] = 'verified'
    old['validator_repair'] = dict(stdout_sha256=audit['stdout_sha256'], controller=audit['repair_controller_commit'])
    cohort['identity'] = identity
    cohort.setdefault('validator_repairs',[]).append(audit)
    accepted_prefix(cohort,refs)


def pair_timings(samples, controls):
    lookup = {a['repeat']: a for a in controls}
    if len(lookup) != len(controls) or len({a['repeat'] for a in samples}) != len(samples) or set(lookup) != {a['repeat'] for a in samples}:
        raise ValueError('paired repetitions differ')
    rows = []
    for a in sorted(samples,key=lambda a:a['repeat']):
        control = lookup[a['repeat']]
        if min(a['process_wall_ns'],control['process_wall_ns'],a['raw']['f4_call_ns'],control['raw']['f4_call_ns']) <= 0:
            raise ValueError('paired durations must be positive')
        rows.append(dict(repeat=a['repeat'],process_ratio=a['process_wall_ns']/control['process_wall_ns'],f4_ratio=a['raw']['f4_call_ns']/control['raw']['f4_call_ns']))
    return rows


def summarize(cohort):
    check_plan(cohort['attempts'])
    refs = references()
    for path, expected in cohort['reference_cohorts_sha256'].items():
        if sha(ROOT/path) != expected:
            raise ValueError('retained independent reference archive changed')
    identity = cohort['identity']
    if identity['build_metadata']['source_commit'] != identity['binary_build_commit'] or any(identity['binaries'][name]['sha256'] != identity['build_metadata']['binaries'][name]['sha256'] for name in ('stock','binary')):
        raise ValueError('binary build provenance differs')
    expected_refs = {f'{p}/{m}': dict(digest=r['digest'], basis_sha256=hashlib.sha256(('\n'.join(sorted(r['basis']))+'\n').encode()).hexdigest()) for (p,m),r in refs.items() if (p,m) in CASES}
    if cohort['references'] != expected_refs:
        raise ValueError('reference field/input/basis identities changed')
    check_plan(cohort['attempts'])
    groups = defaultdict(list)
    trajectories = {}
    for a in cohort['attempts']:
        validate_attempt(a, refs)
        stats = {k: v for k, v in a['raw']['statistics'].items() if not k.endswith('_ns') and k != 'full_statistics'}
        identity = (a['problem'], a['modulus'], 'original' if a['arm'] in ('stock', 'feature-off') else a['arm'])
        if stats != trajectories.setdefault(identity, stats):
            raise ValueError('same-policy trajectory drifted across observation/repetition controls')
        groups[(a['phase'], a['problem'], a['modulus'], a['arm'])].append(a)
    rows, paired = [], []
    for (phase, problem, modulus, arm), attempts in sorted(groups.items()):
        row = dict(phase=phase, problem=problem, modulus=modulus, arm=arm, repeats=len(attempts))
        for key, values in [('process_ms', [a['process_wall_ns']/1e6 for a in attempts]), ('f4_ms', [a['raw']['f4_call_ns']/1e6 for a in attempts]), ('rss_mib', [a['peak_rss_bytes']/1024**2 for a in attempts]), ('cpu_ms', [a['cpu_seconds']*1000 for a in attempts])]:
            row[key] = dict(median=median(values), minimum=min(values), maximum=max(values))
        if phase == 'native':
            row['stages_ms'] = {key: dict(median=median(a['raw']['statistics'][key]/1e6 for a in attempts), minimum=min(a['raw']['statistics'][key]/1e6 for a in attempts), maximum=max(a['raw']['statistics'][key]/1e6 for a in attempts)) for key in ('symbolic_ns','construction_ns','forward_ns','backward_ns','extraction_ns','interreduction_ns')}
            if arm in POLICIES:
                for baseline in ('stock','original'):
                    paired.append(dict(problem=problem,modulus=modulus,arm=arm,baseline=baseline,observations=pair_timings(attempts,groups[(phase,problem,modulus,baseline)])))
        if phase == 'work':
            raw = attempts[0]['raw']
            row['symbolic'] = raw['symbolic']
            row['statistics'] = raw['statistics']
            row['work'] = raw['work']
        rows.append(row)
    return dict(source=cohort['identity'], attempts=len(cohort['attempts']), active_wall_seconds=cohort['active_wall_seconds'], resumptions=cohort['resumptions'], validator_repairs=cohort.get('validator_repairs',[]), rows=rows, paired=paired)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--stock', type=Path)
    parser.add_argument('--binary', type=Path)
    parser.add_argument('--scratch', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--build-commit')
    parser.add_argument('--build-metadata', type=Path)
    parser.add_argument('--replay', type=Path)
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--validator-repair', type=Path)
    args = parser.parse_args()
    if args.validator_repair and not args.resume:
        parser.error('validator repair requires explicit resumption of the retained original cohort')
    storage, guard = load('study_artifacts'), load('grobx-work-study')
    if args.replay:
        summary = summarize(storage.load_study(args.replay / 'results.json.gz'))
        encoded = json.dumps(summary, indent=2) + '\n'
        if (args.replay / 'summary.json').read_text() != encoded:
            raise ValueError('derived symbolic summary differs')
        print('verified 346 complete reduced bases and the retained symbolic summaries')
        return
    if not all((args.stock, args.binary, args.scratch, args.output, args.build_commit, args.build_metadata)):
        parser.error('provide stock, binary, scratch, output, build-commit and build-metadata for a campaign')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip():
        parser.error('commit the instrument before measurement')
    affinity = ','.join(map(str, sorted(os.sched_getaffinity(0))))
    if os.environ.get('ZEEBRA_AFFINITY') != affinity or not os.environ.get('ZEEBRA_MACHINE'):
        parser.error('declare actual machine and affinity, and use benchlock')
    args.scratch.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.output.exists() and not args.resume:
        parser.error('output exists; retain it and resume only an environment hold')
    binaries = dict(stock=args.stock.resolve(), binary=args.binary.resolve())
    build_commit = subprocess.check_output(['git','rev-parse',args.build_commit],cwd=ROOT,text=True).strip()
    source_delta = subprocess.check_output(['git','diff',build_commit,'--','Cargo.toml','Cargo.lock','.cargo','src','examples'],cwd=ROOT,text=True)
    expected_test_delta = subprocess.check_output(['git','show','--format=','4b0750166d76626f73e4636087024ec766588871','--','src/grobner/f4/statistics.rs'],cwd=ROOT,text=True)
    if source_delta not in ('', expected_test_delta):
        parser.error('production source differs from binary build (only the pinned cfg(test) timing fixture fix is allowed)')
    build_metadata = json.loads(args.build_metadata.read_text())
    if build_metadata['source_commit'] != build_commit or any(build_metadata['binaries'][key]['sha256'] != sha(path) for key,path in binaries.items()):
        parser.error('build metadata does not bind these frozen executables')
    cohort = dict(schema=1, identity=dict(commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(), binaries={k: dict(path=str(p), sha256=sha(p)) for k, p in binaries.items()}, machine=os.environ['ZEEBRA_MACHINE'], affinity=affinity, workers=1, cargo_lock_sha256=sha(ROOT/'Cargo.lock'), rustc=subprocess.check_output(['rustc', '-vV'], text=True), build='release;fat LTO;codegen-units=1;x86-64-v3;mold;system allocator;CARGO_INCREMENTAL=0;RUSTC_WRAPPER=', topology=subprocess.check_output(['lscpu', '-e=CPU,CORE,SOCKET,NODE,CACHE,ONLINE'], text=True)), binary_build_commit=build_commit, build_metadata=build_metadata, build_metadata_sha256=sha(args.build_metadata), limits=dict(child_seconds=60, parent_seconds=185, rss_bytes=2*1024**3, campaign_seconds=900, scratch_bytes=512*1024**2, repetitions=5), environment={k: os.environ.get(k) for k in ('RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','CARGO_INCREMENTAL','RUSTC_WRAPPER')}, cargo_config_sha256=sha(ROOT/'.cargo/config.toml'), reference_cohorts_sha256={str(p.relative_to(ROOT)): sha(p) for p in [ROOT/'research/competitive/results/grobx-683.json.gz', ROOT/'research/competitive/results/grobx-683-small.json.gz', ROOT/'research/concurrent-pivots/controls.json.gz', ROOT/'research/public-corpus/results/public-679.json.gz']}, references={f'{p}/{m}': dict(digest=r['digest'], basis_sha256=hashlib.sha256(('\n'.join(sorted(r['basis']))+'\n').encode()).hexdigest()) for (p,m),r in references().items() if (p,m) in CASES}, attempts=[])
    cohort['identity']['binary_build_commit'] = cohort.pop('binary_build_commit')
    cohort['identity']['build_metadata_sha256'] = cohort.pop('build_metadata_sha256')
    cohort['identity']['build_metadata'] = cohort.pop('build_metadata')
    cohort['identity']['cfg_test_only_source_delta'] = source_delta
    cohort['identity']['cfg_test_only_source_delta_sha256'] = hashlib.sha256(source_delta.encode()).hexdigest()
    cohort['active_wall_seconds'] = 0.0
    cohort['resumptions'] = []
    refs, start = references(), time.monotonic()
    if args.resume:
        previous = storage.load_study(args.output)
        if args.validator_repair:
            audit = json.loads(args.validator_repair.read_text())
            if sha(args.output) != audit['original_cohort_sha256']:
                parser.error('repair audit does not bind the untouched original cohort')
            if subprocess.call(['git','diff','--quiet',audit['repair_controller_commit'],'--','tools/external/symbolic-live-study.py','tools/test/symbolic-live-study-test.py'],cwd=ROOT):
                parser.error('continuation controller differs from audited repair implementation')
            repair_signed_reference(previous,audit,cohort['identity'],refs)
        else:
            verify_prefix(previous, cohort['identity'], refs)
        for key in ('limits','environment','cargo_config_sha256','reference_cohorts_sha256','references'):
            if previous[key] != cohort[key]:
                parser.error('resumption changed frozen manifest/reference metadata')
        cohort = previous
        if not args.validator_repair:
            cohort['resumptions'].append(cohort.pop('refusal'))
        cohort['attempts'] = [storage.pack_attempt(a,args.output) for a in cohort['attempts']]
    prior_active_seconds = cohort['active_wall_seconds']
    cells = list(plan())
    for phase, repeat, problem, modulus, arm in cells[len(cohort['attempts']):]:
        compilers = load('worker-pool-study').compiler_processes()
        aggregate_refusal = prior_active_seconds + time.monotonic()-start > 900 or sum(p.stat().st_size for p in args.scratch.iterdir() if p.is_file()) > 512*1024**2
        if compilers or os.getloadavg()[0] > 4 or aggregate_refusal:
            cohort['active_wall_seconds'] = prior_active_seconds + time.monotonic()-start
            cohort['refusal'] = dict(reason='aggregate-budget' if aggregate_refusal else 'environment', compilers=compilers, load=os.getloadavg()[0], next=[phase,repeat,problem,modulus,arm], accepted_prefix=len(cohort['attempts']), at_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
            guard.write(args.output, cohort)
            raise RuntimeError('pre-child quiet/resource gate refused; exact verified prefix retained')
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
        cohort['active_wall_seconds'] = prior_active_seconds + time.monotonic()-start
        guard.write(args.output,cohort)
        print(phase,repeat,problem,modulus,arm,result['status'],flush=True)
        if result['status'] != 'verified':
            raise RuntimeError('failed attempt retained; no retries')
    summary = summarize(storage.load_study(args.output))
    (args.output.parent/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')


if __name__ == '__main__':
    main()
