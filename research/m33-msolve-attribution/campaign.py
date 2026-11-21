#!/usr/bin/env python3
"""#972 M33-M1: the msolve gap's attribution sessions, as `tools/bench-job` jobs (plan §9.7).

    campaign.py inputs   --study BIN                          # cyclic-8 / GF(32003) for #918
    campaign.py manifest --job mq|k|fl --f0 BIN --study BIN    # bench-job manifest on stdout
    campaign.py extract  --job DIR                            # journal -> records-<job>.jsonl.gz
    campaign.py counts   --msolve-count BIN                   # msolve's work counts -> msolve-counts.json

Reuses the #966 baseline's request files, arms and record format (`research/m33-baseline/campaign.py`).
`entry` and `sigf4` run the F0 binary the baseline timed. `f4stages` runs this branch's build, whose
library differs from F0 only by #918's timer split and the concurrent-pass counters, with
`--engine f4 --stages`: on MQ10 at 4-16 workers that is exactly the route `entry` dispatches to
(`Shipping(WorkerCrossover)`), so `f4stages ÷ entry` is the instrument's overhead. `msolve-v2` is
the pinned msolve with `-v 2`, which prints its own per-round matrices and stage timings.
"""
import argparse
import gzip
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research/m33-baseline'))
sys.path.insert(0, str(ROOT / 'tools/external'))
import campaign as base  # noqa: E402
import attempt_journal as aj  # noqa: E402

INPUTS = Path('/buildcache/cargo-target/zeebra-966-p2/inputs')
MINE = Path('/buildcache/cargo-target/zeebra-972/inputs')
JOBS = {
    # MQ10 at both primes: the losing rows (smallest gaps 1.921 at 4 w and 2.254 at 8 w).
    'mq': dict(rows=[('m31', 'mq-random-10'), ('gf32003', 'mq-random-10')], workers=[1, 4, 8, 16]),
    # The named Track M primary, already an exploratory win.
    'k': dict(rows=[('m31', 'katsura-11')], workers=[1, 4, 8, 16]),
    # #918: the FL route's sweep against D' at 16 workers.
    'fl': dict(rows=[('gf32003', 'katsura-11'), ('gf32003', 'mq-random-10'), ('gf32003', 'cyclic-8')],
               workers=[16]),
    # Session 4: the reducer rule that gives msolve-shaped matrices, alone and with the FL order.
    'rd': dict(rows=[('m31', 'mq-random-10'), ('gf32003', 'mq-random-10')], workers=[4, 8, 16]),
}
GENERATED = {('gf32003', 'cyclic-8')}


def write_inputs(study):
    for field, name in GENERATED:
        d = MINE / base.key(field, name)
        d.mkdir(parents=True, exist_ok=True)
        case = json.loads(subprocess.check_output(
            [study, '--field', field, '--name', name, '--engine', 'f4', '--input-only', '--generate'], text=True))
        (d / 'case.json').write_text(json.dumps(case, indent=1) + '\n')
        print(field, name, case['digest'][:12])


def inputs_dir(field, name):
    return (MINE if (field, name) in GENERATED else INPUTS) / base.key(field, name)


def study_arm(name, binary, engine, workers, extra=()):
    arm = base.zeebra_arm(name, binary, engine, workers)
    arm['argv'] += list(extra)
    return arm


def manifest(args):
    job = JOBS[args.job]
    f0, study = args.f0, args.study
    if args.job == 'rd':
        few = ['--stages', '--reducer', 'FewestTerms']
        arms = [study_arm('f4stages', study, 'f4', None, ['--stages']),
                study_arm('f4fl', study, 'f4', None, ['--stages', '--fl']),
                study_arm('f4few', study, 'f4', None, few),
                study_arm('f4fewfl', study, 'f4', None, few + ['--fl'])]
    elif args.job == 'fl':
        arms = [study_arm('forward', study, 'f4', [16], ['--stages']),
                study_arm('fl', study, 'f4', [16], ['--stages', '--fl'])]
    else:
        ms = ['-f', '{inputs[ms]}', '-t', '{workers}', '-g', '2']
        arms = [base.zeebra_arm('entry', f0, 'entry'),
                base.comparand_arm('msolve', args.msolve, ms[:2] + ['-o', '/dev/stdout'] + ms[2:]),
                dict(base.comparand_arm('msolve', args.msolve, ms[:2] + ['-o', '/dev/null'] + ms[2:] + ['-v', '2']),
                     name='msolve-v2')]
        if args.job == 'mq':
            arms += [base.zeebra_arm('sigf4', f0, 'sigf4', [1]),
                     study_arm('f4stages', study, 'f4', [4, 8, 16], ['--stages']),
                     # The Faugère–Lachartre order: fewer products on the probe, an M2 candidate.
                     study_arm('f4fl', study, 'f4', [4, 8, 16], ['--stages', '--fl'])]
        else:
            arms += [base.zeebra_arm('sigf4', f0, 'sigf4', [1]),
                     study_arm('sigf4claim', f0, 'sigf4', [4, 8, 16], ['--claim'])]
    # The F0 arms keep the baseline's provenance; the instrumented build names this branch's commit.
    for a in arms:
        if a['binary'] == str(study):
            a['commit'] = args.commit
            a['build']['recipe'] = (f'checkout whose tracked files equal git archive {args.commit}; '
                                    f'cargo build --release --features research-sigf4 --example sig_f4_study '
                                    f'(F0 plus #918/#972 instrumentation)')
    instances = []
    for field, name in job['rows']:
        d = inputs_dir(field, name)
        files = {} if args.job in ('fl', 'rd') else dict(ms='in.ms')
        instances.append(dict(
            name=f'{field}/{name}',
            params=dict(field=field, name=name,
                        generate='--generate' if (field, name) in GENERATED else '--digest-only'),
            inputs={k: dict(path=str(d / f), sha256=base.sha(d / f)) for k, f in files.items()}))
    return dict(schema='bench-job-manifest-v1', mode='dev',
                context=dict(issue=972, agent=args.agent, track='M', session=args.job),
                arms=arms, instances=instances,
                run=dict(workers=job['workers'], cpus='8-23', repetitions=args.reps, interleave='rotate', seeds=[0],
                         retries=0, limits=dict(wall_seconds=base.CAP_S, kill_after_seconds=30,
                                                rss_bytes=base.CAP_BYTES, live_bytes=None)))


ROUND = re.compile(r'^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+) x (\d+)\s+([\d.]+)%\s+(\d+) new\s+(\d+) zero\s+([\d.]+) \|\s*([\d.]+)')
TIMING = re.compile(r'^(overall\(elapsed\)|overall\(cpu\)|select|symbolic prep\.|update|convert|linear algebra|reduce gb)'
                    r'\s+([\d.]+) sec')
DATA = re.compile(r'^(#rows reduced|#zero reductions|#pairs reduced|size of basis|#terms in basis)\s+(\d+)')


def msolve_verbose(text):
    """msolve `-v 2`: its per-round matrices and its stage timings (10 ms resolution)."""
    rounds, timings, data = [], {}, {}
    for line in text.splitlines():
        if m := ROUND.match(line):
            deg, sel, _, rows, cols, dens, new, zero, real, cpu = m.groups()
            rounds.append(dict(degree=int(deg), pairs=int(sel), rows=int(rows), columns=int(cols),
                               density=float(dens) / 100, new=int(new), zero=int(zero),
                               real_s=float(real), cpu_s=float(cpu)))
        elif m := TIMING.match(line):
            timings[m.group(1)] = float(m.group(2))
        elif m := DATA.match(line):
            data[m.group(1).lstrip('#')] = int(m.group(2))
    return dict(rounds=rounds, timings=timings, data=data)


def extract(args):
    state = aj.load(args.job / 'journal')
    session = (state['stop'] or {}).get('contamination') or {}
    cases, out = {}, []
    for a in state['attempts']:
        cell, md = a['cell'], a['metadata']
        field, name = cell['instance'].split('/')
        if (field, name) not in cases:
            cases[field, name] = json.loads((inputs_dir(field, name) / 'case.json').read_text())
        case = cases[field, name]
        arm = cell['arm']
        verdict = (md.get('contamination') or {}).get('verdict')
        flagged = session.get('flagged', {}).get(md['attempt_id'], [])
        rec = dict(job=state['header']['bench_job']['job_id'], attempt=md['attempt_id'], arm=arm,
                   solver='msolve' if arm.startswith('msolve') else 'zeebra', field=field, name=name,
                   workers=cell['workers'], rep=cell['rep'], status=a['status'], exit=md['exit'],
                   wall_ns=md['process_wall_ns'], cpu_s=md['cpu_seconds'], peak_rss_bytes=md['observed_peak_rss_bytes'],
                   input_digest=case['digest'],
                   contaminated=bool(verdict and verdict['contaminated']) or bool(flagged),
                   reasons=(verdict or {}).get('reasons', []) + flagged,
                   metrics=(md.get('contamination') or {}).get('metrics'), basis_m33=None)
        if a['status'] == 'ok':
            if arm == 'msolve':
                rec['basis_m33'] = base.digest_of('msolve', a['stdout'], case)
            elif arm == 'msolve-v2':
                rec['msolve'] = msolve_verbose((a['stderr'] or b'').decode(errors='replace'))  # -v 2 writes to stderr
            else:
                r = json.loads(a['stdout'])
                rec['basis_m33'] = r.get('basis_m33') if r.get('status') == 'complete' else None
                rec['zeebra'] = {k: r.get(k) for k in base.ZEEBRA_FIELDS}
                rec['zeebra']['statistics'] = r.get('statistics')
        out.append(rec)
    path = HERE / f'records-{args.job.name}.jsonl.gz'
    payload = ''.join(json.dumps(r, sort_keys=True) + '\n' for r in out).encode()
    path.write_bytes(gzip.compress(payload, compresslevel=9, mtime=0))
    meta = dict(job=state['header']['bench_job'], stop=state['stop'], journal_sha256=state['journal_sha256'],
                attempts=len(out))
    Path(str(path).replace('.jsonl.gz', '.session.json')).write_text(json.dumps(meta, indent=1, sort_keys=True) + '\n')
    print(path, len(out), 'attempts')


COUNT = re.compile(r'ZB_COUNT (.*)')


def counts(args):
    """msolve's pivot applications and coefficient products (`tools/external/msolve-count.py`), untimed,
    off the bench CPUs. The counting copy needs its own libneogb beside it."""
    env = dict(os.environ, LD_LIBRARY_PATH=str(Path(args.msolve_count).parents[1] / 'src/neogb/.libs'))
    out = {}
    for job in ('mq', 'k'):
        for field, name in JOBS[job]['rows']:
            for w in (1, 4, 8, 16):
                p = subprocess.run(['taskset', '-c', args.cpus, args.msolve_count, '-f',
                                    str(inputs_dir(field, name) / 'in.ms'), '-o', '/dev/null', '-t', str(w), '-g', '2'],
                                   env=env, capture_output=True, text=True, check=True)
                fields = COUNT.search(p.stderr).group(1).split()
                out[f'{field}/{name}@{w}'] = {k: int(v) for k, v in zip(fields[::2], fields[1::2])}
                print(field, name, w, out[f'{field}/{name}@{w}']['forward_products'], flush=True)
    (HERE / 'msolve-counts.json').write_text(json.dumps(out, indent=1, sort_keys=True) + '\n')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=('inputs', 'manifest', 'extract', 'counts'))
    p.add_argument('--job')
    p.add_argument('--f0', default='/buildcache/cargo-target/zeebra-966-p2/target/release/examples/sig_f4_study')
    p.add_argument('--study', default='/buildcache/cargo-target/zeebra-972/target/release/examples/sig_f4_study')
    p.add_argument('--commit', default='')
    p.add_argument('--msolve', default=str(Path.home() / '.local/opt/zeebra-ext/bin/msolve'))
    p.add_argument('--msolve-count', default='/buildcache/cargo-target/zeebra-972/msolve/counting/.libs/msolve')
    p.add_argument('--cpus', default='24-39')
    p.add_argument('--agent', default='')
    p.add_argument('--reps', type=int, default=9)
    args = p.parse_args()
    if args.command == 'inputs':
        write_inputs(args.study)
    elif args.command == 'manifest':
        print(json.dumps(manifest(args), indent=1))
    elif args.command == 'extract':
        args.job = Path(args.job)
        extract(args)
    else:
        counts(args)


if __name__ == '__main__':
    main()
