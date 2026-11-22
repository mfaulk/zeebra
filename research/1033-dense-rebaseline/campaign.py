#!/usr/bin/env python3
"""#1033's deciding read as four `tools/bench-job` publication jobs: two per deciding row, split by
repetitions (n = 9 for arms under 60 s, n = 3 above, `docs/guide/benchmarking.md`).

    campaign.py inputs   --study BIN --out DIR             # case.json and grobx.json per row
    campaign.py manifest --job J --study BIN --inputs DIR  # one job's manifest on stdout
    campaign.py extract  --job DIR --inputs DIR            # journal -> records-<job>.jsonl.gz

Rows, arms and rules are fixed by the pre-declaration and owner decisions 1 and 2 on #1033: n = 18
at the shipping budget (180 s / 8 GiB), n = 20 at `--live-gib 8` (900 s / 16 GiB). Every Zeebra arm
is `sig_f4_study` built from `git archive` of the frozen tag `measured/1033-dense-rebaseline`.
"""
import argparse
import gzip
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research/m33-baseline'))
sys.path.insert(0, str(ROOT / 'tools/external'))
import admission  # noqa: E402
import attempt_journal as aj  # noqa: E402

FROZEN = '00c9f29f4df5'  # tag measured/1033-dense-rebaseline
GROBX = dict(commit='8005a2a1670a7264617a6f49eeb2618d7fa21701',
             comparand='grobx 0.155.1 (M33/M34 pin, #1029): research/m33-baseline/grobx-pin.sh')
ROWS = {
    'n18': dict(field='gf31', name='mq-dense-18-s18', live=('--digest-only', '--digest-only'),
                cap_s=180, rss=8 * 2**30),
    'n20': dict(field='gf31', name='mq-dense-20-s20', live=('--live-gib', '8'), cap_s=900, rss=16 * 2**30),
}
# (job, row, repetitions, arms); an arm is (name, engine flags, workers). From dev timings (#1033):
# arms that finish under 60 s go in the 9-rep job, the rest in the 3-rep job.
JOBS = {
    'n18-fast': ('n18', 9, [('grobx', None, [1]), ('entry', [], [4, 16]), ('sigclaim', ['--claim'], [4, 16])]),
    'n18-slow': ('n18', 3, [('entry', [], [1]), ('sig', [], [1]), ('f4', ['--stages'], [1, 4, 16])]),
    'n20-fast': ('n20', 9, [('grobx', None, [1])]),
    'n20-slow': ('n20', 3, [('entry', [], [1, 4, 16]), ('sigclaim', ['--claim'], [4, 16]),
                            ('f4', ['--stages'], [1, 4, 16])]),
}
ENGINE = {'entry': 'entry', 'sig': 'sigf4', 'sigclaim': 'sigf4', 'f4': 'f4'}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def inputs(args):
    for key, row in ROWS.items():
        d = Path(args.out, key)
        d.mkdir(parents=True, exist_ok=True)
        case = json.loads(subprocess.check_output(
            [args.study, '--field', row['field'], '--name', row['name'], '--generate', '--engine', 'f4',
             '--input-only'], text=True))
        (d / 'case.json').write_text(json.dumps(case, indent=1) + '\n')
        (d / 'grobx.json').write_text(json.dumps(dict(
            variables=case['variables'], modulus=int(case['modulus']), order='grevlex', workers=1,
            generators=case['generators'], mode='raw', wall_ns=row['cap_s'] * 10**9, rss_bytes=row['rss'])))
        print(key, case['digest'][:12])


def zeebra_arm(name, study, flags, workers, cap_s):
    return dict(name=name, commit=FROZEN, binary=str(study), sha256=sha(study), workers=workers,
                build=dict(profile='release',
                           flags='--features research-sigf4; fat LTO, codegen-units 1 (Cargo.toml); '
                                 '-C target-cpu=x86-64-v3 (.cargo/config.toml); RUSTC_WRAPPER="" CARGO_INCREMENTAL=0',
                           recipe=f'git archive {FROZEN} | tar -x; cargo build --release --features research-sigf4 '
                                  f'--example sig_f4_study'),
                argv=['--field', '{field}', '--name', '{name}', '--generate', '--engine', ENGINE[name], *flags,
                      '--workers', '{workers}', '--digest-only', '{live_flag}', '{live_value}', '--wall-s', str(cap_s)])


def manifest(args):
    row_key, reps, arm_specs = JOBS[args.job]
    row = ROWS[row_key]
    arms = []
    for name, flags, workers in arm_specs:
        if name == 'grobx':
            arms.append(dict(name='grobx155', commit=GROBX['commit'], binary=str(args.grobx),
                             sha256=sha(args.grobx), workers=workers, argv=['{inputs[grobx]}'],
                             build=dict(profile='release', flags='as provisioned (pins.json)',
                                        recipe=GROBX['comparand'], comparand=GROBX['comparand'])))
        else:
            arms.append(zeebra_arm(name, args.study, flags, workers, row['cap_s']))
    d = Path(args.inputs, row_key)
    instance = dict(name=f'{row["field"]}/{row["name"]}',
                    params=dict(field=row['field'], name=row['name'], live_flag=row['live'][0],
                                live_value=row['live'][1]),
                    inputs=dict(grobx=dict(path=str(d / 'grobx.json'), sha256=sha(d / 'grobx.json'))))
    workers = sorted({w for _, _, ws in arm_specs for w in ws})
    m = dict(schema='bench-job-manifest-v1', mode=args.mode,
             context=dict(issue=1033, agent=args.agent, track=args.job, session=args.session),
             arms=arms, instances=[instance],
             run=dict(workers=workers, cpus='8-23', repetitions=reps, interleave='rotate', seeds=[0], retries=0,
                      mode_wait_seconds=args.mode_wait,
                      limits=dict(wall_seconds=row['cap_s'], kill_after_seconds=30, rss_bytes=row['rss'],
                                  live_bytes=None)))
    print(json.dumps(m, indent=1))


def extract(args):
    """One compact record per attempt: status, wall, RSS, contamination, basis digest and the Zeebra
    statistics the gate reads (stages for f4, elimination for sigf4, route for entry)."""
    state = aj.load(args.job / 'journal')
    session = (state['stop'] or {}).get('contamination') or {}
    job = state['header']['bench_job']
    cases = {}
    out = []
    for a in state['attempts']:
        cell, md = a['cell'], a['metadata']
        field, name = cell['instance'].split('/')
        key = 'n18' if name.endswith('18-s18') else 'n20'
        case = cases.setdefault(key, json.loads(Path(args.inputs, key, 'case.json').read_text()))
        verdict = (md.get('contamination') or {}).get('verdict')
        rec = dict(job=job['job_id'], attempt=md['attempt_id'], arm=cell['arm'], workers=cell['workers'],
                   rep=cell['rep'], status=a['status'], exit=md['exit'], wall_ns=md['process_wall_ns'],
                   cpu_s=md['cpu_seconds'], peak_rss_bytes=md['observed_peak_rss_bytes'], field=field, name=name,
                   input_digest=case['digest'],
                   contaminated=bool(verdict and verdict['contaminated'])
                   or md['attempt_id'] in session.get('flagged', {}),
                   reasons=(verdict or {}).get('reasons', []) + session.get('flagged', {}).get(md['attempt_id'], []))
        if cell['arm'].startswith('grobx'):
            text = a['stdout'].decode(errors='replace') if isinstance(a['stdout'], bytes) else a['stdout']
            rec['basis_m33'] = admission.grobx_digest(text, case) if a['status'] == 'ok' else None
        elif a['status'] == 'ok':
            r = json.loads(a['stdout'])
            s = r.get('statistics') or {}
            st = s.get('stages') or {}
            rec.update(basis_m33=r.get('basis_m33'), zeebra_status=r.get('status'), call_ns=r.get('call_ns'),
                       route=s.get('route'), cascade=s.get('cascade'),
                       forward_ns=st.get('forward_ns'), stages_total_ns=st.get('total_ns'),
                       fallback_batches=st.get('parallel_fallback_batches'),
                       elimination_ns=s.get('elimination_ns'), sig_total_ns=s.get('total_ns'),
                       coefficient_products=s.get('coefficient_products'))
        out.append(rec)
    path = HERE / f'records-{job["job_id"]}.jsonl.gz'
    payload = ''.join(json.dumps(r, sort_keys=True) + '\n' for r in out).encode()
    path.write_bytes(gzip.compress(payload, compresslevel=9, mtime=0))
    meta = dict(job=job, stop=state['stop'], journal_sha256=state['journal_sha256'], attempts=len(out))
    Path(str(path).replace('.jsonl.gz', '.session.json')).write_text(json.dumps(meta, indent=1, sort_keys=True) + '\n')
    print(path, len(out), 'attempts')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=['inputs', 'manifest', 'extract'])
    p.add_argument('--study')
    p.add_argument('--grobx', default='/buildcache/cargo-target/zeebra-grobx-8005a2a1/release/grobx-driver')
    p.add_argument('--out')
    p.add_argument('--inputs', default='/buildcache/cargo-target/zeebra-1033/inputs')
    p.add_argument('--job')
    p.add_argument('--mode', choices=['dev', 'publication'], default='publication')
    p.add_argument('--mode-wait', type=int, default=4 * 3600)
    p.add_argument('--agent', default='')
    p.add_argument('--session', default='deciding')
    a = p.parse_args()
    if a.command == 'inputs':
        inputs(a)
    elif a.command == 'manifest':
        manifest(a)
    else:
        a.job = Path(a.job)
        extract(a)


if __name__ == '__main__':
    main()
