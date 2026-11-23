#!/usr/bin/env python3
"""#1039's deciding read as `tools/bench-job` publication jobs.

    campaign.py inputs   --pipeline BIN --out DIR                    # case.json + grobx requests per row
    campaign.py manifest --job J --pipeline BIN --inputs DIR [...]   # one job's manifest on stdout
    campaign.py extract  --job DIR --inputs DIR                      # journal -> records-<job>.jsonl.gz

Rows, cohorts and the decision rule are the pre-declaration posted on #1039 before this read. Every
Zeebra arm is `lex_pipeline` built from `git archive` of the frozen tag
`measured/1039-wiedemann-lex`; grobx is the #1029 pin through its driver, asked for `order: lex`, so
it takes whichever lex route it chooses (FGLM when zero-dimensional with D <= 65535, else F4 in lex).
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
sys.path.insert(0, str(HERE))
import admission  # noqa: E402
import attempt_journal as aj  # noqa: E402
from probe import grobx_stages  # noqa: E402

FROZEN = '5cce19f0bbb7929b14d31e7a0ad112cce6e3099b'  # tag measured/1039-wiedemann-lex
GROBX = dict(commit='8005a2a1670a7264617a6f49eeb2618d7fa21701',
             comparand='grobx 0.155.1 (M33/M34 pin, #1029): research/m33-baseline/grobx-pin.sh')
CAP_S, RSS = 600, 16 * 2**30
P16, P31 = 65537, 2147483647
# key -> (family name, modulus, cohort, class), as pre-declared on #1039.
ROWS = {
    'wd-4-10': ('wd-4-10', P16, 'development', 'shape'),
    'wdsq-4-10': ('wdsq-4-10', P16, 'development', 'nonradical shape'),
    'wd-6-6': ('wd-6-6', P16, 'development', 'shape'),
    'wd-3-30': ('wd-3-30', P16, 'held-out', 'shape'),
    'wd-4-12-p31': ('wd-4-12', P31, 'held-out', 'shape'),
    'wdsq-5-6': ('wdsq-5-6', P16, 'held-out', 'nonradical shape'),
    'wdns-4-10': ('wdns-4-10', P16, 'control', 'non-shape'),
    'wdnr-4-10': ('wdnr-4-10', P16, 'control', 'nonradical non-shape'),
    'wd-5-10': ('wd-5-10', P16, 'control', 'shape, D > 65535'),
    'wd-4-6': ('wd-4-6', P16, 'context', 'shape'),
    'cyclic-7': ('cyclic-7', P16, 'context', 'non-shape'),
    'katsura-11': ('katsura-11', P16, 'context', 'dense operator'),
    'pquad-10-1': ('pquad-10-1', P16, 'context', 'shape, dense operator'),
}
SCORED = ('grobx', [1]), ('adaptive', [1]), ('wiedemann', [1]), ('direct-lex', [1])
# job -> (row keys, repetitions, arms); an arm is (name, workers). n = 9 where every arm is under
# 60 s in development, n = 3 otherwise; `classical` runs apart because it is the slow arm.
JOBS = {
    'n9': (['wd-4-10', 'wdsq-4-10', 'wd-3-30', 'wd-4-12-p31', 'wdsq-5-6', 'wd-4-6', 'cyclic-7', 'katsura-11',
            'pquad-10-1'], 9, [('grobx', [1]), ('adaptive', [1, 16]), ('wiedemann', [1]), ('direct-lex', [1, 16])]),
    'n3': (['wd-6-6', 'wd-5-10', 'wdns-4-10', 'wdnr-4-10'], 3, [*SCORED, ('classical', [1])]),
    # Top-up for contaminated n9 attempts (56 of 486, 52 on the clock rule; session not void): three
    # more repetitions of every n9 arm, pooled by summarize.py, so every cell reaches n >= 9 clean.
    'replace': (['wd-4-10', 'wdsq-4-10', 'wd-3-30', 'wd-4-12-p31', 'wdsq-5-6', 'wd-4-6', 'cyclic-7', 'katsura-11',
                 'pquad-10-1'], 3, [('grobx', [1]), ('adaptive', [1, 16]), ('wiedemann', [1]), ('direct-lex', [1, 16])]),
    'classical': (['wd-4-10', 'wdsq-4-10', 'wd-3-30', 'wd-4-12-p31', 'wdsq-5-6', 'wd-4-6', 'cyclic-7', 'katsura-11',
                   'pquad-10-1'], 3, [('classical', [1])]),
}
ZEEBRA = ('adaptive', 'wiedemann', 'classical', 'direct-lex')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def inputs(args):
    for key, (name, modulus, _cohort, _cls) in ROWS.items():
        d = Path(args.out, key)
        d.mkdir(parents=True, exist_ok=True)
        case = json.loads(subprocess.check_output(
            [args.pipeline, '--family', name, '--modulus', str(modulus), '--input-only'], text=True))
        (d / 'case.json').write_text(json.dumps(case, indent=1) + '\n')
        for mode in ('raw', 'certified'):
            (d / f'grobx-{mode}.json').write_text(json.dumps(dict(
                variables=case['variables'], modulus=modulus, order='lex', workers=1,
                generators=case['generators'], mode=mode, wall_ns=CAP_S * 10**9, rss_bytes=RSS)))
        print(key, case['digest'][:12])


def zeebra_arm(arm, pipeline, workers):
    return dict(name=f'zb-{arm}', commit=FROZEN, binary=str(pipeline), sha256=sha(pipeline), workers=workers,
                build=dict(profile='release',
                           flags='fat LTO, codegen-units 1 (Cargo.toml); -C target-cpu=x86-64-v3 '
                                 '(.cargo/config.toml); RUSTC_WRAPPER="" CARGO_INCREMENTAL=0',
                           recipe=f'git archive {FROZEN} | tar -x; cargo build --release --example lex_pipeline'),
                argv=['--input', '{inputs[case]}', '--arm', arm, '--workers', '{workers}',
                      '--wall-s', str(CAP_S), '--budget', 'lifted'])


def grobx_arm(mode, binary):
    return dict(name='grobx155' if mode == 'raw' else 'grobx155-cert', commit=GROBX['commit'],
                binary=str(binary), sha256=sha(binary), workers=[1], argv=[f'{{inputs[grobx_{mode}]}}'],
                library='grobx', library_version='0.155.1',
                build=dict(profile='release', flags='as provisioned (pins.json)', recipe=GROBX['comparand'],
                           comparand=GROBX['comparand']))


def manifest(args):
    assert FROZEN, 'freeze the tag first'
    row_keys, reps, arm_specs = JOBS[args.job]
    arms = []
    for name, workers in arm_specs:
        if name.startswith('grobx'):
            arms.append(grobx_arm('certified' if name == 'grobx-certified' else 'raw', args.grobx))
        else:
            arms.append(zeebra_arm(name, args.pipeline, workers))
    instances = []
    for key in row_keys:
        d = Path(args.inputs, key)
        files = dict(case=d / 'case.json', grobx_raw=d / 'grobx-raw.json', grobx_certified=d / 'grobx-certified.json')
        instances.append(dict(name=key, params=dict(row=key),
                              inputs={k: dict(path=str(v), sha256=sha(v)) for k, v in files.items()}))
    workers = sorted({w for _, ws in arm_specs for w in ws})
    m = dict(schema='bench-job-manifest-v1', mode=args.mode,
             context=dict(issue=1039, agent=args.agent, track=args.job, session=args.session),
             arms=arms, instances=instances,
             run=dict(workers=workers, cpus='8-23', repetitions=reps, interleave='rotate', seeds=[0], retries=0,
                      mode_wait_seconds=args.mode_wait,
                      limits=dict(wall_seconds=CAP_S, kill_after_seconds=30, rss_bytes=RSS, live_bytes=None)))
    print(json.dumps(m, indent=1))


def extract(args):
    """One compact record per attempt: status, wall, RSS, contamination, the lex-basis digest, and
    each engine's own stage split."""
    state = aj.load(args.job / 'journal')
    session = (state['stop'] or {}).get('contamination') or {}
    job = state['header']['bench_job']
    out = []
    for a in state['attempts']:
        cell, md = a['cell'], a['metadata']
        key = cell['instance']
        case = json.loads(Path(args.inputs, key, 'case.json').read_text())
        verdict = (md.get('contamination') or {}).get('verdict')
        text = a['stdout'].decode(errors='replace') if isinstance(a['stdout'], bytes) else a['stdout']
        rec = dict(job=job['job_id'], attempt=md['attempt_id'], arm=cell['arm'], workers=cell['workers'],
                   rep=cell['rep'], mode=job.get('mode'), status=a['status'], exit=md['exit'],
                   wall_ns=md['process_wall_ns'], cpu_s=md['cpu_seconds'],
                   peak_rss_bytes=md['observed_peak_rss_bytes'], row=key, name=ROWS[key][0],
                   input_digest=case['digest'],
                   contaminated=bool(verdict and verdict['contaminated'])
                   or md['attempt_id'] in session.get('flagged', {}),
                   reasons=(verdict or {}).get('reasons', []) + session.get('flagged', {}).get(md['attempt_id'], []))
        if cell['arm'].startswith('grobx'):
            mode = 'certified' if cell['arm'].endswith('cert') else 'raw'
            raw = json.loads(text) if a['status'] == 'ok' and text.strip() else {}
            rec.update(basis_m33=admission.grobx_digest(text, case, mode) if a['status'] == 'ok' else None,
                       solve_ns=raw.get('solve_ns'), certified=raw.get('certified'), stopped=raw.get('stopped'),
                       stages=grobx_stages(raw.get('report') or ''))
        elif a['status'] == 'ok':
            r = json.loads(text.strip().splitlines()[-1])
            rec['report'] = {k: v for k, v in r.items() if k not in ('name', 'digest', 'modulus')}
            rec['basis_m33'] = r.get('basis_m33')
        out.append(rec)
    path = HERE / f'records-{job["job_id"]}.jsonl.gz'
    payload = ''.join(json.dumps(r, sort_keys=True) + '\n' for r in out).encode()
    path.write_bytes(gzip.compress(payload, compresslevel=9, mtime=0))
    meta = dict(job=job, stop=state['stop'], journal_sha256=state['journal_sha256'], attempts=len(out))
    Path(str(path).replace('.jsonl.gz', '.session.json')).write_text(json.dumps(meta, indent=1, sort_keys=True) + '\n')
    print(path, len(out), 'attempts')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=['inputs', 'manifest', 'extract', 'jobs'])
    p.add_argument('--pipeline')
    p.add_argument('--grobx', default='/buildcache/cargo-target/zeebra-1029-grobx/release/grobx-driver')
    p.add_argument('--out')
    p.add_argument('--inputs', default='/buildcache/cargo-target/zeebra-1039/inputs')
    p.add_argument('--job', help=f'manifest: one of {", ".join(JOBS)}; extract: a job directory')
    p.add_argument('--mode', choices=['dev', 'publication'], default='publication')
    p.add_argument('--mode-wait', type=int, default=4 * 3600)
    p.add_argument('--agent', default='')
    p.add_argument('--session', default='deciding')
    a = p.parse_args()
    if a.command == 'jobs':
        print(' '.join(JOBS))
    elif a.command == 'inputs':
        inputs(a)
    elif a.command == 'manifest':
        manifest(a)
    else:
        a.job = Path(a.job)
        extract(a)


if __name__ == '__main__':
    main()
