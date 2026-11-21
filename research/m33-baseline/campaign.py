#!/usr/bin/env python3
"""#966 Part 2: the F0 baseline cohort as two `tools/bench-job` jobs, one per track (plan §9.1).

    campaign.py inputs   --study BIN --out DIR                 # per-row request files for each solver
    campaign.py manifest --track G|M --study BIN --inputs DIR  # bench-job manifest on stdout
    campaign.py references --inputs DIR --groebner-rs BIN      # independent digests -> references.json
    campaign.py extract --job DIR --track G|M                  # journal -> records-<track>.jsonl.gz
    campaign.py retain --job DIR                              # journal -> journals/<job>/ (small payloads)
    campaign.py threads --track G|M --study BIN ... --inputs DIR  # one sampled attempt per arm and cell

`extract` keeps one compact record per attempt (wall, CPU, RSS, contamination, basis digest and the
Zeebra statistics) so `summarize.py` regenerates `tables.md` from committed files alone. The full
journals are retained beside them under `journals/`.
"""
import argparse
import gzip
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / 'tools/external'))
import admission  # noqa: E402
import attempt_journal as aj  # noqa: E402
import census  # noqa: E402

F0 = '31e334bda226d896686c64495867729119e52b0f'
HARNESS = '9d6f16e4'  # origin/main at Part 2; `git diff --stat F0 HARNESS -- src Cargo.toml Cargo.lock` is empty
ROWS = {
    'G': dict(development=[('wide64', 'eco-12'), ('wide64', 'katsura-11'), ('goldilocks', 'mq-random-11')],
              control=[('wide64', 'cyclic-7'), ('wide64', 'noon-7'), ('wide64', 'noon-8'), ('wide64', 'katsura-9'),
                       ('goldilocks', 'katsura-11'), ('wide64', 'katsura-4')]),
    'M': dict(development=[('gf32003', 'mq-random-10'), ('m31', 'mq-random-10'), ('gf32003', 'katsura-11'),
                           ('m31', 'katsura-11')],
              control=[('gf32003', 'cyclic-7'), ('gf32003', 'noon-7'), ('m31', 'eco-11'), ('gf32003', 'katsura-4')]),
}
GENERATED = {('gf32003', 'noon-7')}  # in no catalog; built by `--generate` in the external contract's form
WORKERS = {'G': [1, 16], 'M': [1, 4, 8, 16]}
CAP_S, CAP_BYTES = admission.CAP_S, admission.CAP_BYTES
COMPARANDS = {
    'grobx155': dict(commit='8005a2a1670a7264617a6f49eeb2618d7fa21701',
                     comparand='grobx 0.155.1 (M33 pin): research/m33-baseline/grobx-pin.sh, pins.json'),
    'grobx073': dict(commit='1854835dbc25f24dc9a9ba017024d5030e99da1c',
                     comparand='grobx 0.73.3 (M31 continuity pin): tools/external/provision-grobx.sh, pins.json'),
    'groebner-rs': dict(commit='c3e1d630fba9b2155a4c389d9022f13e0ba09218',
                        comparand='groebner-rs driver: tools/external/provision-groebner-rs.sh'),
    'msolve': dict(commit='b364edcb', comparand='msolve 0.11.0 release tarball: tools/external/provision.sh, pins.json'),
}


def key(field, name):
    return f'{field}__{name}'


def rows(track):
    return ROWS[track]['development'] + ROWS[track]['control']


def case_of(study, field, name):
    gen = ['--generate'] if (field, name) in GENERATED else []
    return json.loads(subprocess.check_output(
        [study, '--field', field, '--name', name, '--engine', 'f4', '--input-only', *gen], text=True))


def write_inputs(study, out):
    for track in ROWS:
        for field, name in rows(track):
            d = Path(out, key(field, name))
            d.mkdir(parents=True, exist_ok=True)
            case = case_of(study, field, name)
            (d / 'case.json').write_text(json.dumps(case, indent=1) + '\n')
            (d / 'in.ms').write_text(admission.msolve_input(case))
            base = dict(variables=case['variables'], modulus=int(case['modulus']), order='grevlex', workers=1,
                        generators=case['generators'])
            (d / 'grobx.json').write_text(json.dumps(dict(base, mode='raw', wall_ns=CAP_S * 10**9,
                                                          rss_bytes=CAP_BYTES)))
            (d / 'groebner-rs.json').write_text(json.dumps(base))
            print(field, name, case['digest'][:12], flush=True)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def zeebra_arm(name, study, engine, workers=None):
    arm = dict(name=name, commit=HARNESS, binary=str(study), sha256=sha(study),
               build=dict(profile='release', flags='--features research-sigf4; fat LTO, codegen-units 1 (Cargo.toml); '
                                                 '-C target-cpu=x86-64-v3 (.cargo/config.toml); RUSTC_WRAPPER="" CARGO_INCREMENTAL=0',
                          recipe=f'git archive {HARNESS} | tar -x; cargo build --release --features research-sigf4 '
                                 f'--example sig_f4_study (src/, Cargo.toml, Cargo.lock identical to F0 {F0[:8]})'),
               argv=['--field', '{field}', '--name', '{name}', '{generate}', '--engine', engine,
                     '--workers', '{workers}', '--digest-only', '--wall-s', str(CAP_S)])
    if workers:
        arm['workers'] = workers
    return arm


def comparand_arm(name, binary, argv, workers=None):
    c = COMPARANDS[name.split(':')[0]]
    arm = dict(name=name, commit=c['commit'], binary=str(binary), sha256=sha(binary),
               build=dict(profile='release', flags='as provisioned (pins.json)', recipe=c['comparand'],
                          comparand=c['comparand']), argv=argv)
    if workers:
        arm['workers'] = workers
    return arm


def manifest(args):
    track = args.track
    if track == 'G':
        arms = [zeebra_arm('sigf4', args.study, 'sigf4', [1]), zeebra_arm('f4', args.study, 'f4', [1]),
                zeebra_arm('entry', args.study, 'entry', [1]), zeebra_arm('entry16', args.study, 'entry', [16]),
                comparand_arm('grobx155', args.grobx155, ['{inputs[grobx]}'], [1]),
                comparand_arm('grobx073', args.grobx073, ['{inputs[grobx]}'], [1]),
                comparand_arm('groebner-rs', args.groebner_rs, ['{inputs[groebner_rs]}'], [1])]
    else:
        # sigf4 at 1 w is H0's arm (plan §6): the signature route on Katsura-11 at a small prime.
        arms = [zeebra_arm('entry', args.study, 'entry'), zeebra_arm('sigf4', args.study, 'sigf4', [1]),
                comparand_arm('msolve', args.msolve, ['-f', '{inputs[ms]}', '-o', '/dev/stdout', '-t', '{workers}',
                                                      '-g', '2'])]
    instances = []
    selected = [r for r in rows(track) if not args.rows or key(*r) in args.rows]
    for field, name in selected:
        d = Path(args.inputs, key(field, name))
        files = dict(ms='in.ms') if track == 'M' else dict(grobx='grobx.json', groebner_rs='groebner-rs.json')
        instances.append(dict(
            name=f'{field}/{name}',
            params=dict(field=field, name=name,
                        generate='--generate' if (field, name) in GENERATED else '--digest-only'),
            inputs={k: dict(path=str(d / f), sha256=sha(d / f)) for k, f in files.items()}))
    if args.arms:
        arms = [a for a in arms if a['name'] in args.arms]
    workers = WORKERS[track] if not args.workers else args.workers
    for a in arms:
        if a.get('workers'):
            a['workers'] = [w for w in a['workers'] if w in workers]
    arms = [a for a in arms if a.get('workers', workers)]
    return dict(schema='bench-job-manifest-v1', mode='dev',
                context=dict(issue=966, agent=args.agent, track=track, session=args.session),
                arms=arms, instances=instances,
                run=dict(workers=workers, cpus='8-23', repetitions=args.reps, interleave='rotate', seeds=[0],
                         retries=0, limits=dict(wall_seconds=CAP_S, kill_after_seconds=30, rss_bytes=CAP_BYTES,
                                                live_bytes=None)))


def solver_of(arm):
    return arm.split(':')[0] if not arm.startswith(('sigf4', 'f4', 'entry')) else 'zeebra'


_DIGESTS = {}


def digest_of(arm, stdout, case):
    """The `m33-basis-v1` digest an attempt printed (Zeebra) or that its basis text hashes to; a
    repeated output (raw grobx is seeded, so its nine replies are one blob) is hashed once."""
    basis = stdout
    if solver_of(arm) not in ('zeebra', 'msolve'):
        try:  # the JSON replies carry per-call timings, so only their basis is a stable key
            reply = json.loads(stdout)
            basis = json.dumps([reply.get('basis'), reply.get('stopped'), reply.get('certified')]).encode()
        except ValueError:
            pass
    memo = (solver_of(arm), case['digest'], hashlib.sha256(basis).hexdigest())
    if memo not in _DIGESTS:
        _DIGESTS[memo] = _digest_of(arm, stdout, case)
    return _DIGESTS[memo]


def _digest_of(arm, stdout, case):
    text = stdout.decode(errors='replace')
    try:
        if solver_of(arm) == 'zeebra':
            r = json.loads(text)
            return r.get('basis_m33') if r.get('status') == 'complete' else None
        if arm.startswith('grobx'):
            return admission.grobx_digest(text, case)
        if arm == 'groebner-rs':
            return admission.groebner_rs_digest(text, case)
        if arm == 'msolve':
            return admission.msolve_digest(text, case)
    except ValueError:
        return None
    raise ValueError(arm)


ZEEBRA_FIELDS = ('call_ns', 'main_ns', 'basis_m33_ns', 'peak_rss_bytes', 'digest', 'status')
STAGES = ('bookkeeping_ns', 'symbolic_ns', 'elimination_ns', 'interreduction_ns', 'total_ns')


def extract(args):
    state = aj.load(args.job / 'journal')
    cases = {}
    out = []
    session = (state['stop'] or {}).get('contamination') or {}
    for a in state['attempts']:
        cell, md = a['cell'], a['metadata']
        field, name = cell['instance'].split('/')
        if (field, name) not in cases:
            cases[field, name] = json.loads(Path(args.inputs, key(field, name), 'case.json').read_text())
        case = cases[field, name]
        verdict = (md.get('contamination') or {}).get('verdict')
        rec = dict(track=args.track, job=state['header']['bench_job']['job_id'], attempt=md['attempt_id'],
                   arm=cell['arm'], solver=solver_of(cell['arm']), field=field, name=name, workers=cell['workers'],
                   rep=cell['rep'], status=a['status'], exit=md['exit'], wall_ns=md['process_wall_ns'],
                   cpu_s=md['cpu_seconds'], peak_rss_bytes=md['observed_peak_rss_bytes'], cpus=md['cpus'],
                   input_digest=case['digest'],
                   contaminated=bool(verdict and verdict['contaminated']) or md['attempt_id'] in session.get('flagged', {}),
                   reasons=(verdict or {}).get('reasons', []) + session.get('flagged', {}).get(md['attempt_id'], []),
                   metrics=(md.get('contamination') or {}).get('metrics'),
                   basis_m33=digest_of(cell['arm'], a['stdout'], case) if a['status'] == 'ok' else None)
        if rec['solver'] == 'zeebra' and a['status'] == 'ok':
            r = json.loads(a['stdout'])
            rec['zeebra'] = {k: r.get(k) for k in ZEEBRA_FIELDS}
            st = r.get('statistics') or {}
            rec['zeebra'].update(route=st.get('route'), stages={k: st[k] for k in STAGES if k in st} or None)
        out.append(rec)
    path = args.output or HERE / f'records-{args.track}-{state["header"]["bench_job"]["job_id"]}.jsonl.gz'
    payload = ''.join(json.dumps(r, sort_keys=True) + '\n' for r in out).encode()
    path.write_bytes(gzip.compress(payload, compresslevel=9, mtime=0))
    meta = dict(job=state['header']['bench_job'], stop=state['stop'], journal_sha256=state['journal_sha256'],
                attempts=len(out))
    Path(str(path).replace('.jsonl.gz', '.session.json')).write_text(json.dumps(meta, indent=1, sort_keys=True) + '\n')
    print(path, len(out), 'attempts')


RETAIN_BLOB_BYTES = 64 * 1024


def retain(args):
    """Copy a job's journal into journals/<job>/: header, the hash-chained journal gzipped, and every
    payload under 64 KiB (Zeebra's reports, stderr). Larger payloads, the competitors' basis texts, are
    listed by digest and size in omitted.json; `extract` read them, and the full journal stays in the job."""
    src, dst = args.job / 'journal', HERE / 'journals' / args.job.name
    (dst / 'blobs').mkdir(parents=True, exist_ok=True)
    (dst / 'header.json').write_bytes((src / 'header.json').read_bytes())
    (dst / 'journal.jsonl.gz').write_bytes(gzip.compress((src / 'journal.jsonl').read_bytes(), 9, mtime=0))
    omitted = {}
    for blob in sorted((src / 'blobs').iterdir()):
        if blob.stat().st_size < RETAIN_BLOB_BYTES:
            (dst / 'blobs' / blob.name).write_bytes(blob.read_bytes())
        else:
            omitted[blob.name[:-3]] = blob.stat().st_size
    (dst / 'omitted.json').write_text(json.dumps(dict(
        rule=f'payloads of {RETAIN_BLOB_BYTES} gzipped bytes or more are not committed', source=str(src),
        payloads=omitted), indent=1, sort_keys=True) + '\n')
    print(dst, len(omitted), 'omitted')


def references(args):
    """One independent reference digest per row, untimed, off the bench CPUs: Singular below 2³¹,
    groebner-rs at one worker on the wide fields (plan §5.2.5)."""
    os.environ.setdefault('M33_ADMISSION_CPUS', '24-39')
    admission.CPUS = os.environ['M33_ADMISSION_CPUS']
    path = HERE / 'references.json'
    refs = json.loads(path.read_text()) if path.exists() else {}
    for track in ROWS:
        for field, name in rows(track):
            if key(field, name) in refs:
                continue
            case = json.loads(Path(args.inputs, key(field, name), 'case.json').read_text())
            if track == 'M':
                _, ok, digest = admission.singular(case)
                ref = 'Singular std, redSB'
            else:
                _, ok, digest = admission.groebner_rs(args.groebner_rs, case)
                ref = 'groebner-rs, 1 worker'
            refs[key(field, name)] = dict(reference=ref, input_digest=case['digest'], basis_m33=digest if ok else None)
            print(field, name, ref, (digest or 'FAILED')[:12], flush=True)
            path.write_text(json.dumps(refs, indent=1, sort_keys=True) + '\n')


def threads(args):
    """Observed threads (plan §11.5): one census-sampled attempt per arm and cell, on the cell's CPUs."""
    m = json.loads(Path(args.manifest).read_text())
    out = Path(args.output).open('a')
    with tempfile.TemporaryDirectory(dir=os.environ.get('TMPDIR')) as d:
        for inst in m['instances']:
            for w in m['run']['workers']:
                for arm in m['arms']:
                    if w not in arm.get('workers', m['run']['workers']):
                        continue
                    values = dict(inst['params'], workers=w, inputs={k: v['path'] for k, v in inst['inputs'].items()})
                    argv = [a.format_map(values) for a in arm['argv']]
                    argv = [Path(d, 'out') if a == '/dev/stdout' else a for a in argv]
                    cpus = '8' if w == 1 else f'8-{7 + w}'
                    r = census.sampled([arm['binary'], *map(str, argv)], cpus)
                    rec = dict(track=m['context']['track'], arm=arm['name'], instance=inst['name'], workers=w, **r)
                    out.write(json.dumps(rec) + '\n')
                    out.flush()
                    print(rec['arm'], rec['instance'], w, rec['active'], rec['concurrent'], rec['rc'], flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=('inputs', 'manifest', 'references', 'extract', 'retain', 'threads'))
    p.add_argument('--study')
    p.add_argument('--out')
    p.add_argument('--inputs', default='/buildcache/cargo-target/zeebra-966-p2/inputs')
    p.add_argument('--track', choices=sorted(ROWS))
    p.add_argument('--grobx155', default='/buildcache/cargo-target/zeebra-grobx-8005a2a1/release/grobx-driver')
    p.add_argument('--grobx073', default='/buildcache/cargo-target/zeebra-966-grobx073/release/grobx-driver')
    p.add_argument('--groebner-rs', default='/buildcache/cargo-target/zeebra-groebner-rs/release/groebner-rs-driver')
    p.add_argument('--msolve', default=str(Path.home() / '.local/opt/zeebra-ext/bin/msolve'))
    p.add_argument('--agent', default='')
    p.add_argument('--session', default='baseline')
    p.add_argument('--reps', type=int, default=9)
    p.add_argument('--rows', nargs='*', help='field__name keys (an extension job)')
    p.add_argument('--arms', nargs='*')
    p.add_argument('--workers', type=int, nargs='*')
    p.add_argument('--job', type=Path)
    p.add_argument('--manifest')
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    if args.command == 'inputs':
        write_inputs(args.study, args.out or args.inputs)
    elif args.command == 'manifest':
        print(json.dumps(manifest(args), indent=1))
    elif args.command == 'references':
        references(args)
    elif args.command == 'extract':
        extract(args)
    elif args.command == 'retain':
        retain(args)
    else:
        threads(args)


if __name__ == '__main__':
    main()
