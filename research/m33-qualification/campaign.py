#!/usr/bin/env python3
"""#974 M33-Q: F0 and F2 harness builds, the bench-job manifests and the untimed references.

    campaign.py build --commit SHA [--harness SHA]            # git archive SHA + this harness; prints the binary
    campaign.py manifest --suite SUITE --f0-study BIN --f2-study BIN --f2 SHA [--agent ID] > manifest.json
    campaign.py manifest --suite gate-d-G --gate-d --f2 SHA ...  # the held-out read; refused without both
    campaign.py inputs --study BIN                             # case.json per correctness row (no solve)
    campaign.py references --study BIN                         # Singular / groebner-rs digests, untimed

Suites: `grevlex`, `grlex`, `lex` (correctness, 3 repetitions at 1 and 16 workers), `regression-G`,
`regression-M` (controls, n = 9), `small-G`, `small-M` (controls under 300 ms, warm calls: 22 calls
per process, the cold one dropped, n = 31) and `gate-d-G`, `gate-d-M` (held-out, n = 9). Every other
suite refuses a held-out row, by name and by input digest; a Gate D suite refuses unless `--gate-d
--f2 SHA` are both given.
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research/m33-baseline'))
import admission  # noqa: E402
import campaign as baseline  # noqa: E402

F0 = baseline.F0
HARNESS = 'examples/m33_qualify.rs'
BUILD = Path(os.environ.get('M33Q_BUILD', '/buildcache/cargo-target/zeebra-974'))
HELD_OUT = json.loads((ROOT / 'research/m33-baseline/held-out.json').read_text())
CATALOG = {(c['field'], c['name']) for c in json.loads((ROOT / 'research/wide-corpus/cases.json').read_text())}
FIELDS = ('gf2', 'gf32003', 'm31', 'w59', 'wide64', 'goldilocks')
CROSS = ('katsura-8', 'eco-9', 'cyclic-6', 'noon-7', 'mq-random-9-s2')
LEX = ('katsura-4', 'eco-6', 'cyclic-5')
# #961's table, every instance named in it, plus two GF(2) rows.
ROWS_961 = [('wide64', 'katsura-9'), ('goldilocks', 'katsura-11'), ('wide64', 'katsura-11'),
            ('goldilocks', 'mq-random-11'), ('goldilocks', 'mq-random-10'), ('m31', 'katsura-10'),
            ('gf32003', 'mq-random-10'), ('m31', 'mq-random-10'), ('wide64', 'eco-12'), ('m31', 'eco-11'),
            ('gf2', 'katsura-7'), ('gf2', 'cyclic-6')]
# Under 300 ms at some relevant worker count in the F0 baseline cohort (records-*.jsonl.gz, entry arm).
SMALL = {'G': {'cyclic-7', 'katsura-4', 'katsura-9', 'noon-7'}, 'M': {'cyclic-7', 'katsura-4', 'noon-7'}}
WALL_S, RSS = 180, 8 * 2**30


def row(order, field, name):
    """One instance; ladder MQ rows (no seed) take the ladder's seed n, and a wide row frozen in the
    #738 catalog is read from it, as the F0 baseline timed it."""
    if name.startswith('mq-random-') and '-s' not in name and (field, name) not in CATALOG:
        name = f'{name}-s{name.rsplit("-", 1)[1]}'
    return dict(order=order, field=field, name=name, catalog=(field, name) in CATALOG)


def held_out(r):
    return any((h['field'], h['name']) == (r['field'], r['name']) for t in HELD_OUT.values() for h in t)


def suite_rows(suite):
    if suite == 'grevlex':
        rows = [row('grevlex', f, n) for t in baseline.ROWS for f, n in baseline.rows(t)]
        rows += [row('grevlex', f, n) for f in FIELDS for n in CROSS]
    elif suite == 'grlex':
        rows = [row('grlex', f, n) for f, n in ROWS_961]
    elif suite == 'lex':
        rows = [row('lex', f, n) for f in FIELDS for n in LEX]
    elif suite.startswith(('regression-', 'small-')):
        track = suite[-1]
        controls = baseline.ROWS[track]['control']
        small = suite.startswith('small-')
        rows = [row('grevlex', f, n) for f, n in controls if (n in SMALL[track]) == small]
    elif suite in ('gate-d-G', 'gate-d-M'):
        rows = [dict(order='grevlex', field=h['field'], name=h['name'], catalog=False) for h in HELD_OUT[suite[-1]]]
    else:
        raise SystemExit(f'unknown suite {suite}')
    out = []
    for r in rows:
        if r not in out:
            out.append(r)
    return out


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def build(commit, harness):
    """`git archive` of `commit` with this harness file laid over it, release (fat LTO, one codegen
    unit, x86-64-v3 from Cargo.toml and .cargo/config.toml); never under $HOME (CLAUDE.md §1)."""
    full = subprocess.check_output(['git', 'rev-parse', commit], text=True, cwd=ROOT).strip()
    src, target = BUILD / f'src-{full[:12]}', BUILD / f'target-{full[:12]}'
    shutil.rmtree(src, ignore_errors=True)
    src.mkdir(parents=True)
    archive = subprocess.run(['git', 'archive', full], cwd=ROOT, check=True, capture_output=True).stdout
    subprocess.run(['tar', '-x', '-C', str(src)], input=archive, check=True)
    text = subprocess.check_output(['git', 'show', f'{harness}:{HARNESS}'], cwd=ROOT)
    (src / HARNESS).write_bytes(text)
    env = dict(os.environ, CARGO_TARGET_DIR=str(target), RUSTC_WRAPPER='', CARGO_INCREMENTAL='0',
               TMPDIR=str(BUILD / 'tmp'))
    (BUILD / 'tmp').mkdir(parents=True, exist_ok=True)
    subprocess.run(['cargo', 'build', '-j24', '--release', '--locked', '--example', 'm33_qualify'],
                   cwd=src, env=env, check=True)
    out = BUILD / 'bin' / full[:12] / 'm33_qualify'
    out.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(target / 'release/examples/m33_qualify', out)
    print(out, sha(out))


def arm(name, study, commit, harness, engine, workers=None, extra=()):
    a = dict(name=name, commit=commit, binary=str(Path(study).resolve()), sha256=sha(study),
             build=dict(profile='release', flags='fat LTO, codegen-units 1 (Cargo.toml); -C target-cpu=x86-64-v3 '
                                                 '(.cargo/config.toml); RUSTC_WRAPPER="" CARGO_INCREMENTAL=0',
                        recipe=f'git archive {commit} | tar -x; git show {harness}:{HARNESS} > {HARNESS}; '
                               'cargo build --release --locked --example m33_qualify'),
             argv=['--field', '{field}', '--name', '{name}', '{catalog}', '--order', '{order}', '--engine', engine,
                   '--workers', '{workers}', '--wall-s', str(WALL_S), *extra])
    if workers:
        a['workers'] = workers
    return a


def manifest(args):
    suite = args.suite
    gate_d = suite.startswith('gate-d-')
    if gate_d and not (args.gate_d and args.f2):
        raise SystemExit('Gate D is the one held-out read (plan §13): pass --gate-d --f2 <commit> explicitly')
    if args.gate_d and not gate_d:
        raise SystemExit('--gate-d belongs to the gate-d-G and gate-d-M suites only')
    if not args.f2:
        raise SystemExit('--f2 <commit> is required: the F2 arm is built from that commit')
    rows = suite_rows(suite)
    digests = {h['digest'] for t in HELD_OUT.values() for h in t}
    if not gate_d and any(held_out(r) or case_of(args.f2_study, r)['digest'] in digests for r in rows):
        raise SystemExit(f'{suite} names a held-out row; only Gate D may read it')
    if gate_d and any(case_of(args.f2_study, r)['digest'] not in digests for r in rows):
        raise SystemExit('a Gate D row does not reproduce its held-out input digest')
    correctness = suite in ('grevlex', 'grlex', 'lex')
    engines = args.engines or (['entry'] if gate_d else ['entry', 'f4'])
    extra = ['--sample-threads'] if correctness else ['--repeat', '22'] if suite.startswith('small-') else []
    arms = []
    for version, study, commit in (('f0', args.f0_study, F0), ('f2', args.f2_study, args.f2)):
        for engine in engines:
            if suite == 'grlex' and version == 'f0' and engine == 'entry':
                continue  # #961: F0's graded-lex signature route exhausts 8 GiB; F2 must route it to F4
            arms.append(arm(f'{version}-{engine}', study, commit, args.harness, engine, extra=extra))
    if correctness:
        workers = [1, 16]
    else:
        workers = baseline.WORKERS[suite[-1]]
    instances = [dict(name=f'{r["order"]}/{r["field"]}/{r["name"]}',
                      params=dict(field=r['field'], name=r['name'], order=r['order'],
                                  catalog='--catalog' if r['catalog'] else '')) for r in rows]
    reps = args.reps or (3 if correctness else 31 if suite.startswith('small-') else 9)
    m = dict(schema='bench-job-manifest-v1', mode=args.mode or ('publication' if gate_d else 'dev'),
             context=dict(issue=974, agent=args.agent, suite=suite, f0=F0, f2=args.f2, harness=args.harness),
             arms=arms, instances=instances,
             run=dict(workers=args.workers or workers, cpus=args.cpus, repetitions=reps, interleave='rotate',
                      seeds=[0], retries=0,
                      limits=dict(wall_seconds=WALL_S + 20, kill_after_seconds=30, rss_bytes=RSS, live_bytes=None)))
    if args.rows:
        m['instances'] = [i for i in instances if i['name'] in args.rows]
    return m


def case_of(study, r):
    argv = [study, '--field', r['field'], '--name', r['name'], '--input-only'] + (['--catalog'] if r['catalog'] else [])
    return json.loads(subprocess.check_output(argv, text=True))


def inputs(args):
    out = Path(args.out)
    for suite in ('grevlex', 'grlex', 'lex'):
        for r in suite_rows(suite):
            d = out / f'{r["field"]}__{r["name"]}'
            d.mkdir(parents=True, exist_ok=True)
            (d / 'case.json').write_text(json.dumps(case_of(args.study, r), indent=1) + '\n')


SINGULAR_ORDER = dict(grevlex='dp', grlex='Dp', lex='lp')


def singular(case, order):
    names = ','.join(case['variables'])
    script = (f"short=0;\nring r={case['modulus']},({names}),{SINGULAR_ORDER[order]};\n"
              f"ideal i={','.join(case['generators'])};\noption(redSB);\nideal g=std(i);\n"
              "int k;\nfor(k=1;k<=size(g);k++){print(g[k]);}\nquit;\n")
    r = admission.guarded(['Singular', '-q', '--no-rc', '-c', script], admission.CERTIFIED_CAP_S)
    texts = [t for t in r['stdout'].splitlines() if t.strip()]
    ok = r['rc'] == 0 and r['stop'] is None and bool(texts)
    return admission.basis_digest.basis_digest(texts, int(case['modulus']), case['variables']) if ok else None


def groebner_rs(binary, case, order):
    with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False, dir=os.environ.get('TMPDIR')) as f:
        json.dump(dict(variables=case['variables'], modulus=int(case['modulus']), order=order, workers=1,
                       generators=case['generators']), f)
    r = admission.guarded([binary, f.name], admission.CERTIFIED_CAP_S)
    os.unlink(f.name)
    return admission.groebner_rs_digest(r['stdout'] if r['rc'] == 0 and r['stop'] is None else '', case)


def references(args):
    """One independent digest per correctness row, untimed and off the bench CPUs: Singular below
    2³¹ (GF(2) included), groebner-rs at one worker on the wide fields. A grevlex row the F0 baseline
    already referenced (by input digest) reuses that reading."""
    admission.CPUS = os.environ.setdefault('M33_ADMISSION_CPUS', '24-39')
    prior = {v['input_digest']: v for v in json.loads((ROOT / 'research/m33-baseline/references.json').read_text()).values()}
    path = HERE / 'references.json'
    refs = json.loads(path.read_text()) if path.exists() else {}
    for suite in ('grevlex', 'grlex', 'lex'):
        for r in suite_rows(suite):
            k = f'{r["order"]}/{r["field"]}/{r["name"]}'
            if k in refs or (args.rows and k not in args.rows):
                continue
            case = case_of(args.study, r)
            if r['order'] == 'grevlex' and case['digest'] in prior and prior[case['digest']]['basis_m33']:
                ref = dict(prior[case['digest']], reference=prior[case['digest']]['reference'] + ' (#966)')
            elif int(case['modulus']) < 2**31:
                ref = dict(reference=f'Singular std, redSB, {SINGULAR_ORDER[r["order"]]}',
                           basis_m33=singular(case, r['order']))
            else:
                ref = dict(reference='groebner-rs, 1 worker', basis_m33=groebner_rs(args.groebner_rs, case, r['order']))
            refs[k] = dict(ref, input_digest=case['digest'])
            print(k, ref['reference'], (ref['basis_m33'] or 'FAILED')[:12], flush=True)
            path.write_text(json.dumps(refs, indent=1, sort_keys=True) + '\n')


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=('build', 'manifest', 'inputs', 'references'))
    p.add_argument('--commit')
    p.add_argument('--harness', default='HEAD')
    p.add_argument('--suite')
    p.add_argument('--f0-study')
    p.add_argument('--f2-study')
    p.add_argument('--f2')
    p.add_argument('--gate-d', action='store_true')
    p.add_argument('--agent', default='')
    p.add_argument('--engines', nargs='*')
    p.add_argument('--workers', type=int, nargs='*')
    p.add_argument('--reps', type=int)
    p.add_argument('--rows', nargs='*')
    p.add_argument('--cpus', default='8-23')
    p.add_argument('--mode', choices=('dev', 'publication'))
    p.add_argument('--study')
    p.add_argument('--out', default=str(BUILD / 'inputs'))
    p.add_argument('--groebner-rs', default='/buildcache/cargo-target/zeebra-groebner-rs/release/groebner-rs-driver')
    args = p.parse_args(argv)
    if args.command == 'build':
        build(args.commit, args.harness)
    elif args.command == 'manifest':
        print(json.dumps(manifest(args), indent=1))
    elif args.command == 'inputs':
        inputs(args)
    else:
        references(args)


if __name__ == '__main__':
    main()
