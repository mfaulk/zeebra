#!/usr/bin/env python3
"""#1012 Gate H: S0 seal and the development-panel performance matrix (plan §8.3, §8.5, §12).

    campaign.py seal                                   # S0 three-cohort draw -> s0/
    campaign.py plan --pass 1|2                        # what the next jobs would run, with a cost projection
    campaign.py drive --pass 1|2 --binary BIN          # submit and run every job of the pass, in order
    campaign.py features --binary FEATURE_COSTS        # #1009 feature-set cost per development record
    campaign.py collect                                # job reports -> results/attempts.jsonl

The rules are the ones recorded on #1012 before any cell was run (J1-J8 and the ladder refinement).
`drive` runs inside a CCD reservation that the caller holds (`tools/bench-reserve.sh reserve`); it
never reserves or releases. Jobs live under $ZEEBRA_BENCH_JOBS (default /buildcache/bench-jobs);
`results/jobs.json` lists every job this campaign submitted, which is what `collect` reads.
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import corpus_lineage as cl  # noqa: E402

CATALOGS = (ROOT / 'research/m34-public-corpus/catalog.json', ROOT / 'research/m34-structural-corpus/catalog.json')
REFERENCES = (ROOT / 'research/m34-public-corpus/references.json', ROOT / 'research/m34-structural-corpus/references.json')
S0 = HERE / 's0'
RESULTS = HERE / 'results'
JOBS = RESULTS / 'jobs.json'
SALT = 'm34-s0-v1'
EXPOSED_FAMILIES = ('katsura', 'cyclic', 'eco', 'noon', 'reimer')
UNTOUCHED, VALIDATION = 0.30, 0.20

# The #1011 arms (docs/research/m34-qualification.md §3) as one configuration per worker count.
CONFIGS = {
    'P1': ('f4', 1), 'P2': ('f4', 4), 'P3': ('f4', 16),
    'P4': ('sig', 1), 'P5': ('sig', 8), 'P6': ('sig', 16),
    'P7-w1': ('cap16', 1), 'P7-w16': ('cap16', 16),
    'P8-w1': ('adaptive', 1), 'P8-w16': ('adaptive', 16),
}
CAP_S, OUTER_S, RSS = 300, 330, 16 * 2**30
CENSORED = ('timeout', 'memory-refusal', 'rss-limit')
SLOW_MS = 60_000
CPUS = '8-23'


def records():
    out = []
    for path in CATALOGS:
        out += json.loads(path.read_text())
    return sorted(out, key=lambda r: r['id'])


def references():
    refs = {}
    for path in REFERENCES:
        refs.update(json.loads(path.read_text())['references'])
    return refs


# --- S0 ------------------------------------------------------------------------------------------

def s2_groups(rs):
    """Whole-group S2 closure exactly as `corpus_lineage.draw_split` forms it."""
    roots = cl.presentation_roots(rs)
    parents = {r['id']: r['id'] for r in rs}

    def find(name):
        while name != parents[name]:
            parents[name] = parents[parents[name]]
            name = parents[name]
        return name

    owners = {}
    for r in rs:
        for key, value in cl.group_dimensions(r, 'S2', roots).items():
            owner = owners.setdefault((key, value), r['id'])
            parents[find(r['id'])] = find(owner)
    groups = defaultdict(list)
    for name in sorted(parents):
        groups[find(name)].append(name)
    return list(groups.values())


def group_hash(group):
    return cl.sha(['hash-groups-v1', SALT, 'S2', group])


def split_file(protocol, assignments, **extra):
    return dict(schema='corpus-split-v1', protocol=protocol, **extra,
                assignments=[dict(id=i, partition=p) for i, p in sorted(assignments.items())])


def scale(r):
    n = r['lineage']['family_parameters'].get('n')
    return n if type(n) in (int, float) else None


def seal(_args):
    rs = records()
    by_id = {r['id']: r for r in rs}
    exposed = sorted(r['id'] for r in rs if r['lineage']['family_id'] in EXPOSED_FAMILIES)
    groups = s2_groups(rs)
    eligible = sorted((g for g in groups if not set(g) & set(exposed)), key=lambda g: (group_hash(g), g))
    k_u, k_v = int(UNTOUCHED * len(groups) + 0.5), int(VALIDATION * len(groups) + 0.5)
    cohort = {}
    for i, g in enumerate(eligible):
        for name in g:
            cohort[name] = 'untouched' if i < k_u else 'validation' if i < k_u + k_v else 'development'
    for g in groups:
        for name in g:
            cohort.setdefault(name, 'development')
    # The tool's own draw must select exactly the first k_u + k_v unexposed groups.
    drawn = cl.draw_split(rs, 'S2', SALT, k_u + k_v, exposed)
    assert {a['id'] for a in drawn['assignments'] if a['partition'] == 'evaluation'} == \
        {n for n, c in cohort.items() if c != 'development'}, 'hash order differs from draw_split'

    dev_groups = eligible[k_u + k_v:]
    checks, carve = {}, {}
    # S5: the first unexposed development group with both fields keeps p31, loses p64 to untouched.
    for g in dev_groups:
        sub = [by_id[n] for n in g]
        fields = {r['field']['characteristic'] for r in sub}
        if len(fields) < 2:
            continue
        wide = max(fields, key=int)
        split = split_file('S5-field', {r['id']: 'evaluation' if r['field']['characteristic'] == wide else 'development'
                                        for r in sub})
        errors = cl.check_split(sub, split)
        if not errors:
            carve['S5'] = dict(group=g, field=wide, moved=sorted(r['id'] for r in sub if r['field']['characteristic'] == wide))
            checks['S5-field'] = dict(split=split, errors=errors)
            break
    # S3: the next unexposed development group with >= 3 distinct n moves its top-n records to untouched.
    for g in dev_groups:
        if carve.get('S5', {}).get('group') == g:
            continue
        sub = [by_id[n] for n in g if scale(by_id[n]) is not None]
        sizes = sorted({scale(r) for r in sub})
        if len(sizes) < 3:
            continue
        split = split_file('S3', {r['id']: 'evaluation' if scale(r) == sizes[-1] else 'development' for r in sub},
                           scale_parameter='n')
        errors = cl.check_split(sub, split)
        if not errors:
            carve['S3'] = dict(group=g, n=sizes[-1], moved=sorted(r['id'] for r in sub if scale(r) == sizes[-1]))
            checks['S3'] = dict(split=split, errors=errors)
            break
    for kind in ('S5', 'S3'):
        if kind not in carve:
            sys.exit(f'seal stopped: no development group admits the {kind} carve-out')
        for name in carve[kind]['moved']:
            cohort[name] = 'untouched'
    s2 = dict(drawn)
    checks['S2'] = dict(split=s2, errors=cl.check_split(rs, s2))
    if any(c['errors'] for c in checks.values()):
        sys.exit(f'seal stopped: {json.dumps({k: c["errors"] for k, c in checks.items()})}')

    S0.mkdir(exist_ok=True)
    (S0 / 'exposed.json').write_text(json.dumps(exposed, indent=1) + '\n')
    for name, c in checks.items():
        (S0 / f'split-{name}.json').write_text(json.dumps(c['split'], indent=1, sort_keys=True) + '\n')
    group_rows = []
    for g in sorted(groups, key=lambda g: (group_hash(g), g)):
        families = sorted({by_id[n]['lineage']['family_id'] for n in g})
        group_rows.append(dict(hash=group_hash(g), families=families, exposed=bool(set(g) & set(exposed)),
                               cohort=sorted({cohort[n] for n in g}), records=len(g)))
    out = dict(schema='m34-cohorts-v1', salt=SALT, protocol='S2', rule='#1012 J1 (issuecomment-7151054452)',
               catalog_sha256=cl.sha(rs), catalogs={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                                    for p in CATALOGS},
               groups=len(groups), untouched_groups=k_u, validation_groups=k_v, carve_outs=carve,
               counts={c: sum(1 for v in cohort.values() if v == c) for c in ('development', 'validation', 'untouched')},
               group_table=group_rows, assignments=dict(sorted(cohort.items())))
    (S0 / 'cohorts.json').write_text(json.dumps(out, indent=1, sort_keys=True) + '\n')
    print(json.dumps({k: out[k] for k in ('groups', 'untouched_groups', 'validation_groups', 'counts')}, indent=1))
    for row in group_rows:
        print(row['hash'][:12], '/'.join(row['cohort']), row['records'], ','.join(row['families']))


def development():
    """Development records only: the one cohort Gate H may read (plan §9.1)."""
    cohorts = json.loads((S0 / 'cohorts.json').read_text())
    if cohorts['catalog_sha256'] != cl.sha(records()):
        sys.exit('the catalogs changed after S0 was sealed')
    keep = {i for i, c in cohorts['assignments'].items() if c == 'development'}
    return [r for r in records() if r['id'] in keep]


# --- Matrix --------------------------------------------------------------------------------------

def ladder_key(r):
    """#1012 J6 as refined twice: records of one generated construction differing only in scale."""
    if (r['generator'] is None and not r['id'].startswith('gen-')) or scale(r) is None:
        return None
    params = {k: v for k, v in r['lineage']['family_parameters'].items() if k not in ('n', 'sites')}
    derived = r['lineage']['presentation_parent'] is not None
    return json.dumps([r['lineage']['family_id'], r['field']['characteristic'], derived, params], sort_keys=True)


def tiers(rs):
    """Rung index per record: 0 for records outside a ladder."""
    ladders = defaultdict(list)
    for r in rs:
        key = ladder_key(r)
        if key:
            ladders[key].append(r)
    tier = {r['id']: 0 for r in rs}
    for members in ladders.values():
        sizes = sorted({scale(r) for r in members})
        for r in members:
            tier[r['id']] = sizes.index(scale(r))
    return tier


def instance_name(record_id):
    return record_id.replace('@', '.')


def outcomes():
    """(record id, config) -> list of selection records, from every collected attempt."""
    out = defaultdict(list)
    path = RESULTS / 'attempts.jsonl'
    if path.exists():
        for line in path.read_text().splitlines():
            a = json.loads(line)
            out[(a['record'], a['config'])].append(a)
    return out


def ladder_censored(rs, done):
    """(record id, config) cells the ladder rule excludes: a lower rung of the same ladder censored."""
    tier, skip = tiers(rs), set()
    ladders = defaultdict(list)
    for r in rs:
        if ladder_key(r):
            ladders[ladder_key(r)].append(r)
    for members in ladders.values():
        members.sort(key=lambda r: tier[r['id']])
        for config in CONFIGS:
            hit = False
            for r in members:
                if hit:
                    skip.add((r['id'], config))
                elif any(a['status'] in CENSORED for a in done.get((r['id'], config), [])):
                    hit = True
    return skip


def wanted(cell_attempts):
    """Repetitions a cell should have (J5): 1 after pass 1; 0 more once censored; else 5 or 3."""
    if not cell_attempts:
        return 1
    first = cell_attempts[0]
    if first['status'] in CENSORED:
        return 1
    timed = [a['wall_ms'] for a in cell_attempts if a['status'].startswith('completed-')]
    return 5 if timed and sorted(timed)[len(timed) // 2] < SLOW_MS else 3


def pending(rs, pass_no):
    """[(tier, record, config, reps)] still to run in this pass."""
    done = outcomes()
    tier, skip = tiers(rs), ladder_censored(rs, done)
    todo = []
    for r in rs:
        for config in CONFIGS:
            if (r['id'], config) in skip:
                continue
            have = done.get((r['id'], config), [])
            if pass_no == 1 and not have:
                todo.append((tier[r['id']], r, config, 1))
            elif pass_no == 2 and have:
                extra = wanted(have) - len(have)
                if extra > 0:
                    todo.append((0, r, config, extra))
    return todo


def jobs_for(todo):
    """One job per (tier, repetitions, configuration set), so a job never runs an excluded cell."""
    by_record = defaultdict(set)
    meta = {}
    for t, r, config, reps in todo:
        by_record[(t, reps, r['id'])].add(config)
        meta[r['id']] = r
    groups = defaultdict(list)
    for (t, reps, rid), configs in sorted(by_record.items()):
        groups[(t, reps, tuple(sorted(configs)))].append(meta[rid])
    return [dict(tier=t, reps=reps, configs=list(c), records=rs) for (t, reps, c), rs in sorted(groups.items())]


def inputs_dir():
    d = Path(os.environ.get('ZB1012_INPUTS', '/buildcache/cargo-target/zeebra-1012/inputs'))
    d.mkdir(parents=True, exist_ok=True)
    return d


def record_file(r):
    path = inputs_dir() / f"{instance_name(r['id'])}.json"
    text = json.dumps([r], sort_keys=True)
    if not path.exists() or path.read_text() != text:
        path.write_text(text)
    return path


def manifest(job, binary, sha, harness, agent, pass_no):
    configs = job['configs']
    arms = []
    for c in configs:
        engine, w = CONFIGS[c]
        arms.append(dict(name=c, commit=harness, binary=binary, sha256=sha, workers=[w], contract='T-GB',
                         configuration=c,
                         build=dict(profile='release', flags='fat LTO, codegen-units 1 (Cargo.toml); -C target-cpu=x86-64-v3 '
                                    '(.cargo/config.toml); RUSTC_WRAPPER="" CARGO_INCREMENTAL=0',
                                    recipe=f'git archive {harness} | tar -x; cargo build --release --locked '
                                           '--features research-sigf4 --example m34_matrix'),
                         argv=['--catalog', '{input}', '--id', '{id}', '--engine', engine, '--workers', '{workers}',
                               '--wall-s', str(CAP_S)]))
    instances = []
    for r in job['records']:
        path = record_file(r)
        lineage = {k: str(r['lineage'][k]) for k in ('family_id', 'formulation_id', 'support_id', 'source_id')}
        instances.append(dict(name=instance_name(r['id']), params=dict(id=r['id']), path=str(path),
                              sha256=hashlib.sha256(path.read_bytes()).hexdigest(), lineage=lineage))
    workers = sorted({CONFIGS[c][1] for c in configs})
    return dict(schema='bench-job-manifest-v1', mode='dev',
                context=dict(issue=1012, agent=agent, harness=harness, z0='28df047f28a87ab2da3e2077e07c56833d0cb0e1',
                             pass_no=pass_no, tier=job['tier'], s0=cl.sha(json.loads((S0 / 'cohorts.json').read_text()))),
                arms=arms, instances=instances,
                run=dict(cpus=CPUS, interleave='rotate', repetitions=job['reps'], retries=0, seeds=[0], workers=workers,
                         limits=dict(wall_seconds=OUTER_S, kill_after_seconds=30, rss_bytes=RSS, live_bytes=None)))


def projection(todo):
    """Machine-seconds: a cell's pass-1 wall (or the cap when unknown) times its repetitions."""
    done = outcomes()
    total = 0.0
    for _, r, config, reps in todo:
        have = [a['wall_ms'] for a in done.get((r['id'], config), [])]
        total += reps * (sorted(have)[len(have) // 2] / 1e3 if have else CAP_S)
    return total


def plan(args):
    rs = development()
    todo = pending(rs, args.pass_no)
    jobs = jobs_for(todo)
    print(f'pass {args.pass_no}: {len(todo)} cells, {sum(c[3] for c in todo)} attempts, {len(jobs)} jobs')
    if args.pass_no == 2:
        print(f'projected {projection(todo) / 3600:.2f} machine-hours')
    for j in jobs:
        print(f"  tier {j['tier']} reps {j['reps']} {','.join(j['configs'])}: {len(j['records'])} records")


def bench_job(*argv):
    p = subprocess.run([str(ROOT / 'tools/bench-job'), *argv], capture_output=True, text=True)
    return p.returncode, p.stdout, p.stderr


def drive(args):
    sha = hashlib.sha256(Path(args.binary).read_bytes()).hexdigest()
    agent = subprocess.run([str(ROOT / 'scripts/agent/zb-claim.sh'), 'id'], capture_output=True, text=True).stdout.strip()
    rs = development()
    jobs_seen = json.loads(JOBS.read_text()) if JOBS.exists() else []
    while True:
        todo = pending(rs, args.pass_no)
        if not todo:
            break
        # Pass 1 runs one tier at a time so the ladder rule sees the rung below.
        low = min(t for t, *_ in todo)
        batch = [x for x in todo if x[0] == low]
        for job in jobs_for(batch):
            m = manifest(job, args.binary, sha, args.harness, agent, args.pass_no)
            path = inputs_dir() / f"manifest-{cl.sha(m)[:12]}.json"
            path.write_text(json.dumps(m, sort_keys=True))
            rc, out, err = bench_job('submit', str(path))
            if rc != 0:
                sys.exit(f'submit refused ({rc}): {err.strip()}')
            job_id = out.strip().split()[-1]
            jobs_seen.append(dict(job=job_id, pass_no=args.pass_no, tier=job['tier'], configs=job['configs'],
                                  reps=job['reps'], records=[r['id'] for r in job['records']]))
            JOBS.parent.mkdir(exist_ok=True)
            JOBS.write_text(json.dumps(jobs_seen, indent=1) + '\n')
            print(f"run {job_id}: tier {job['tier']} reps {job['reps']} {len(job['records'])} records "
                  f"x {len(job['configs'])} configs", flush=True)
            rc, out, err = bench_job('run', job_id)
            print(f'  rc {rc} {err.strip()[-300:]}', flush=True)
            if rc not in (0,):
                sys.exit(f'job {job_id} did not finish (rc {rc})')
            collect_job(job_id)


def collect_job(job_id):
    """Append one job's selection records to results/attempts.jsonl (idempotent per job)."""
    refs = {instance_name(k): v['reduced_basis_digest'] for k, v in references().items()
            if v.get('status') == 'reference' and v.get('reduced_basis_digest')}
    ref_path = inputs_dir() / 'references.json'
    ref_path.write_text(json.dumps(refs, sort_keys=True))
    rc, out, err = bench_job('report', job_id, '--json', '--references', str(ref_path))
    if rc != 0:
        sys.exit(f'report {job_id} failed: {err.strip()}')
    report = json.loads(out)
    digests = {v['attempt']: v['basis_sha256'] for v in report['verification']}
    flagged = {v['attempt'] for v in report['verification'] if v['contaminated']}
    path = RESULTS / 'attempts.jsonl'
    seen = set()
    if path.exists():
        seen = {json.loads(x)['attempt'] for x in path.read_text().splitlines()}
    with path.open('a') as f:
        for s in report['selection']:
            if s['attempt'] in seen:
                continue
            row = dict(job=job_id, attempt=s['attempt'], record=s['instance'][:-4] + '@' + s['instance'][-3:],
                       config=s['arm'], workers=s['workers'], rep=s['rep'], status=s['status'], reason=s['reason'],
                       wall_ms=s['wall_ms'], completion_ms=s['completion_ms'], censored_at_ms=s['censored_at_ms'],
                       basis_sha256=digests.get(s['attempt']), contaminated=s['attempt'] in flagged,
                       family_id=s['lineage'].get('family_id'))
            f.write(json.dumps(row, sort_keys=True) + '\n')
    return report


def collect(_args):
    for job in json.loads(JOBS.read_text()):
        collect_job(job['job'])


def features(args):
    """#1009's set cost per development record (J4): `feature_costs --skip-solve`, one process each."""
    out = RESULTS / 'features.jsonl'
    have = set()
    if out.exists():
        have = {json.loads(x)['id'] for x in out.read_text().splitlines()}
    catalogs = {r['id']: p for p in CATALOGS for r in json.loads(p.read_text())}
    for r in development():
        if r['id'] in have:
            continue
        p = subprocess.run(['taskset', '--cpu-list', CPUS.split('-')[0], args.binary, '--catalog', str(catalogs[r['id']]),
                            '--id', r['id'], '--skip-solve'], capture_output=True, text=True, timeout=600)
        line = p.stdout.strip().splitlines()[-1] if p.returncode == 0 and p.stdout.strip() else None
        row = json.loads(line) if line else dict(id=r['id'], failure=p.stderr.strip()[-300:])
        with out.open('a') as f:
            f.write(json.dumps(row, sort_keys=True) + '\n')
        print(r['id'], 'ok' if line else 'FAILED', flush=True)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=('seal', 'plan', 'drive', 'features', 'collect'))
    p.add_argument('--pass', dest='pass_no', type=int, choices=(1, 2), default=1)
    p.add_argument('--binary')
    p.add_argument('--harness', default='6c77117a')
    args = p.parse_args(argv)
    if args.command in ('drive', 'features') and not args.binary:
        sys.exit(f'{args.command} needs --binary')
    dict(seal=seal, plan=plan, drive=drive, features=features, collect=collect)[args.command](args)


if __name__ == '__main__':
    main()
