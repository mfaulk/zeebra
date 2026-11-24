#!/usr/bin/env python3
"""#1011 / #997: the preregistered Cyclic-8 no-regression gate and MQ10 regime read (gate997.json).

    gate997.py references                       # untimed independent references -> gate997-references.json
    gate997.py manifest --job cyclic8|mq10 --harness BIN [--agent ID] > manifest.json
    gate997.py verdict --job-dir DIR ...         # per-cell intervals and the admission decision -> gate997.md

The thresholds, rows, workers and n are gate997.json, committed before any timed read (owner
decision on #1043). Nothing here changes them.
"""
import argparse
import importlib.util
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import bench_stats as bs  # noqa: E402

PREREG = json.loads((HERE / 'gate997.json').read_text())
REFS = HERE / 'gate997-references.json'
WALL_S, RSS = 180, 8 * 2**30


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _m33q():
    return _load('m33q', ROOT / 'research/m33-qualification/campaign.py')


def split(row):
    order, field, name = row.split('/')
    return dict(order=order, field=field, name=name)


def manifest(job, harness_bin, agent):
    m33q = _m33q()
    arms = [m33q.arm(f'z0-{e}', harness_bin, PREREG['z0'], PREREG['harness'], e) for e in ('f4', 'fewest-fl')]
    instances = [dict(name=r, params=dict(**{k: v for k, v in split(r).items()}, catalog='')) for r in job['rows']]
    return dict(schema='bench-job-manifest-v1', mode='publication',
                context=dict(issue=1011, candidate=997, agent=agent, job=job['name'], z0=PREREG['z0'],
                             harness=PREREG['harness'], prereg='research/m34-qualification/gate997.json'),
                arms=arms, instances=instances,
                run=dict(workers=job['workers'], cpus='8-23', repetitions=PREREG['repetitions'], interleave='rotate',
                         seeds=[0], retries=0, mode_wait_seconds=1800,
                         limits=dict(wall_seconds=WALL_S + 20, kill_after_seconds=30, rss_bytes=RSS, live_bytes=None)))


def cell_verdict(records, reference, rule):
    """Paired fewest-fl / f4 over clean attempts equal to the reference; 'short' below n pairs."""
    good = [r for r in records if r['status'] == 'ok' and not r['contaminated']
            and r['report'].get('status') == 'complete' and r['report'].get('basis_m33') == reference]
    by = {e: {(r['job'], r['rep']): r['wall_ns'] for r in good if r['engine'] == e} for e in ('f4', 'fewest-fl')}
    ratios = bs.paired_ratios(by['fewest-fl'], by['f4'])
    out = dict(pairs=len(ratios), dropped=len(records) - len(good))
    if len(ratios) < PREREG['repetitions']:
        return dict(out, verdict='short', ci=None)
    ci = bs.paired_ratio(ratios, seed=rule)
    ok = ci.hi <= 1.05 if rule == 'every upper <= 1.05' else ci.hi < 1
    return dict(out, verdict='pass' if ok else 'fail', ci=ci)


def decision(cyclic8, mq10):
    if 'fail' in cyclic8:
        return 'reject'
    return 'admit' if all(v == 'pass' for v in cyclic8) and mq10 == 'pass' else 'defer'


def references(_args):
    """Untimed, off the bench CPUs: Singular below 2^31; grobx 0.155.1 certified (proof-checked,
    digest-only reply) on 2^64-353, since the groebner-rs driver is not provisioned here; MQ10's from
    research/m33-baseline/references.json (Singular, the same input digest)."""
    m33q = _m33q()
    admission = m33q.admission
    admission.CPUS = '24-39'
    harness = _args.harness
    refs = json.loads(REFS.read_text()) if REFS.exists() else {}
    for job in PREREG['jobs']:
        for row in job['rows']:
            if row in refs:
                continue
            r = split(row)
            case = json.loads(admission.guarded([harness, '--field', r['field'], '--name', r['name'],
                                                 '--input-only'], 60)['stdout'])
            if r['field'] == 'm31' and r['name'] == 'mq-random-10-s10':
                base = json.loads((ROOT / 'research/m33-baseline/references.json').read_text())['m31__mq-random-10']
                if base['input_digest'] != case['digest']:
                    raise SystemExit('MQ10 input differs from the M33 reference input')
                ref = dict(reference=base['reference'] + ' (research/m33-baseline/references.json)',
                           basis_m33=base['basis_m33'])
            elif int(case['modulus']) < 2**31:
                ref = dict(reference='Singular std, redSB, dp', basis_m33=m33q.singular(case, r['order']))
            else:
                ref = dict(reference='grobx 0.155.1 certified, digest-only', basis_m33=grobx(_args.grobx, case))
            refs[row] = dict(ref, input_digest=case['digest'])
            print(row, ref['reference'], (ref['basis_m33'] or 'FAILED')[:12], flush=True)
            REFS.write_text(json.dumps(refs, indent=1, sort_keys=True) + '\n')


def grobx(binary, case):
    import os
    import tempfile
    admission = _m33q().admission
    with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False, dir=os.environ.get('TMPDIR')) as f:
        json.dump(dict(variables=case['variables'], modulus=int(case['modulus']), order='grevlex', workers=1,
                       generators=case['generators'], mode='certified', digest_only=True,
                       wall_ns=1800 * 10**9, rss_bytes=32 * 2**30), f)
    r = admission.guarded([binary, f.name], 1800)
    os.unlink(f.name)
    reply = json.loads(r['stdout']) if r['rc'] == 0 and r['stdout'].strip() else {}
    return reply.get('basis_m33') if reply.get('certified') and not reply.get('stopped') else None


def verdict(args):
    summarize = _load('m33q_summarize', ROOT / 'research/m33-qualification/summarize.py')
    refs = json.loads(REFS.read_text())
    records = [a for d in args.job_dir for a in summarize.attempts(d)]
    rules = {row: job for job in PREREG['jobs'] for row in job['rows']}
    lines = ['| Row | Workers | Rule | Pairs | fewest-fl ÷ f4 [95%] | Verdict |', '|---|---:|---|---:|---|---|']
    by_job = {j['name']: [] for j in PREREG['jobs']}
    for row, job in rules.items():
        for w in job['workers']:
            cell = [r for r in records if r['instance'] == row and r['workers'] == w]
            v = cell_verdict(cell, refs[row]['basis_m33'], job['pass'])
            by_job[job['name']].append(v['verdict'])
            ci = v['ci']
            text = f'{ci.median:.3f} [{ci.lo:.3f}, {ci.hi:.3f}]' if ci else '—'
            lines.append(f"| {row} | {w} | {job['pass']} | {v['pairs']} | {text} | {v['verdict']} |")
    d = decision(by_job['cyclic8'], (by_job['mq10'] or ['short'])[0])
    lines += ['', f'**Decision: {d}** ({PREREG["decision"]}).']
    (HERE / 'gate997.md').write_text('\n'.join(lines) + '\n')
    print('\n'.join(lines))


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=('references', 'manifest', 'verdict'))
    p.add_argument('--job', choices=[j['name'] for j in PREREG['jobs']])
    p.add_argument('--harness')
    p.add_argument('--grobx', default='/buildcache/cargo-target/zeebra-bench-m34/grobx-8005a2a1/release/grobx-driver')
    p.add_argument('--agent', default='')
    p.add_argument('--job-dir', nargs='*', default=[])
    args = p.parse_args(argv)
    if args.command == 'manifest':
        job = next(j for j in PREREG['jobs'] if j['name'] == args.job)
        print(json.dumps(manifest(job, args.harness, args.agent), indent=1))
    elif args.command == 'references':
        references(args)
    else:
        verdict(args)


if __name__ == '__main__':
    main()
