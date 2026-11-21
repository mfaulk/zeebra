#!/usr/bin/env python3
"""#971 (M33-G2): paired Zeebra ÷ Zeebra sessions for one candidate against its merge base.

    campaign.py manifest --base B --head H --agent ID --session S [--gate b|c] > manifests/<S>.json
    campaign.py extract --job DIR      # journal -> records-<job>.jsonl.gz (+ .session.json)
    campaign.py retain --job DIR       # journal -> journals/<job>/ (payloads under 64 KiB)

Arms: `base` and `head`, the timed `research-sigf4` study built from `git archive` of each commit
(`build.sh`), and `grobx155` at one worker on the development rows only, for the exploratory
Zeebra ÷ grobx read. Gate B is 1 w on the three development rows and Noon-8 and Cyclic-7 (RSS);
Gate C adds the remaining Track G controls and 16 w. Request formats and inputs are #966's, and
the extractor is #970's (`research/m33-grobx-attribution/campaign.py`), unchanged.
"""
import argparse
import gzip
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


g1 = _load('m33_g1_campaign', ROOT / 'research/m33-grobx-attribution/campaign.py')
base = g1.base

DEVELOPMENT = [('wide64', 'eco-12'), ('wide64', 'katsura-11'), ('goldilocks', 'mq-random-11')]
GATE_ROWS = {
    'b': DEVELOPMENT + [('wide64', 'noon-8'), ('wide64', 'cyclic-7')],
    'c': DEVELOPMENT + [('wide64', 'cyclic-7'), ('wide64', 'noon-7'), ('wide64', 'noon-8'),
                        ('wide64', 'katsura-9'), ('goldilocks', 'katsura-11')],
    # Under 300 ms: the warm-call method (plan §11.6), k = 21 calls per process.
    'c-warm': [('wide64', 'katsura-4')],
}
WARM_CALLS = 21
HELD_OUT = {(r['field'], r['name']) for t in json.loads((ROOT / 'research/m33-baseline/held-out.json').read_text()).values()
            for r in t}


def manifest(args):
    rows = GATE_ROWS[args.gate]
    assert not HELD_OUT & set(rows), 'a held-out row is never timed for Zeebra'
    workers = [1] if args.gate == 'b' else [1, 16]
    study = lambda c: g1.study(args.bin, 'sig', c)  # noqa: E731
    arms = [g1.zeebra_arm('base', study(args.base), 'sig', args.base),
            g1.zeebra_arm('head', study(args.head), 'sig', args.head)]
    for arm in arms:
        arm['workers'] = workers
        if args.gate == 'c-warm':
            arm['argv'] += ['--repeat', str(WARM_CALLS)]
    instances = []
    for field, name in rows:
        d = Path(args.inputs, base.key(field, name))
        instances.append(dict(name=f'{field}/{name}', params=dict(field=field, name=name),
                              inputs=dict(grobx=dict(path=str(d / 'grobx.json'), sha256=base.sha(d / 'grobx.json')))))
    if args.grobx and args.gate != 'c-warm':
        arms.append(base.comparand_arm('grobx155', args.grobx155, ['{inputs[grobx]}'], [1]))
    return dict(schema='bench-job-manifest-v1', mode='dev',
                context=dict(issue=971, agent=args.agent, track='G', session=args.session),
                arms=arms, instances=instances,
                run=dict(workers=workers, cpus='8-23', repetitions=args.reps, interleave='rotate', seeds=[0], retries=0,
                         limits=dict(wall_seconds=base.CAP_S, kill_after_seconds=30, rss_bytes=base.CAP_BYTES,
                                     live_bytes=None)))


def extract(args):
    """#970's records, plus each attempt's worker count, which a 1-w-only session did not need."""
    g1.HERE = HERE
    g1.extract(args)
    state = base.aj.load(args.job / 'journal')
    workers = {a['metadata']['attempt_id']: a['cell']['workers'] for a in state['attempts']}
    calls = {a['metadata']['attempt_id']: json.loads(a['stdout']).get('calls_ns') for a in state['attempts']
             if a['status'] == 'ok' and not a['cell']['arm'].startswith('grobx')}
    path = HERE / f"records-{state['header']['bench_job']['job_id']}.jsonl.gz"
    recs = [json.loads(line) for line in gzip.decompress(path.read_bytes()).decode().splitlines()]
    for r in recs:
        r['workers'] = workers[r['attempt']]
        if calls.get(r['attempt']):
            r['zeebra']['calls_ns'] = calls[r['attempt']]
    payload = ''.join(json.dumps(r, sort_keys=True) + '\n' for r in recs).encode()
    path.write_bytes(gzip.compress(payload, compresslevel=9, mtime=0))


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=('manifest', 'extract', 'retain'))
    p.add_argument('--bin', default='/buildcache/cargo-target/zeebra-971/bin')
    p.add_argument('--base')
    p.add_argument('--head')
    p.add_argument('--gate', choices=sorted(GATE_ROWS), default='b')
    p.add_argument('--inputs', default=g1.INPUTS)
    p.add_argument('--grobx155', default='/buildcache/cargo-target/zeebra-grobx-8005a2a1/release/grobx-driver')
    p.add_argument('--no-grobx', dest='grobx', action='store_false')
    p.add_argument('--agent', default='')
    p.add_argument('--session', default='g2-1-b')
    p.add_argument('--reps', type=int, default=9)
    p.add_argument('--job', type=Path)
    args = p.parse_args()
    if args.command == 'manifest':
        print(json.dumps(manifest(args), indent=1))
    elif args.command == 'extract':
        extract(args)
    else:
        base.HERE = HERE
        base.retain(args)


if __name__ == '__main__':
    main()
