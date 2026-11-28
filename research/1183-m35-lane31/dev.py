#!/usr/bin/env python3
"""#1183 (M35 E2) development read: the 31-bit lane on the size-12 R3 rows (dev mode; decides nothing).

    dev.py manifest --binary BIN --commit SHA --inputs DIR > manifest.json
    dev.py extract --job-dir DIR > attempts.jsonl
    dev.py table attempts.jsonl

Arms: Adaptive, F4 and the forced signature engine, each without and with `--lane31`. One worker,
shipping limits, 3 interleaved repetitions. The lane arms run on the 31-bit rows only. The wide rows
carry the same generators at 2^64 - 59 or p64 and give the 2^31/2^64 time ratio of §9.8.
`inputs` are #1200's per-record directories.
"""
import argparse
import json
import statistics
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research' / '1200-m35-publication'))
sys.path.insert(0, str(ROOT / 'tools'))
import campaign  # noqa: E402

NARROW = ('p31', 'm31', 'babybear', 'koalabear')
FAMILIES = {'gen-chandrasekhar-h-12': ('p31', 'babybear', 'koalabear', 'p64'),
            'katsura-12': ('m31', 'babybear', 'koalabear', 'w59'),
            'eco-12': ('m31', 'babybear', 'koalabear', 'w59')}
BASE = {'adaptive': ['--engine', 'adaptive'], 'f4': ['--engine', 'f4'], 'sig': ['--engine', 'sig']}
CAP_S = 300


def rows():
    return [f'{field}/{family}' for family, fields in FAMILIES.items() for field in fields]


def manifest(a):
    zeebra = campaign.zeebra_arm('adaptive', a.binary, a.commit)
    narrow = [r for r in rows() if r.split('/')[0] in NARROW]
    arms = []
    for name, flags in BASE.items():
        for lane in (False, True):
            arm = dict(zeebra, name=f'{name}-lane31' if lane else name,
                       argv=['--catalog', '{inputs[record]}', '--id', '{id}', *flags, *(['--lane31'] if lane else []),
                             '--workers', '1', '--wall-s', str(CAP_S)])
            if lane:
                arm['instances'] = narrow
            arms.append(arm)
    instances = []
    for row in rows():
        field, name = row.split('/')
        record = Path(a.inputs, row, 'record.json')
        instances.append(dict(name=row, params=dict(id=f'{name}@{field}'),
                              inputs=dict(record=dict(path=str(record), sha256=campaign.sha(record)))))
    m = dict(schema='bench-job-manifest-v1', mode='dev', context=dict(issue=1183, agent=a.agent, job='lane31-dev'),
             arms=arms, instances=instances,
             run=dict(workers=[1], cpus=a.cpus, repetitions=3, interleave='rotate', seeds=[0], retries=0,
                      limits=dict(wall_seconds=CAP_S + 30, kill_after_seconds=30, rss_bytes=campaign.CAP_BYTES,
                                  live_bytes=None)))
    json.dump(m, sys.stdout, indent=1)
    print()


def extract(a):
    state = campaign.aj.load(Path(a.job_dir) / 'journal')
    for att in state['attempts']:
        cell, md = att['cell'], att['metadata']
        verdict = (md.get('contamination') or {}).get('verdict')
        rec = dict(id=cell['instance'], arm=cell['arm'], rep=cell['rep'], harness_status=att['status'],
                   peak_rss_bytes=md['observed_peak_rss_bytes'], contaminated=bool(verdict and verdict['contaminated']))
        try:
            reply = json.loads(att['stdout'].decode().strip().splitlines()[-1])
            rec.update(status=reply.get('status'), call_ns=reply.get('call_ns'), route=reply.get('route'),
                       basis_sha256=reply.get('basis_sha256'), error=reply.get('error'))
        except (ValueError, IndexError):
            rec.update(status='unparsed')
        print(json.dumps(rec, sort_keys=True))


def table(a):
    d = defaultdict(list)
    for line in open(a.attempts):
        r = json.loads(line)
        if not r['contaminated']:
            d[(r['id'], r['arm'])].append(r)

    def med(row, arm):
        rs = d.get((row, arm), [])
        if rs and all(r['status'] == 'complete' for r in rs):
            return statistics.median(r['call_ns'] for r in rs) / 1e9
        return None

    for family, fields in FAMILIES.items():
        wide = f'{fields[-1]}/{family}'
        wide_best = min(filter(None, (med(wide, x) for x in BASE)), default=None)
        print(f'\n{family}: best wide ({fields[-1]}) = {wide_best}')
        for field in fields[:-1]:
            row = f'{field}/{family}'
            t = {arm: med(row, arm) for arm in [*BASE, *(f'{x}-lane31' for x in BASE)]}
            best = min(filter(None, (t[x] for x in BASE)), default=None)
            best_lane = min(filter(None, (t[f'{x}-lane31'] for x in BASE)), default=None)
            digests = {r['basis_sha256'] for arm in t for r in d.get((row, arm), []) if r['status'] == 'complete'}
            routes = {arm: sorted({str(r['route']) for r in d.get((row, arm), [])}) for arm in ('adaptive', 'adaptive-lane31')}
            cells = ' '.join(f'{k}={v:.3f}' if v else f'{k}=STOP' for k, v in t.items())
            gain = f'{best / best_lane:.2f}x' if best and best_lane else '-'
            ratio = (f'{best / wide_best:.2f} -> {best_lane / wide_best:.2f}'
                     if best and best_lane and wide_best else '-')
            print(f'  {row}: {cells}\n    lane gain {gain}; 2^31/2^64 {ratio}; digests={len(digests)}; routes={routes}')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='cmd', required=True)
    m = sub.add_parser('manifest')
    m.add_argument('--binary', required=True)
    m.add_argument('--commit', required=True)
    m.add_argument('--inputs', required=True)
    m.add_argument('--agent', default='synchronous-mapping-dove@feat/1183-lane31-bench')
    m.add_argument('--cpus', default='8-23')
    e = sub.add_parser('extract')
    e.add_argument('--job-dir', required=True)
    t = sub.add_parser('table')
    t.add_argument('attempts')
    a = p.parse_args()
    {'manifest': manifest, 'extract': extract, 'table': table}[a.cmd](a)


if __name__ == '__main__':
    main()
