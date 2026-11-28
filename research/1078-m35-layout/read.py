#!/usr/bin/env python3
"""#1078 (M35 D): the §9.4 memory read of the four row layouts.

    read.py inputs --study BIN --out DIR
    read.py manifest --binary BIN --commit SHA --inputs DIR --job timing|refused > manifest.json
    read.py extract --job-dir DIR > attempts.jsonl
    read.py decide timing.jsonl refused.jsonl
    read.py manifest ... --job control --control-binary BIN --control-commit SHA > manifest.json
    read.py control control.jsonl

Every arm is the forced signature engine at one worker under its default limits (the shipping
512,000,000-byte live budget), `m34_matrix --engine sig --workers 1 --row-layout ARM --stages`.
The criteria were posted on #1078 before this read ran.
"""
import argparse
import gzip
import json
import statistics
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / 'tools'))
sys.path.insert(0, str(ROOT / 'research' / '1200-m35-publication'))
import bench_stats  # noqa: E402
import campaign  # noqa: E402
from census import record  # noqa: E402

ARMS = ('baseline', 'source', 'u16', 'both')
STRUCTURED = ('katsura-11', 'eco-12', 'cyclic-7', 'noon-9')
TIMING = ([('mq-dense-15-s15', f) for f in ('gf32003', 'm31')]
          + [('mq-dense-18-s18', 'm31'), ('mq-random-11-s11', 'gf32003')]
          + [(r, f) for r in STRUCTURED for f in ('gf32003', 'm31', 'goldilocks')]
          # Sizes the census did not run.
          + [('mq-dense-16-s16', 'm31'), ('katsura-12', 'm31')])
REFUSED = [('mq-dense-20-s20', 'm31')]
# The default's cost of carrying the layout dispatch: the baseline arm at the layout commit against the
# census commit, whose cascade has no layout variants.
CONTROL = [('mq-dense-15-s15', 'm31'), ('mq-dense-16-s16', 'm31'), ('mq-random-11-s11', 'gf32003'),
           ('katsura-12', 'm31'), ('eco-12', 'gf32003'), ('noon-9', 'm31'), ('cyclic-7', 'goldilocks')]
CAP_S = 1800


def inputs(a):
    for row, field in TIMING + REFUSED:
        rec = record(row, field, a.study)
        d = Path(a.out, field, row)
        d.mkdir(parents=True, exist_ok=True)
        (d / 'record.json').write_text('[\n' + json.dumps(rec, sort_keys=True) + '\n]\n')
        print(rec['id'], file=sys.stderr)


def manifest(a):
    rows, reps = {'timing': (TIMING, 7), 'refused': (REFUSED, 1), 'control': (CONTROL, 7)}[a.job]
    argv = ['--catalog', '{inputs[record]}', '--id', '{id}', '--engine', 'sig', '--workers', '1', '--stages',
            '--wall-s', str(CAP_S)]
    # The template's argv is replaced below; only binary, commit and env are taken from it.
    zeebra = campaign.zeebra_arm('adaptive', a.binary, a.commit)
    if a.job == 'control':
        census = campaign.zeebra_arm('adaptive', a.control_binary, a.control_commit)
        arms = [dict(census, name='census', argv=argv), dict(zeebra, name='layout', argv=argv)]
    else:
        arms = [dict(zeebra, name=arm, argv=argv + ['--row-layout', arm]) for arm in ARMS]
    instances = []
    for row, field in rows:
        path = Path(a.inputs, field, row, 'record.json')
        instances.append(dict(name=f'{field}/{row}', params=dict(id=f'{row}@{field}'),
                              inputs=dict(record=dict(path=str(path), sha256=campaign.sha(path)))))
    m = dict(schema='bench-job-manifest-v1', mode='publication',
             context=dict(issue=1078, agent=a.agent, job=f'row-layout-{a.job}'), arms=arms, instances=instances,
             run=dict(workers=[1], cpus=a.cpus, repetitions=reps, interleave='rotate', seeds=[0], retries=0,
                      mode_wait_seconds=3600,
                      limits=dict(wall_seconds=CAP_S + 60, kill_after_seconds=30, rss_bytes=campaign.CAP_BYTES,
                                  live_bytes=None)))
    json.dump(m, sys.stdout, indent=1)
    print()


def extract(a):
    state = campaign.aj.load(Path(a.job_dir) / 'journal')
    session = (state['stop'] or {}).get('contamination') or {}
    for att in state['attempts']:
        cell, md = att['cell'], att['metadata']
        verdict = (md.get('contamination') or {}).get('verdict')
        rec = dict(id=cell['instance'], arm=cell['arm'], rep=cell['rep'], harness_status=att['status'],
                   peak_rss_bytes=md['observed_peak_rss_bytes'],
                   contaminated=bool(verdict and verdict['contaminated'])
                   or md['attempt_id'] in session.get('flagged', {}))
        try:
            reply = json.loads(att['stdout'].decode(errors='replace').strip().splitlines()[-1])
            rec.update(status=reply.get('status'), call_ns=reply.get('call_ns'), error=reply.get('error'),
                       basis_sha256=reply.get('basis_sha256'), layout=reply.get('layout'),
                       batches=(reply.get('counters') or {}).get('batches'))
        except (ValueError, IndexError):
            rec.update(status='unparsed')
        print(json.dumps(rec, sort_keys=True))


def load(path):
    d = defaultdict(list)
    for line in (gzip.open(path, "rt") if str(path).endswith(".gz") else open(path)):
        r = json.loads(line)
        if not r['contaminated']:
            d[(r['id'], r['arm'])].append(r)
    return d


def live_peak(r, arm):
    # The arm's own live peak; equal to the census entry for it (tests::
    # test_every_row_layout_keeps_the_basis_and_meets_its_census).
    return r['layout']['peak_live_bytes'][arm]


def decide(a):
    d = load(a.timing)
    verdict = {arm: [] for arm in ARMS[1:]}
    for row, field in TIMING:
        rid = f'{field}/{row}'
        base = [r for r in d[(rid, 'baseline')] if r['status'] == 'complete']
        digests = {r['basis_sha256'] for arm in ARMS for r in d[(rid, arm)] if r['status'] == 'complete'}
        line = [f'{rid:26s}']
        for arm in ARMS[1:]:
            done = [r for r in d[(rid, arm)] if r['status'] == 'complete']
            if not base or not done:
                line.append(f'{arm}: incomplete')
                verdict[arm].append(False)
                continue
            ratio = bench_stats.independent_ratio([r['call_ns'] for r in done], [r['call_ns'] for r in base],
                                                  seed=1078)
            live = live_peak(done[0], arm) / live_peak(base[0], 'baseline')
            rss = statistics.median(r['peak_rss_bytes'] for r in done) / statistics.median(
                r['peak_rss_bytes'] for r in base)
            ok = live <= 0.80 and ratio.hi <= 1.03 and len(digests) == 1
            verdict[arm].append(ok)
            line.append(f'{arm}: live={live:.3f} wall={ratio.median:.3f} ({ratio.lo:.3f}-{ratio.hi:.3f}) '
                        f'rss={rss:.3f} {"ok" if ok else "MISS"}')
        print(' | '.join(line) + f' | digests={len(digests)} base={statistics.median(r["call_ns"] for r in base) / 1e9 if base else 0:.3f}s')
    refused = load(a.refused)
    completed = {}
    for row, field in REFUSED:
        rid = f'{field}/{row}'
        for arm in ARMS:
            rs = refused[(rid, arm)]
            completed[arm] = bool(rs) and all(r['status'] == 'complete' for r in rs)
            print(f'refused {rid} {arm}: {[(r["status"], (r.get("error") or "")[:60]) for r in rs]}')
    for arm in ARMS[1:]:
        rows_ok = sum(verdict[arm])
        print(f'{arm}: {rows_ok}/{len(verdict[arm])} rows meet live<=0.80 and wall hi<=1.03; '
              f'refused case completed={completed[arm]} (baseline {completed["baseline"]}); '
              f'{"PASS" if all(verdict[arm]) and completed[arm] and not completed["baseline"] else "FAIL"}')


def control(a):
    d = load(a.attempts)
    for row, field in CONTROL:
        rid = f'{field}/{row}'
        runs = {arm: [r for r in d[(rid, arm)] if r['status'] == 'complete'] for arm in ('census', 'layout')}
        digests = {r['basis_sha256'] for rs in runs.values() for r in rs}
        ratio = bench_stats.independent_ratio([r['call_ns'] for r in runs['layout']],
                                              [r['call_ns'] for r in runs['census']], seed=1078)
        print(f'{rid:26s} layout/census wall={ratio.median:.3f} ({ratio.lo:.3f}-{ratio.hi:.3f}) '
              f'n={ratio.n}/{ratio.n_ref} digests={len(digests)}')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='cmd', required=True)
    i = sub.add_parser('inputs')
    i.add_argument('--study', required=True)
    i.add_argument('--out', required=True)
    m = sub.add_parser('manifest')
    m.add_argument('--binary', required=True)
    m.add_argument('--commit', required=True)
    m.add_argument('--inputs', required=True)
    m.add_argument('--job', choices=('timing', 'refused', 'control'), required=True)
    m.add_argument('--control-binary')
    m.add_argument('--control-commit')
    m.add_argument('--agent', default='synchronous-mapping-dove@feat/1078-row-layout')
    m.add_argument('--cpus', default='8-23')
    e = sub.add_parser('extract')
    e.add_argument('--job-dir', required=True)
    t = sub.add_parser('decide')
    t.add_argument('timing')
    t.add_argument('refused')
    c = sub.add_parser('control')
    c.add_argument('attempts')
    a = p.parse_args()
    {'inputs': inputs, 'manifest': manifest, 'extract': extract, 'decide': decide, 'control': control}[a.cmd](a)


if __name__ == '__main__':
    main()
