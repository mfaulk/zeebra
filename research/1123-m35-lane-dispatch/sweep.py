#!/usr/bin/env python3
"""#1123 (M35 E): lane dispatch by a per-batch entry threshold, development sweep (dev; decides nothing).

    sweep.py inputs --study BIN --out DIR
    sweep.py manifest --binary BIN --commit SHA --inputs DIR > manifest.json
    sweep.py heldout-inputs --study BIN --out DIR
    sweep.py heldout-manifest --binary BIN --commit SHA --inputs DIR > manifest.json
    sweep.py extract --job-dir DIR > attempts.jsonl
    sweep.py table attempts.jsonl

Every arm runs shipping Adaptive at one worker:
- `field`: no lane;
- `lane`: `--lane16`, the lane forced on every batch;
- `tN`: `--lane16 --lane-min-entries N`.

Rows are #945's dense regime rows and its specification controls at GF(31) and GF(32003), plus
Noon-6 at GF(32003) (#269's regression, #1123's review note). Rows come from
`sig_f4_study --generate` at the measured commit.
"""
import argparse
import json
import statistics
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research' / '1200-m35-publication'))
import campaign  # noqa: E402

ROWS = ([(f'mq-dense-{n}-s{n}', f, 'regime') for n in (15, 18) for f in ('gf31', 'gf32003')]
        + [(r, f, 'control') for r in ('katsura-8', 'cyclic-6', 'mq-random-10-s10') for f in ('gf31', 'gf32003')]
        + [('noon-6', 'gf32003', 'control')])
THRESHOLDS = (1_000, 10_000, 100_000, 1_000_000)
# Frozen on #1123 from the development sweep e4f4f895fe63, before any held-out row existed.
FROZEN = 100_000
HELD_OUT = ([(f'mq-dense-16-s16', f, 'target') for f in ('gf31', 'gf32003', 'gf7681')]
            + [('mq-dense-18-s18', 'gf7681', 'target')]
            + [(r, f, 'control') for r in ('katsura-7', 'katsura-9', 'cyclic-7', 'noon-7', 'noon-8', 'eco-8',
                                          'mq-random-9-s9', 'mq-random-11-s11') for f in ('gf32003', 'gf7681')]
            + [(r, f, 'specification') for r in ('katsura-8', 'cyclic-6') for f in ('gf31', 'gf32003')]
            + [('noon-6', 'gf32003', 'specification')])
CAP_S = 300


def generated(row, field, role, study, split='development'):
    argv = [study, '--field', field, '--name', row, '--generate', '--engine', 'f4', '--input-only']
    case = json.loads(subprocess.check_output(argv, text=True))
    p = int(case['modulus'])
    names = case['variables']
    equations = []
    for text in case['generators']:
        terms = {k: c % p for k, c in campaign.public.parse_integer_polynomial(text, names).items() if c % p}
        equations.append([{'exponents': list(k), 'coefficient': [str(c)]} for k, c in sorted(terms.items())])
    lineage = f'm35-e/{row.rsplit("-", 2)[0] if row.startswith("mq-") else row.rsplit("-", 1)[0]}'
    rec = {'schema': 'corpus-instance-v1', 'id': f'{row}@{field}',
           'field': {'characteristic': str(p), 'extension_degree': 1, 'defining_polynomial': []},
           'variables': names, 'order': 'grevlex', 'task': 'T-GB', 'equations': equations,
           'generator': {'call': [Path(study).name, *argv[1:]], 'zeebra_input_digest': case['digest']},
           'lineage': {'family_id': lineage, 'formulation_id': f'{lineage}/{row}', 'split': split, 'role': role}}
    lineage_tools = campaign.panel_catalog.corpus_lineage
    rec['lineage']['support_id'] = lineage_tools.support_digest(rec)
    rec['normalized_input_digest'] = lineage_tools.input_digest(rec)
    return rec


def write_inputs(rows, study, out, split):
    for row, field, role in rows:
        record = generated(row, field, role, study, split)
        d = Path(out, field, row)
        d.mkdir(parents=True, exist_ok=True)
        (d / 'record.json').write_text('[\n' + json.dumps(record, sort_keys=True) + '\n]\n')
        base = dict(variables=record['variables'], modulus=int(record['field']['characteristic']),
                    order='grevlex', workers=1, generators=campaign.public.generator_texts(record),
                    wall_ns=CAP_S * 10**9, rss_bytes=campaign.CAP_BYTES)
        (d / 'grobx.json').write_text(json.dumps(dict(base, mode='raw')))
        print(record['id'], len(record['variables']), len(record['equations']), file=sys.stderr)


def arms_flags(thresholds):
    return {'field': [], 'lane': ['--lane16'],
            **{f't{t}': ['--lane16', '--lane-min-entries', str(t)] for t in thresholds}}


def zeebra_arms(binary, commit, flags_by_name):
    zeebra = campaign.zeebra_arm('adaptive', binary, commit)
    return [dict(zeebra, name=name, argv=['--catalog', '{inputs[record]}', '--id', '{id}', '--engine', 'adaptive',
                                          *flags, '--workers', '1', '--wall-s', str(CAP_S)])
            for name, flags in flags_by_name.items()]


def instances(rows, inputs_dir, files=('record',)):
    out = []
    for row, field, _ in rows:
        d = Path(inputs_dir, field, row)
        out.append(dict(name=f'{field}/{row}', params=dict(id=f'{row}@{field}'),
                        inputs={k: dict(path=str(d / f'{k}.json'), sha256=campaign.sha(d / f'{k}.json'))
                                for k in files}))
    return out


def inputs(a):
    write_inputs(ROWS, a.study, a.out, 'development')


def heldout_inputs(a):
    write_inputs(HELD_OUT, a.study, a.out, 'held-out')


def heldout_manifest(a):
    arms = zeebra_arms(a.binary, a.commit, {'field': [], 'rule': ['--lane16', '--lane-min-entries', str(FROZEN)],
                                            'lane': ['--lane16']})
    m = dict(schema='bench-job-manifest-v1', mode='publication',
             context=dict(issue=1123, agent=a.agent, job='held-out-read'),
             arms=arms, instances=instances(HELD_OUT, a.inputs),
             run=dict(workers=[1], cpus=a.cpus, repetitions=9, interleave='rotate', seeds=[0], retries=0,
                      mode_wait_seconds=3600,
                      limits=dict(wall_seconds=CAP_S + 30, kill_after_seconds=30, rss_bytes=campaign.CAP_BYTES,
                                  live_bytes=None)))
    json.dump(m, sys.stdout, indent=1)
    print()


def manifest(a):
    m = dict(schema='bench-job-manifest-v1', mode='dev', context=dict(issue=1123, agent=a.agent, job='threshold-sweep'),
             arms=zeebra_arms(a.binary, a.commit, arms_flags(THRESHOLDS)), instances=instances(ROWS, a.inputs),
             run=dict(workers=[1], cpus=a.cpus, repetitions=3, interleave='rotate', seeds=[0], retries=0,
                      limits=dict(wall_seconds=CAP_S + 30, kill_after_seconds=30, rss_bytes=campaign.CAP_BYTES,
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
            if cell['arm'] == 'grobx':
                rec.update(status='complete' if reply.get('basis') and not reply.get('stopped') else 'stopped',
                           call_ns=reply.get('solve_ns'))
            else:
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
    names = list(arms_flags(THRESHOLDS))
    for row, field, role in ROWS:
        rid = f'{field}/{row}'
        med = {}
        for arm in names:
            rs = d.get((rid, arm), [])
            if rs and all(r['status'] == 'complete' for r in rs):
                med[arm] = statistics.median(r['call_ns'] for r in rs) / 1e9
        f = med.get('field')
        digests = {r['basis_sha256'] for arm in names for r in d.get((rid, arm), []) if r['status'] == 'complete'}
        routes = sorted({str(r.get('route')) for r in d.get((rid, 'field'), [])})
        cells = ' '.join(f'{arm}={med[arm] / f:.3f}' if arm in med and f else f'{arm}=-' for arm in names[1:])
        print(f'{rid:28s} [{role}] field={f and round(f, 4)} s  {cells}  digests={len(digests)} route={routes}')


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
    m.add_argument('--agent', default='synchronous-mapping-dove@feat/1123-lane-dispatch')
    m.add_argument('--cpus', default='8-23')
    hi = sub.add_parser('heldout-inputs')
    hi.add_argument('--study', required=True)
    hi.add_argument('--out', required=True)
    hm = sub.add_parser('heldout-manifest')
    hm.add_argument('--binary', required=True)
    hm.add_argument('--commit', required=True)
    hm.add_argument('--inputs', required=True)
    hm.add_argument('--agent', default='synchronous-mapping-dove@feat/1123-lane-dispatch')
    hm.add_argument('--cpus', default='8-23')
    e = sub.add_parser('extract')
    e.add_argument('--job-dir', required=True)
    t = sub.add_parser('table')
    t.add_argument('attempts')
    a = p.parse_args()
    {'inputs': inputs, 'manifest': manifest, 'heldout-inputs': heldout_inputs, 'heldout-manifest': heldout_manifest,
     'extract': extract, 'table': table}[a.cmd](a)


if __name__ == '__main__':
    main()
