#!/usr/bin/env python3
"""#1183 (M35 E2) deciding read for the 31-bit lane (plan §9.8), as declared on #1183.

    decide.py inputs --qualify BIN --panel DIR --out DIR
    decide.py manifest --binary BIN --commit SHA --grobx BIN --inputs DIR > manifest.json
    decide.py extract --job-dir DIR --inputs DIR > attempts.jsonl

Publication mode, one worker, 9 interleaved repetitions. On the 31-bit rows: shipping Adaptive,
Adaptive with `--lane31`, and grobx's default. On the wide rows: Adaptive alone, which gives the
2^31/2^64 time ratio.
"""
import argparse
import json
import shutil
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research' / '1200-m35-publication'))
import campaign  # noqa: E402

# (row, narrow field, wide field, role). Size 12 is the development scale; 13 is held out.
FAMILIES = [('gen-chandrasekhar-h', 'p31', 'p64'), ('katsura', 'm31', 'w59'), ('eco', 'm31', 'w59')]
ROWS = ([(f'{f}-12', n, 'regime') for f, n, _ in FAMILIES]
        + [(f'{f}-12', 'babybear', 'reproduction') for f, _, _ in FAMILIES]
        + [(f'{f}-13', n, 'held-out scale') for f, n, _ in FAMILIES]
        + [(f'{f}-{s}', w, 'wide') for f, _, w in FAMILIES for s in (12, 13)])
NARROW = {'p31', 'm31', 'babybear', 'koalabear'}
CAP_S = 300


def key(row, field):
    return f'{field}/{row}'


def inputs(a):
    for row, field, role in ROWS:
        src, dst = Path(a.panel, key(row, field)), Path(a.out, key(row, field))
        dst.mkdir(parents=True, exist_ok=True)
        if (src / 'record.json').exists():
            for name in ('record.json', 'grobx.json'):
                shutil.copyfile(src / name, dst / name)
            print(f'{row}@{field} from the panel', file=sys.stderr)
            continue
        family = dict(lineage=f'm35-e2/{row.rsplit("-", 1)[0]}', split='held-out', role=role)
        record = campaign.panel_catalog.generated(family, row, field, a.qualify, None)
        (dst / 'record.json').write_text('[\n' + json.dumps(record, sort_keys=True) + '\n]\n')
        base = dict(variables=record['variables'], modulus=int(record['field']['characteristic']),
                    order='grevlex', workers=1, generators=campaign.public.generator_texts(record),
                    wall_ns=CAP_S * 10**9, rss_bytes=campaign.CAP_BYTES)
        (dst / 'grobx.json').write_text(json.dumps(dict(base, mode='raw')))
        print(f'{row}@{field} generated', file=sys.stderr)


def manifest(a):
    narrow = [key(r, f) for r, f, _ in ROWS if f in NARROW]
    zeebra = campaign.zeebra_arm('adaptive', a.binary, a.commit)
    arms = [dict(zeebra, name='adaptive',
                 argv=['--catalog', '{inputs[record]}', '--id', '{id}', '--engine', 'adaptive', '--workers', '1',
                       '--wall-s', str(CAP_S)]),
            dict(zeebra, name='lane', instances=narrow,
                 argv=['--catalog', '{inputs[record]}', '--id', '{id}', '--engine', 'adaptive', '--lane31',
                       '--workers', '1', '--wall-s', str(CAP_S)]),
            dict(campaign.grobx_arm('grobx', a.grobx, 'grobx'), instances=narrow)]
    instances = []
    for row, field, _ in ROWS:
        d = Path(a.inputs, key(row, field))
        files = dict(record='record.json', grobx='grobx.json')
        instances.append(dict(name=key(row, field), params=dict(id=f'{row}@{field}'),
                              inputs={k: dict(path=str(d / v), sha256=campaign.sha(d / v)) for k, v in files.items()}))
    m = dict(schema='bench-job-manifest-v1', mode='publication',
             context=dict(issue=1183, agent=a.agent, job='deciding-read'), arms=arms, instances=instances,
             run=dict(workers=[1], cpus=a.cpus, repetitions=9, interleave='rotate', seeds=[0], retries=0,
                      mode_wait_seconds=3600,
                      limits=dict(wall_seconds=CAP_S + 30, kill_after_seconds=30, rss_bytes=campaign.CAP_BYTES,
                                  live_bytes=None, output_bytes=campaign.OUTPUT_BYTES)))
    json.dump(m, sys.stdout, indent=1)
    print()


def extract(a):
    roles = {key(r, f): role for r, f, role in ROWS}
    state = campaign.aj.load(Path(a.job_dir) / 'journal')
    session = (state['stop'] or {}).get('contamination') or {}
    for att in state['attempts']:
        cell, md = att['cell'], att['metadata']
        record = json.loads(Path(a.inputs, cell['instance'], 'record.json').read_text())[0]
        verdict = (md.get('contamination') or {}).get('verdict')
        rec = dict(id=record['id'], role=roles[cell['instance']], arm=cell['arm'], rep=cell['rep'],
                   harness_status=att['status'], peak_rss_bytes=md['observed_peak_rss_bytes'],
                   contaminated=bool(verdict and verdict['contaminated'])
                   or md['attempt_id'] in session.get('flagged', {}))
        try:
            reply = json.loads(att['stdout'].decode(errors='replace').strip().splitlines()[-1])
        except (ValueError, IndexError):
            print(json.dumps(dict(rec, status='unparsed'), sort_keys=True))
            continue
        if cell['arm'] == 'grobx':
            done = not reply.get('stopped') and reply.get('basis')
            basis = campaign.public.basis_digest(
                record, campaign.public.parse_grobx_basis(reply['basis'], record['variables'])) if done else None
            rec.update(status='complete' if done else 'stopped', call_ns=reply.get('solve_ns'), basis_sha256=basis,
                       error=reply.get('stopped'))
        else:
            rec.update(status=reply.get('status'), call_ns=reply.get('call_ns'), route=reply.get('route'),
                       basis_sha256=reply.get('basis_sha256'), error=reply.get('error'))
        print(json.dumps(rec, sort_keys=True))


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='cmd', required=True)
    i = sub.add_parser('inputs')
    i.add_argument('--qualify', required=True)
    i.add_argument('--panel', required=True, help="#1200's per-record input directories")
    i.add_argument('--out', required=True)
    m = sub.add_parser('manifest')
    m.add_argument('--binary', required=True)
    m.add_argument('--commit', required=True)
    m.add_argument('--grobx', required=True)
    m.add_argument('--inputs', required=True)
    m.add_argument('--agent', default='synchronous-mapping-dove@feat/1183-lane31-bench')
    m.add_argument('--cpus', default='8-23')
    e = sub.add_parser('extract')
    e.add_argument('--job-dir', required=True)
    e.add_argument('--inputs', required=True)
    a = p.parse_args()
    {'inputs': inputs, 'manifest': manifest, 'extract': extract}[a.cmd](a)


if __name__ == '__main__':
    main()
