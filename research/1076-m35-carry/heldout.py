#!/usr/bin/env python3
"""#1076's held-out read for the frozen lead-fall carry rule (plan §9.3), as declared on #1076.

    heldout.py inputs --qualify BIN --out DIR
    heldout.py manifest --binary BIN --commit SHA --grobx BIN --inputs DIR > manifest.json
    heldout.py extract --job-dir DIR --inputs DIR > attempts.jsonl

Publication mode, one worker, 9 interleaved repetitions. Arms: shipping F4 and Adaptive, the forced
signature engine, `rule` (the signature engine with `--carry continue@fall`) and grobx's default.
"""
import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research' / '1200-m35-publication'))
import campaign  # noqa: E402

# (row, field, role): the two declared scales, the fresh family, then §9.1's controls.
ROWS = [('cyclic-7', 'goldilocks', 'scale'), ('cyclic-8', 'goldilocks', 'scale'),
        ('reimer-6', 'm31', 'fresh'), ('reimer-7', 'm31', 'fresh'),
        ('eco-12', 'goldilocks', 'control'), ('katsura-12', 'goldilocks', 'control')]
ARMS = {'f4': ['--engine', 'f4'], 'adaptive': ['--engine', 'adaptive'], 'sig': ['--engine', 'sig'],
        'rule': ['--engine', 'sig', '--carry', 'continue@fall']}
CAP_S = 300


def inputs(a):
    for row, field, role in ROWS:
        family = dict(lineage=f'm35-c/{row.rsplit("-", 1)[0]}', split='held-out', role=role)
        record = campaign.panel_catalog.generated(family, row, field, a.qualify, None)
        d = Path(a.out, f'{field}/{row}')
        d.mkdir(parents=True, exist_ok=True)
        (d / 'record.json').write_text('[\n' + json.dumps(record, sort_keys=True) + '\n]\n')
        base = dict(variables=record['variables'], modulus=int(record['field']['characteristic']),
                    order='grevlex', workers=1, generators=campaign.public.generator_texts(record),
                    wall_ns=CAP_S * 10**9, rss_bytes=campaign.CAP_BYTES)
        (d / 'grobx.json').write_text(json.dumps(dict(base, mode='raw')))
        print(record['id'], len(record['variables']), len(record['equations']), file=sys.stderr)


def manifest(a):
    zeebra = campaign.zeebra_arm('adaptive', a.binary, a.commit)
    arms = [dict(zeebra, name=name, argv=['--catalog', '{inputs[record]}', '--id', '{id}', *flags,
                                          '--workers', '1', '--wall-s', str(CAP_S)])
            for name, flags in ARMS.items()]
    arms.append(campaign.grobx_arm('grobx', a.grobx, 'grobx'))
    instances = []
    for row, field, _ in ROWS:
        d = Path(a.inputs, field, row)
        files = dict(record='record.json', grobx='grobx.json')
        instances.append(dict(name=f'{field}/{row}', params=dict(id=f'{row}@{field}'),
                              inputs={k: dict(path=str(d / v), sha256=campaign.sha(d / v)) for k, v in files.items()}))
    m = dict(schema='bench-job-manifest-v1', mode='publication',
             context=dict(issue=1076, agent=a.agent, job='held-out-read'), arms=arms, instances=instances,
             run=dict(workers=[1], cpus=a.cpus, repetitions=9, interleave='rotate', seeds=[0], retries=0,
                      mode_wait_seconds=3600,
                      limits=dict(wall_seconds=CAP_S + 30, kill_after_seconds=30, rss_bytes=campaign.CAP_BYTES,
                                  live_bytes=None, output_bytes=campaign.OUTPUT_BYTES)))
    json.dump(m, sys.stdout, indent=1)
    print()


def extract(a):
    roles = {f'{field}/{row}': role for row, field, role in ROWS}
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
                       basis_sha256=reply.get('basis_sha256'), error=reply.get('error'), carry=reply.get('carry'))
        print(json.dumps(rec, sort_keys=True))


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='cmd', required=True)
    i = sub.add_parser('inputs')
    i.add_argument('--qualify', required=True)
    i.add_argument('--out', required=True)
    m = sub.add_parser('manifest')
    m.add_argument('--binary', required=True)
    m.add_argument('--commit', required=True)
    m.add_argument('--grobx', required=True)
    m.add_argument('--inputs', required=True)
    m.add_argument('--agent', default='synchronous-mapping-dove@feat/1076-lead-fall')
    m.add_argument('--cpus', default='8-23')
    e = sub.add_parser('extract')
    e.add_argument('--job-dir', required=True)
    e.add_argument('--inputs', required=True)
    a = p.parse_args()
    {'inputs': inputs, 'manifest': manifest, 'extract': extract}[a.cmd](a)


if __name__ == '__main__':
    main()
