#!/usr/bin/env python3
"""#1080's deciding read: the frozen rule on the held-out rows it admits (plan §9.2, Amendment 1).

    decide.py inputs --held-out DIR --out DIR
    decide.py manifest --binary BIN --commit SHA --grobx BIN --inputs DIR > manifest.json
    decide.py extract --job-dir DIR --inputs DIR > attempts.jsonl

Arms, one worker, publication mode, 9 interleaved repetitions:
- `adaptive`: shipping Adaptive, the best qualified Zeebra configuration on mq-full (#1080 dev job
  1f9557dc94f2);
- `rule`: the frozen rule's route on an admitted row, shipping F4 with certified zeros, slack 2;
- `grobx`: grobx's default, reported per §9.2 whether or not the internal gate passes.

Rows the rule declines take the unchanged route, so they need no measurement.
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research' / '1200-m35-publication'))
import campaign  # noqa: E402

ARMS = {'adaptive': ['--engine', 'adaptive'], 'rule': ['--engine', 'f4', '--hilbert', 'certified-zeros+2']}
CAP_S = 600


def admitted(held_out):
    out = subprocess.check_output([sys.executable, str(HERE / 'predicate.py'),
                                   *map(str, sorted(Path(held_out).glob('*/*/record.json')))], text=True)
    return [r['id'] for r in map(json.loads, out.splitlines()) if r['admitted']]


def inputs(a):
    for rid in admitted(a.held_out):
        record = json.loads(Path(a.held_out, campaign.key(rid), 'record.json').read_text())[0]
        d = Path(a.out, campaign.key(rid))
        d.mkdir(parents=True, exist_ok=True)
        (d / 'record.json').write_text('[\n' + json.dumps(record, sort_keys=True) + '\n]\n')
        base = dict(variables=record['variables'], modulus=int(record['field']['characteristic']),
                    order='grevlex', workers=1, generators=campaign.public.generator_texts(record),
                    wall_ns=CAP_S * 10**9, rss_bytes=campaign.CAP_BYTES)
        (d / 'grobx.json').write_text(json.dumps(dict(base, mode='raw')))
        print(rid, file=sys.stderr)


def manifest(a):
    zeebra = campaign.zeebra_arm('adaptive', a.binary, a.commit)
    arms = []
    for name, flags in ARMS.items():
        arm = dict(zeebra, name=name,
                   argv=['--catalog', '{inputs[record]}', '--id', '{id}', *flags, '--workers', '1',
                         '--wall-s', str(CAP_S)])
        arms.append(arm)
    arms.append(campaign.grobx_arm('grobx', a.grobx, 'grobx'))
    instances = []
    for d in sorted(Path(a.inputs).glob('*/*/record.json')):
        name = f'{d.parent.parent.name}/{d.parent.name}'
        files = dict(record='record.json', grobx='grobx.json')
        instances.append(dict(name=name, params=dict(id=f'{d.parent.name}@{d.parent.parent.name}'),
                              inputs={k: dict(path=str(d.parent / v), sha256=campaign.sha(d.parent / v))
                                      for k, v in files.items()}))
    m = dict(schema='bench-job-manifest-v1', mode='publication',
             context=dict(issue=1080, agent=a.agent, job='deciding-read'), arms=arms, instances=instances,
             run=dict(workers=[1], cpus=a.cpus, repetitions=9, interleave='rotate', seeds=[0], retries=0,
                      mode_wait_seconds=3600,
                      limits=dict(wall_seconds=CAP_S + 30, kill_after_seconds=30, rss_bytes=campaign.CAP_BYTES,
                                  live_bytes=None, output_bytes=campaign.OUTPUT_BYTES)))
    json.dump(m, sys.stdout, indent=1)
    print()


def extract(a):
    state = campaign.aj.load(Path(a.job_dir) / 'journal')
    session = (state['stop'] or {}).get('contamination') or {}
    for att in state['attempts']:
        cell, md = att['cell'], att['metadata']
        record = json.loads(Path(a.inputs, cell['instance'], 'record.json').read_text())[0]
        verdict = (md.get('contamination') or {}).get('verdict')
        rec = dict(id=record['id'], arm=cell['arm'], rep=cell['rep'], harness_status=att['status'],
                   peak_rss_bytes=md['observed_peak_rss_bytes'],
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
                       basis_sha256=reply.get('basis_sha256'), error=reply.get('error'), hilbert=reply.get('hilbert'))
        print(json.dumps(rec, sort_keys=True))


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='cmd', required=True)
    i = sub.add_parser('inputs')
    i.add_argument('--held-out', required=True)
    i.add_argument('--out', required=True)
    m = sub.add_parser('manifest')
    m.add_argument('--binary', required=True)
    m.add_argument('--commit', required=True)
    m.add_argument('--grobx', required=True)
    m.add_argument('--inputs', required=True)
    m.add_argument('--agent', default='synchronous-mapping-dove@feat/1076-carry-arms')
    m.add_argument('--cpus', default='8-23')
    e = sub.add_parser('extract')
    e.add_argument('--job-dir', required=True)
    e.add_argument('--inputs', required=True)
    a = p.parse_args()
    {'inputs': inputs, 'manifest': manifest, 'extract': extract}[a.cmd](a)


if __name__ == '__main__':
    main()
