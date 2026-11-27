#!/usr/bin/env python3
"""#1200: the publication-mode read of #1162's priced manifest, as `tools/bench-job` jobs.

    campaign.py inputs   --catalog catalog.json --out DIR              # one directory per record
    campaign.py manifest --inputs DIR --matrix BIN --grobx BIN --dev probe.jsonl [--dev ...] \
                         --job primary-9|primary-3|frontier|exact [--ids a@f,b@f] > manifest.json
    campaign.py extract  --job-dir /buildcache/bench-jobs/<id> --inputs DIR --out records.jsonl

The repetition rule is #1162's price (`summarize.py`): 9 attempts when an arm's development time
is under 60 s, 3 above, 1 on a frontier row. `bench-job` has one repetition count per job, so the
primary panel is two jobs, `primary-9` and `primary-3`, each arm restricted to the instances its
development time puts in that job. Each Zeebra arm solves a one-record catalog with
`m34_matrix --catalog`, and grobx the request built from the same record, so both solve
byte-identical inputs.
"""
import argparse
import gzip
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
sys.path.insert(0, str(ROOT / 'tools' / 'external'))
sys.path.insert(0, str(ROOT / 'research' / '1162-m35-baseline'))
import attempt_journal as aj  # noqa: E402
import catalog as panel_catalog  # noqa: E402
import m34_public_corpus as public  # noqa: E402
import summarize  # noqa: E402

# grobx prints its basis (137 MB gzipped for Chandrasekhar-H 13 at p64); the 1 GiB default stopped
# the first primary-9 job after 189 of 1161 attempts.
OUTPUT_BYTES = 32 << 30
CAP_S = 300
CAP_BYTES = 16 * 2**30
GROBX = dict(commit='8005a2a1670a7264617a6f49eeb2618d7fa21701',
             comparand='grobx 0.155.1 (M33 pin): research/m33-baseline/grobx-pin.sh, pins.json')
ZEEBRA_ARMS = {'f4': 'f4', 'adaptive': 'adaptive'}


def key(record_id):
    row, field = record_id.split('@')
    return f'{field}/{row}'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def inputs(args):
    for record in json.loads(Path(args.catalog).read_text()):
        d = Path(args.out, key(record['id']))
        d.mkdir(parents=True, exist_ok=True)
        (d / 'record.json').write_text('[\n' + json.dumps(record, sort_keys=True) + '\n]\n')
        base = dict(variables=record['variables'], modulus=int(record['field']['characteristic']),
                    order='grevlex', workers=1, generators=public.generator_texts(record),
                    wall_ns=CAP_S * 10**9, rss_bytes=CAP_BYTES)
        (d / 'grobx.json').write_text(json.dumps(dict(base, mode='raw')))
        (d / 'grobx-certified.json').write_text(json.dumps(dict(base, mode='certified')))
    print(f'wrote {Path(args.out)}', file=sys.stderr)


def plan(dev_rows):
    """(record id, arm) -> job, from the panel and the development times."""
    panel = json.loads((ROOT / 'research/1162-m35-baseline/panel.json').read_text())
    cells = {}
    for family, row, field in panel_catalog.panel_rows(panel):
        rid = f'{row}@{field}'
        for arm in summarize.PRIMARY_ARMS:
            if row in family.get('frontier', []):
                cells[rid, arm] = 'frontier'
            else:
                s = summarize.attempt_seconds(dev_rows.get(rid, {}).get(arm), CAP_S)
                cells[rid, arm] = f'primary-{summarize.repetitions(s)}'
    for rid in summarize.EXACT_ROWS:
        cells[rid, 'grobx-certified'] = 'exact'
    return cells


def zeebra_arm(name, matrix, commit):
    return dict(name=name, commit=commit, binary=str(matrix), sha256=sha(matrix),
                build=dict(profile='release',
                           flags='--features research-sigf4; fat LTO, codegen-units 1 (Cargo.toml); '
                                 '-C target-cpu=x86-64-v3 (.cargo/config.toml); RUSTC_WRAPPER="" CARGO_INCREMENTAL=0',
                           recipe=f'git archive {commit} | tar -x; cargo build --release --features research-sigf4 '
                                  '--example m34_matrix'),
                argv=['--catalog', '{inputs[record]}', '--id', '{id}', '--engine', ZEEBRA_ARMS[name],
                      '--workers', '1', '--wall-s', str(CAP_S)],
                library='zeebra')


def grobx_arm(name, binary, request):
    return dict(name=name, commit=GROBX['commit'], binary=str(binary), sha256=sha(binary),
                build=dict(profile='release', flags='as provisioned (pins.json)', recipe=GROBX['comparand'],
                           comparand=GROBX['comparand']),
                argv=[f'{{inputs[{request}]}}'], library=name)


def manifest(args):
    dev = {}
    for path in args.dev:
        for rid, arms in summarize.load(path).items():
            dev.setdefault(rid, {}).update(arms)
    cells = {c: j for c, j in plan(dev).items() if j == args.job}
    if args.ids:
        cells = {c: j for c, j in cells.items() if c[0] in args.ids.split(',')}
    by_arm = {}
    for rid, arm in sorted(cells):
        by_arm.setdefault(arm, []).append(key(rid))
    arms = []
    for arm, names in by_arm.items():
        if arm in ZEEBRA_ARMS:
            a = zeebra_arm(arm, args.matrix, args.commit)
        else:
            a = grobx_arm(arm, args.grobx, 'grobx' if arm == 'grobx' else 'grobx_certified')
        a['instances'] = names
        arms.append(a)
    instances = []
    for rid in sorted({rid for rid, _ in cells}):
        d = Path(args.inputs, key(rid))
        files = dict(record='record.json', grobx='grobx.json', grobx_certified='grobx-certified.json')
        instances.append(dict(name=key(rid), params=dict(id=rid),
                              inputs={k: dict(path=str(d / f), sha256=sha(d / f)) for k, f in files.items()}))
    reps = dict(primary_9=9, primary_3=3, frontier=1, exact=3)[args.job.replace('-', '_')]
    m = dict(schema='bench-job-manifest-v1', mode=args.mode,
             context=dict(issue=1200, agent=args.agent, job=args.job),
             arms=arms, instances=instances,
             run=dict(workers=[1], cpus=args.cpus, repetitions=reps, interleave='rotate', seeds=[0], retries=0,
                      mode_wait_seconds=3600,
                      limits=dict(wall_seconds=CAP_S + 30, kill_after_seconds=30, rss_bytes=CAP_BYTES,
                                  live_bytes=None, output_bytes=OUTPUT_BYTES)))
    json.dump(m, sys.stdout, indent=1)
    print()
    print(f'{args.job}: {len(instances)} instances, '
          f'{sum(len(a["instances"]) for a in arms) * reps} attempts', file=sys.stderr)


def digest(arm, stdout, record):
    text = stdout.decode(errors='replace')
    try:
        reply = json.loads(text.strip().splitlines()[-1])
    except (ValueError, IndexError):
        return None, None
    if arm in ZEEBRA_ARMS:
        return reply.get('status'), reply.get('basis_sha256') if reply.get('status') == 'complete' else None
    if reply.get('stopped') or not reply.get('basis'):
        return 'stopped', None
    return 'complete', public.basis_digest(record, public.parse_grobx_basis(reply['basis'], record['variables']))


def extract(args):
    state = aj.load(Path(args.job_dir) / 'journal')
    out = []
    session = (state['stop'] or {}).get('contamination') or {}
    for a in state['attempts']:
        cell, md = a['cell'], a['metadata']
        field, row = cell['instance'].split('/')
        rid = f'{row}@{field}'
        record = json.loads(Path(args.inputs, cell['instance'], 'record.json').read_text())[0]
        verdict = (md.get('contamination') or {}).get('verdict')
        status, basis = digest(cell['arm'], a['stdout'], record) if a['status'] == 'ok' else (a['status'], None)
        rec = dict(id=rid, arm=cell['arm'], rep=cell['rep'], job=state['header']['bench_job']['job_id'],
                   attempt=md['attempt_id'], harness_status=a['status'], status=status,
                   process_wall_ns=md['process_wall_ns'], peak_rss_bytes=md['observed_peak_rss_bytes'],
                   cpus=md['cpus'], basis_sha256=basis,
                   contaminated=bool(verdict and verdict['contaminated'])
                   or md['attempt_id'] in session.get('flagged', {}))
        if cell['arm'] in ZEEBRA_ARMS and a['status'] == 'ok':
            reply = json.loads(a['stdout'].decode().strip().splitlines()[-1])
            rec.update(call_ns=reply.get('call_ns'), route=reply.get('route'), error=reply.get('error'))
        else:
            try:
                reply = json.loads(a['stdout'].decode().strip().splitlines()[-1])
                rec.update(call_ns=reply.get('solve_ns'), error=reply.get('stopped'))
            except (ValueError, IndexError, AttributeError):
                pass
        out.append(rec)
    payload = ''.join(json.dumps(r, sort_keys=True) + '\n' for r in out)
    path = Path(args.out)
    path.write_bytes(gzip.compress(payload.encode(), mtime=0) if path.suffix == '.gz' else payload.encode())
    print(f'{len(out)} attempts -> {path}', file=sys.stderr)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='command', required=True)
    i = sub.add_parser('inputs')
    i.add_argument('--catalog', required=True)
    i.add_argument('--out', required=True)
    m = sub.add_parser('manifest')
    m.add_argument('--inputs', required=True)
    m.add_argument('--matrix', required=True)
    m.add_argument('--commit', required=True, help='the commit m34_matrix was built from')
    m.add_argument('--grobx', required=True)
    m.add_argument('--dev', action='append', required=True, help='development probe records (repeatable)')
    m.add_argument('--job', required=True, choices=('primary-9', 'primary-3', 'frontier', 'exact'))
    m.add_argument('--mode', default='publication', choices=('dev', 'publication'))
    m.add_argument('--cpus', default='8-23')
    m.add_argument('--agent', default=subprocess.run([str(ROOT / 'scripts/agent/zb-claim.sh'), 'id'],
                                                     capture_output=True, text=True).stdout.strip())
    m.add_argument('--ids')
    e = sub.add_parser('extract')
    e.add_argument('--job-dir', required=True)
    e.add_argument('--inputs', required=True)
    e.add_argument('--out', required=True)
    args = p.parse_args()
    dict(inputs=inputs, manifest=manifest, extract=extract)[args.command](args)


if __name__ == '__main__':
    main()
