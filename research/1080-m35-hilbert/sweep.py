#!/usr/bin/env python3
"""#1080: B's development slack sweep (dev mode; not a deciding read).

    sweep.py catalog --qualify BIN --study BIN --out DIR
    sweep.py manifest --binary BIN --commit SHA --inputs DIR > manifest.json
    sweep.py extract --job-dir DIR > sweep.jsonl

Shipping F4 with `HilbertSelection::CertifiedZeros { slack }` forced on, at slack 0, 2, 8 and 32,
against the same engine with Hilbert selection off, on the exposed development regime rows and
#1080's four adverse controls. Controls forced on are diagnostic (plan §9.1): they specify the
eligibility rule and decide nothing. Held-out rows are generated only after the rule is frozen.
"""
import argparse
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research/1162-m35-baseline'))
sys.path.insert(0, str(ROOT / 'tools'))
sys.path.insert(0, str(ROOT / 'tools/external'))
import catalog as baseline  # noqa: E402

# (row, field, role). `mq-full-N-s0` is the frozen wide-corpus `mq-random-N` (StdRng, full support).
ROWS = [(f'mq-full-{n}-s0', f, 'regime') for n in (10, 11, 12) for f in ('goldilocks', 'wide64')] + [
    ('mq-dense-15-s15', 'm31', 'regime'), ('mq-dense-18-s18', 'm31', 'regime'),
    ('eco-12', 'w59', 'control'), ('katsura-11', 'm31', 'control'),
    ('mq-random-10-s10', 'm31', 'control'), ('cyclic-8', 'm31', 'control')]
SLACKS = (0, 2, 8, 32)
CAP_S = 300


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def key(row, field):
    return f'{field}/{row}'


def catalog(a):
    for row, field, role in ROWS:
        family = dict(lineage=f'm35-b/{row.rsplit("-", 2)[0] if row.startswith("mq-") else row.rsplit("-", 1)[0]}',
                      split='development', role=role)
        rec = baseline.generated(family, row, field, a.qualify, a.study)
        d = Path(a.out, key(row, field))
        d.mkdir(parents=True, exist_ok=True)
        (d / 'record.json').write_text(json.dumps([rec]) + '\n')
        print(rec['id'], len(rec['variables']), len(rec['equations']), file=sys.stderr)


def manifest(a):
    build = dict(profile='release', recipe=f'git archive {a.commit} | tar -x; cargo build --release '
                 '--features research-sigf4 --example m34_matrix',
                 flags='--features research-sigf4; fat LTO, codegen-units 1 (Cargo.toml); -C target-cpu=x86-64-v3 '
                 '(.cargo/config.toml); RUSTC_WRAPPER="" CARGO_INCREMENTAL=0')
    modes = {'off': 'off', **{f'cz{s}': f'certified-zeros+{s}' for s in SLACKS}}
    arms = [dict(name=name, commit=a.commit, binary=a.binary, sha256=sha(a.binary), build=build, library='zeebra',
                 argv=['--catalog', '{inputs[record]}', '--id', '{id}', '--engine', 'f4', '--hilbert', mode,
                       '--workers', '1', '--wall-s', str(CAP_S)])
            for name, mode in modes.items()]
    instances = [dict(name=key(r, f), params=dict(id=f'{r}@{f}'),
                      inputs=dict(record=dict(path=str(Path(a.inputs, key(r, f), 'record.json')),
                                              sha256=sha(Path(a.inputs, key(r, f), 'record.json')))))
                 for r, f, _ in ROWS]
    m = dict(schema='bench-job-manifest-v1', mode='dev', context=dict(issue=1080, agent=a.agent, job='slack-sweep'),
             arms=arms, instances=instances,
             run=dict(workers=[1], cpus=a.cpus, repetitions=3, interleave='rotate', seeds=[0], retries=0,
                      limits=dict(wall_seconds=CAP_S + 30, kill_after_seconds=30, rss_bytes=32 << 30,
                                  live_bytes=None)))
    json.dump(m, sys.stdout, indent=1)
    print()


def extract(a):
    import attempt_journal as aj
    state = aj.load(Path(a.job_dir) / 'journal')
    roles = {key(r, f): role for r, f, role in ROWS}
    for att in state['attempts']:
        c, md = att['cell'], att['metadata']
        rec = dict(id=c['instance'], arm=c['arm'], rep=c['rep'], role=roles.get(c['instance']),
                   harness_status=att['status'], peak_rss_bytes=md['observed_peak_rss_bytes'])
        try:
            reply = json.loads(att['stdout'].decode().strip().splitlines()[-1])
            rec.update(status=reply.get('status'), call_ns=reply.get('call_ns'),
                       basis_sha256=reply.get('basis_sha256'), error=reply.get('error'),
                       hilbert=reply.get('hilbert'))
        except (ValueError, IndexError):
            rec.update(status='unparsed')
        print(json.dumps(rec, sort_keys=True))


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='cmd', required=True)
    c = sub.add_parser('catalog')
    c.add_argument('--qualify', required=True)
    c.add_argument('--study', required=True)
    c.add_argument('--out', required=True)
    m = sub.add_parser('manifest')
    m.add_argument('--binary', required=True)
    m.add_argument('--commit', required=True)
    m.add_argument('--inputs', required=True)
    m.add_argument('--agent', default='synchronous-mapping-dove@research/1080-1076-harness')
    m.add_argument('--cpus', default='8-23')
    e = sub.add_parser('extract')
    e.add_argument('--job-dir', required=True)
    a = p.parse_args()
    dict(catalog=catalog, manifest=manifest, extract=extract)[a.cmd](a)


if __name__ == '__main__':
    main()
