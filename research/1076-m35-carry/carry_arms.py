#!/usr/bin/env python3
"""#1076 step 2: carry's intrinsic value, restart vs continue at fixed boundaries (plan §7.3).

    carry_arms.py manifest --binary PATH --commit SHA --inputs DIR > manifest.json
    carry_arms.py extract --job-dir DIR > attempts.jsonl
    carry_arms.py table attempts.jsonl

Arms per row: shipping Adaptive, shipping F4, the forced signature engine, and `restart@D` /
`continue@D` for each boundary D in BOUNDARIES. One worker, shipping limits. Dev mode: it
characterizes and decides nothing; no online boundary rule is fitted here.
"""
import argparse
import hashlib
import json
import statistics
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/external'))

# Cyclic-like development rows, then plan §7.3's controls: Eco switches early, Katsura stays.
# From unrecorded probes on the measured build: Cyclic-8's signature run ends past degree 20 and its
# continue cost falls sharply between boundaries 12 and 13; Eco-12 and Katsura-12 lose at every one.
BOUNDARIES = {
    'm31/cyclic-7': (8, 10, 11, 12, 14),
    'm31/cyclic-8': (8, 10, 11, 12, 13, 14, 16, 18),
    'm31/eco-12': (6, 8, 12),
    'm31/katsura-12': (6, 10),
}
CAP_S = 300
RSS = 64 << 30
BASE = {'adaptive': ['--engine', 'adaptive'], 'f4': ['--engine', 'f4'], 'sig': ['--engine', 'sig']}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def arm_flags():
    """Arm name -> (flags, rows it runs on; None for every row)."""
    arms = {name: (flags, None) for name, flags in BASE.items()}
    for d in sorted({d for ds in BOUNDARIES.values() for d in ds}):
        rows = [row for row, ds in BOUNDARIES.items() if d in ds]
        for mode in ('restart', 'continue'):
            arms[f'{mode}-{d}'] = (['--engine', 'sig', '--carry', f'{mode}@{d}'], rows)
    return arms


def manifest(a):
    build = dict(profile='release', recipe=f'git archive {a.commit} | tar -x; cargo build --release '
                 '--features research-sigf4 --example m34_matrix',
                 flags='--features research-sigf4; fat LTO, codegen-units 1 (Cargo.toml); -C target-cpu=x86-64-v3 '
                 '(.cargo/config.toml); RUSTC_WRAPPER="" CARGO_INCREMENTAL=0')
    digest = sha(a.binary)
    arms = []
    for name, (flags, rows) in arm_flags().items():
        arm = dict(name=name, commit=a.commit, binary=a.binary, sha256=digest, build=build, library='zeebra',
                   argv=['--catalog', '{inputs[record]}', '--id', '{id}', *flags, '--workers', '1',
                         '--wall-s', str(CAP_S)])
        if rows is not None:
            arm['instances'] = rows
        arms.append(arm)
    instances = []
    for row in BOUNDARIES:
        field, name = row.split('/')
        record = Path(a.inputs, row, 'record.json')
        instances.append(dict(name=row, params=dict(id=f'{name}@{field}'),
                              inputs=dict(record=dict(path=str(record), sha256=sha(record)))))
    m = dict(schema='bench-job-manifest-v1', mode='dev', context=dict(issue=1076, agent=a.agent, job='carry-arms'),
             arms=arms, instances=instances,
             run=dict(workers=[1], cpus=a.cpus, repetitions=a.repetitions, interleave='rotate', seeds=[0],
                      retries=0, limits=dict(wall_seconds=CAP_S + 30, kill_after_seconds=30, rss_bytes=RSS,
                                             live_bytes=None)))
    json.dump(m, sys.stdout, indent=1)
    print()


def extract(a):
    import attempt_journal as aj
    state = aj.load(Path(a.job_dir) / 'journal')
    for att in state['attempts']:
        c, md = att['cell'], att['metadata']
        rec = dict(id=c['instance'], arm=c['arm'], rep=c['rep'], harness_status=att['status'],
                   peak_rss_bytes=md['observed_peak_rss_bytes'], contaminated=bool(((md.get('contamination') or {}).get('verdict') or {}).get('contaminated')))
        try:
            reply = json.loads(att['stdout'].decode().strip().splitlines()[-1])
            rec.update(status=reply.get('status'), call_ns=reply.get('call_ns'),
                       basis_sha256=reply.get('basis_sha256'), error=reply.get('error'), carry=reply.get('carry'))
        except (ValueError, IndexError):
            rec.update(status='unparsed')
        print(json.dumps(rec, sort_keys=True))


def table(a):
    rows = defaultdict(list)
    with open(a.attempts) as f:
        for line in f:
            r = json.loads(line)
            if not r['contaminated']:
                rows[(r['id'], r['arm'])].append(r)
    for rid in BOUNDARIES:
        arms = sorted({arm for (i, arm) in rows if i == rid}, key=lambda s: (('-' in s), s.split('-')[-1].zfill(3), s))
        best = min((statistics.median(r['call_ns'] for r in rows[(rid, x)]) for x in ('f4', 'adaptive')
                    if all(r['status'] == 'complete' for r in rows[(rid, x)])), default=None)
        print(f'\n{rid}  best shipping = {best / 1e9:.3f} s' if best else f'\n{rid}')
        for arm in arms:
            rs = rows[(rid, arm)]
            done = [r for r in rs if r['status'] == 'complete']
            if len(done) < len(rs):
                print(f'  {arm:12s} {len(rs) - len(done)} of {len(rs)} not complete: {rs[0]["error"]}')
                continue
            t = statistics.median(r['call_ns'] for r in done)
            c = done[0].get('carry') or {}
            extra = ''
            if c:
                extra = (f'  stop@{c["degree"]} seed={c["seed"]} sig_elems={c["signature_elements"]} '
                         f'prefix={statistics.median(r["carry"]["prefix_ns"] for r in done) / 1e9:.3f}s '
                         f'f4_batches={c["conventional_batches"]}')
            digests = {r['basis_sha256'] for r in done}
            print(f'  {arm:12s} {t / 1e9:8.3f} s  x{t / best if best else float("nan"):5.2f}'
                  f'{"" if len(digests) == 1 else "  DIGESTS DIFFER"}{extra}')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='cmd', required=True)
    m = sub.add_parser('manifest')
    m.add_argument('--binary', required=True)
    m.add_argument('--commit', required=True)
    m.add_argument('--inputs', required=True)
    m.add_argument('--agent', default='synchronous-mapping-dove@feat/1076-carry-arms')
    m.add_argument('--cpus', default='8-23')
    m.add_argument('--repetitions', type=int, default=3)
    e = sub.add_parser('extract')
    e.add_argument('--job-dir', required=True)
    t = sub.add_parser('table')
    t.add_argument('attempts')
    a = p.parse_args()
    {'manifest': manifest, 'extract': extract, 'table': table}[a.cmd](a)


if __name__ == '__main__':
    main()
