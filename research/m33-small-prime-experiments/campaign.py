#!/usr/bin/env python3
"""#973 M33-M2, candidate K-IR: the stop-rule session as a `tools/bench-job` job (plan §9.8, §13).

    campaign.py manifest --study BIN --commit SHA   # bench-job manifest on stdout
    campaign.py extract  --job DIR                  # journal -> records-<job>.jsonl.gz

One arm, `irsplit`: `--engine entry` on a build of the measured commit, whose library differs from
its merge base only by the sub-stage clocks of the final interreduction, printed to stderr when
`ZB_IR_SPLIT` is set in the runner's environment (`tools/bench-job run` passes it through). The
records reuse #972's format (`research/m33-msolve-attribution/campaign.py`) plus the parsed clocks.
"""
import argparse
import gzip
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research/m33-baseline'))
sys.path.insert(0, str(ROOT / 'tools/external'))
import campaign as base  # noqa: E402
import attempt_journal as aj  # noqa: E402

# The Gate A row, and the other development row that the signature route serves.
ROWS = [('m31', 'katsura-11'), ('gf32003', 'katsura-11')]
WORKERS = [1, 4, 8, 16]
SPLIT = re.compile(r'IRSPLIT (.*)')


def manifest(args):
    arm = base.zeebra_arm('irsplit', args.study, 'entry')
    arm['commit'] = args.commit
    arm['build']['recipe'] = (f'checkout whose tracked files equal git archive {args.commit}; '
                              'cargo build --release --features research-sigf4 --example sig_f4_study '
                              '(merge base plus the ZB_IR_SPLIT sub-stage clocks)')
    instances = [dict(name=f'{f}/{n}', params=dict(field=f, name=n, generate='--digest-only'), inputs={})
                 for f, n in ROWS]
    return dict(schema='bench-job-manifest-v1', mode='dev',
                context=dict(issue=973, agent=args.agent, track='M', session='kir-split'),
                arms=[arm], instances=instances,
                run=dict(workers=WORKERS, cpus='8-23', repetitions=args.reps, interleave='rotate', seeds=[0],
                         retries=0, limits=dict(wall_seconds=base.CAP_S, kill_after_seconds=30,
                                                rss_bytes=base.CAP_BYTES, live_bytes=None)))


def split(stderr):
    """The `IRSPLIT key=value` lines, merged; milliseconds except the shape counts."""
    out = {}
    for line in stderr.splitlines():
        if m := SPLIT.search(line):
            for kv in m.group(1).split():
                k, v = kv.split('=')
                out[k] = float(v)
    return out


def extract(args):
    state = aj.load(args.job / 'journal')
    session = (state['stop'] or {}).get('contamination') or {}
    out = []
    for a in state['attempts']:
        cell, md = a['cell'], a['metadata']
        field, name = cell['instance'].split('/')
        verdict = (md.get('contamination') or {}).get('verdict')
        flagged = session.get('flagged', {}).get(md['attempt_id'], [])
        rec = dict(job=state['header']['bench_job']['job_id'], attempt=md['attempt_id'], arm=cell['arm'],
                   field=field, name=name, workers=cell['workers'], rep=cell['rep'], status=a['status'],
                   exit=md['exit'], wall_ns=md['process_wall_ns'], cpu_s=md['cpu_seconds'],
                   peak_rss_bytes=md['observed_peak_rss_bytes'],
                   contaminated=bool(verdict and verdict['contaminated']) or bool(flagged),
                   reasons=(verdict or {}).get('reasons', []) + flagged)
        if a['status'] == 'ok':
            r = json.loads(a['stdout'])
            st = r.get('statistics') or {}
            rec.update(digest=r.get('digest'), basis_m33=r.get('basis_m33'), main_ns=r.get('main_ns'),
                       route=st.get('route'), team=st.get('team'),
                       split=split((a['stderr'] or b'').decode(errors='replace')))
        out.append(rec)
    path = HERE / f'records-{args.job.name}.jsonl.gz'
    payload = ''.join(json.dumps(r, sort_keys=True) + '\n' for r in out).encode()
    path.write_bytes(gzip.compress(payload, compresslevel=9, mtime=0))
    meta = dict(job=state['header']['bench_job'], stop=state['stop'], journal_sha256=state['journal_sha256'],
                attempts=len(out))
    Path(str(path).replace('.jsonl.gz', '.session.json')).write_text(json.dumps(meta, indent=1, sort_keys=True) + '\n')
    print(path, len(out), 'attempts')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=('manifest', 'extract'))
    p.add_argument('--job')
    p.add_argument('--study', default='/buildcache/cargo-target/zeebra-973/sig_f4_study-159f1958')
    p.add_argument('--commit', default='')
    p.add_argument('--agent', default='')
    p.add_argument('--reps', type=int, default=9)
    args = p.parse_args()
    if args.command == 'manifest':
        print(json.dumps(manifest(args), indent=1))
    else:
        args.job = Path(args.job)
        extract(args)


if __name__ == '__main__':
    main()
