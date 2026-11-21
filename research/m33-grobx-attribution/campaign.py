#!/usr/bin/env python3
"""#970 (M33-G1): one bench-job session attributing the 1-w grobx gap on Track G's three rows.

    campaign.py manifest --bin DIR --commit C --agent ID [--reps 9] > manifests/<session>.json
    campaign.py extract --job DIR      # journal -> records-<job>.jsonl.gz (+ .session.json)
    campaign.py retain --job DIR       # journal -> journals/<job>/ (payloads under 64 KiB)
    campaign.py work --bin DIR         # untimed conventional-F4 counters (`--discovery`) -> work.json

Arms, all at one worker on CPU 8: `sig` (the timed build, F0 source), `split` (the
`research-sigf4-split` build: unfused symbolic, stage-component clocks and the element ledger),
`grobx155` (its stock report carries its own stage clocks and budget charges), `sig-hw` and `split-hw`
(the same two builds under `hwcount.py`), and `sig-w4` (the timed build asked for four workers on
the one CPU: design 2's reducer-block pass ahead of the cascade, #894's question for this route).
Request formats and inputs are #966's (`research/m33-baseline/campaign.py`), unchanged.
"""
import argparse
import gzip
import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'research/m33-baseline'))
# #966's campaign module shares this file's name, so it is loaded under its own.
_spec = importlib.util.spec_from_file_location('m33_baseline_campaign', ROOT / 'research/m33-baseline/campaign.py')
base = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(base)

ROWS = [('wide64', 'eco-12'), ('wide64', 'katsura-11'), ('goldilocks', 'mq-random-11')]
INPUTS = '/buildcache/cargo-target/zeebra-966-p2/inputs'
FEATURES = {'sig': 'research-sigf4', 'split': 'research-sigf4-split', 'work': 'research-sigf4,research-work'}


def study(bin_dir, build, commit):
    return Path(bin_dir, f'sig_f4_study-{build}-{commit}')


def zeebra_arm(name, binary, build, commit, workers='{workers}', wrapped=None):
    flags = (f'--features {FEATURES[build]}; fat LTO, codegen-units 1 (Cargo.toml); -C target-cpu=x86-64-v3 '
             '(.cargo/config.toml); RUSTC_WRAPPER="" CARGO_INCREMENTAL=0')
    recipe = f'git archive {commit} | tar -x; cargo build --release --locked --features {FEATURES[build]} --example sig_f4_study'
    argv = ['--field', '{field}', '--name', '{name}', '--engine', 'sigf4', '--workers', workers, '--digest-only',
            '--wall-s', str(base.CAP_S)]
    arm = dict(name=name, commit=commit, binary=str(binary), sha256=base.sha(binary),
               build=dict(profile='release', flags=flags, recipe=recipe), argv=argv, workers=[1])
    if wrapped:  # hwcount.py is the arm's binary; the study it runs is named and hashed in the recipe
        arm.update(binary=str(wrapped), sha256=base.sha(wrapped), argv=['--', str(binary), *argv])
        arm['build']['recipe'] += f'; run under research/m33-grobx-attribution/hwcount.py, study SHA-256 {base.sha(binary)}'
    return arm


def manifest(args):
    sig, split = study(args.bin, 'sig', args.commit), study(args.bin, 'split', args.commit)
    hw = HERE / 'hwcount.py'
    arms = [zeebra_arm('sig', sig, 'sig', args.commit), zeebra_arm('split', split, 'split', args.commit),
            base.comparand_arm('grobx155', args.grobx155, ['{inputs[grobx]}'], [1]),
            zeebra_arm('sig-hw', sig, 'sig', args.commit, wrapped=hw),
            zeebra_arm('split-hw', split, 'split', args.commit, wrapped=hw),
            zeebra_arm('sig-w4', sig, 'sig', args.commit, workers='4')]
    instances = []
    for field, name in ROWS:
        d = Path(args.inputs, base.key(field, name))
        instances.append(dict(name=f'{field}/{name}', params=dict(field=field, name=name),
                              inputs=dict(grobx=dict(path=str(d / 'grobx.json'), sha256=base.sha(d / 'grobx.json')))))
    return dict(schema='bench-job-manifest-v1', mode='dev',
                context=dict(issue=970, agent=args.agent, track='G', session=args.session),
                arms=arms, instances=instances,
                run=dict(workers=[1], cpus='8-23', repetitions=args.reps, interleave='rotate', seeds=[0], retries=0,
                         limits=dict(wall_seconds=base.CAP_S, kill_after_seconds=30, rss_bytes=base.CAP_BYTES,
                                     live_bytes=None)))


def report_lines(text):
    """grobx's stock report: one `(seconds, kind, {key: value})` per line, numbers parsed."""
    out = []
    for line in text.splitlines():
        parts = line.split()
        if len(parts) < 2:
            continue
        fields = {}
        for p in parts[2:]:
            k, sep, v = p.partition('=')
            if not sep:
                continue
            try:
                fields[k] = int(v)
            except ValueError:
                try:
                    fields[k] = float(v)
                except ValueError:
                    fields[k] = v
        out.append((float(parts[0]), parts[1], fields))
    return out


ROUND_CLOCKS = ('select', 'symbolic', 'encode', 'reduce', 'backsub', 'record', 'decode', 'update')
INTER_CLOCKS = ('symbolic', 'encode', 'reduce', 'decode')


def grobx_summary(text):
    """Per engine run, the round totals (clocks in ns, budget charges, reductions, zero reductions,
    largest matrix); then the final interreduction and the call's end, from one stock report."""
    runs, inter, end, text_ns = [], None, None, 0
    for _, kind, f in report_lines(text):
        if kind == 'run':
            runs.append(dict(engine=f.get('engine'), reduce=f.get('reduce'), rounds=0, reductions=0, zero=0,
                             pivots=0, subtracted=0, entries=0, max_rows=0, max_columns=0,
                             **{f'{c}_ns': 0 for c in ROUND_CLOCKS}))
        elif kind == 'echelon' and runs:
            runs[-1]['subtracted'] += f.get('subtracted', 0)
        elif kind == 'round' and runs:
            r = runs[-1]
            r['rounds'] += 1
            for k in ('reductions', 'zero', 'pivots', 'subtracted', 'entries'):
                r[k] += f.get(k, 0)
            r['max_rows'] = max(r['max_rows'], f.get('rows', 0))
            r['max_columns'] = max(r['max_columns'], f.get('columns', 0))
            for c in ROUND_CLOCKS:
                r[f'{c}_ns'] += round(f.get(c, 0) * 1e9)
        elif kind == 'ran' and runs:
            runs[-1].update(outcome=f.get('outcome'), run_ns=round(f.get('time', 0) * 1e9),
                            elements=f.get('elements'))
        elif kind == 'inter':
            inter = dict(rows=f['rows'], columns=f['columns'], entries=f['entries'], subtracted=f['subtracted'],
                         elements=f['elements'], **{f'{c}_ns': round(f.get(c, 0) * 1e9) for c in INTER_CLOCKS})
        elif kind == 'text':
            text_ns += round(f.get('time', 0) * 1e9)
        elif kind == 'end':
            end = round(f.get('time', 0) * 1e9)
    return dict(runs=runs, inter=inter, text_ns=text_ns, call_ns=end)


def hwcount_of(stderr):
    """The `hwcount {json}` line `hwcount.py` appends to the attempt's stderr, or None."""
    for line in reversed(stderr.decode(errors='replace').splitlines()):
        if line.startswith('hwcount '):
            return json.loads(line[len('hwcount '):])
    return None


def extract(args):
    state = base.aj.load(args.job / 'journal')
    session = (state['stop'] or {}).get('contamination') or {}
    out = []
    for a in state['attempts']:
        cell, md = a['cell'], a['metadata']
        field, name = cell['instance'].split('/')
        verdict = (md.get('contamination') or {}).get('verdict')
        arm = cell['arm']
        rec = dict(job=state['header']['bench_job']['job_id'], attempt=md['attempt_id'], arm=arm, field=field,
                   name=name, rep=cell['rep'], status=a['status'], exit=md['exit'], wall_ns=md['process_wall_ns'],
                   cpu_s=md['cpu_seconds'], peak_rss_bytes=md['observed_peak_rss_bytes'],
                   contaminated=bool(verdict and verdict['contaminated']) or md['attempt_id'] in session.get('flagged', {}),
                   reasons=(verdict or {}).get('reasons', []) + session.get('flagged', {}).get(md['attempt_id'], []),
                   metrics=(md.get('contamination') or {}).get('metrics'))
        if a['status'] == 'ok' and arm.startswith('grobx'):
            reply = json.loads(a['stdout'])
            rec['grobx'] = dict(grobx_summary(reply['report']), parse_ns=reply.get('parse_ns'),
                                solve_ns=reply.get('solve_ns'))
            rec['basis_m33'] = base.admission.grobx_digest(a['stdout'].decode(), json.loads(
                Path(INPUTS, base.key(field, name), 'case.json').read_text()))
        elif a['status'] == 'ok':
            r = json.loads(a['stdout'])
            rec['zeebra'] = {k: r.get(k) for k in ('call_ns', 'main_ns', 'basis_m33_ns', 'status')}
            rec['zeebra']['statistics'] = r.get('statistics')
            rec['basis_m33'] = r.get('basis_m33')
            rec['hwcount'] = hwcount_of(a['stderr'])
        out.append(rec)
    job = state['header']['bench_job']['job_id']
    path = HERE / f'records-{job}.jsonl.gz'
    payload = ''.join(json.dumps(r, sort_keys=True) + '\n' for r in out).encode()
    path.write_bytes(gzip.compress(payload, compresslevel=9, mtime=0))
    meta = dict(job=state['header']['bench_job'], stop=state['stop'], journal_sha256=state['journal_sha256'],
                attempts=len(out))
    Path(str(path).replace('.jsonl.gz', '.session.json')).write_text(json.dumps(meta, indent=1, sort_keys=True) + '\n')
    print(path, len(out), 'attempts')


def work(args):
    """Conventional F4's serial work ledger per row (`--engine f4 --discovery`), untimed, off the bench CPUs;
    counters are deterministic, so one run per row."""
    binary = study(args.bin, 'work', args.commit)
    out = {}
    for field, name in ROWS:
        r = json.loads(subprocess.check_output(
            ['taskset', '-c', args.cpu, str(binary), '--field', field, '--name', name, '--engine', 'f4',
             '--workers', '1', '--digest-only', '--discovery', '--wall-s', '600'], text=True))
        out[f'{field}/{name}'] = dict(work=r.get('work'), basis_m33=r.get('basis_m33'), call_ns=r.get('call_ns'))
        print(field, name, json.dumps(r.get('work'))[:200], flush=True)
    meta = dict(binary=binary.name, sha256=base.sha(binary), commit=args.commit, cpus=args.cpu,
                note='untimed: off the bench CPUs beside builds; only the counters are read')
    (HERE / 'work.json').write_text(json.dumps(dict(meta=meta, rows=out), indent=1, sort_keys=True) + '\n')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('command', choices=('manifest', 'extract', 'retain', 'work'))
    p.add_argument('--bin', default='/buildcache/cargo-target/zeebra-970/bin')
    p.add_argument('--commit')
    p.add_argument('--inputs', default=INPUTS)
    p.add_argument('--grobx155', default='/buildcache/cargo-target/zeebra-grobx-8005a2a1/release/grobx-driver')
    p.add_argument('--agent', default='')
    p.add_argument('--session', default='g1')
    p.add_argument('--reps', type=int, default=9)
    p.add_argument('--job', type=Path)
    p.add_argument('--cpu', default=os.environ.get('M33_UNTIMED_CPUS', '40'))
    args = p.parse_args()
    if args.command == 'manifest':
        print(json.dumps(manifest(args), indent=1))
    elif args.command == 'extract':
        extract(args)
    elif args.command == 'retain':
        base.HERE = HERE
        base.retain(args)
    else:
        work(args)


if __name__ == '__main__':
    main()
