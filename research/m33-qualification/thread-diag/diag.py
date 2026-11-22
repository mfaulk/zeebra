"""Thread-state diagnosis of the five M33-Q thread-cap rows (owner decision 11 on #965).

Diagnosis only, not a timing session: each arm of the correctness manifests runs at 16 workers
under `tasktrace`, which samples every thread's state from outside the process. A team is a run of
worker births with no gap over TEAM_GAP_US; it starts at its first birth and finishes when its last
member is last seen. Usage: diag.py run --manifests DIR --tasktrace BIN --out DIR [--reps N]
[--cpus LIST]; diag.py report --out DIR.
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path

ROWS = {  # row -> the manifest it came from
    'grevlex/gf32003/katsura-11': 'q-grevlex.json',
    'grevlex/gf32003/noon-7': 'q-grevlex.json',
    'grevlex/wide64/cyclic-7': 'q-grevlex.json',
    'grevlex/wide64/noon-8': 'q-grevlex.json',
    'grlex/wide64/eco-12': 'q-grlex.json',
}
CAP = 16
TEAM_GAP_US = 500


def argv(arm, params):
    out = []
    for a in arm['argv']:
        a = a.format(workers=CAP, **params)
        if a and a != '--sample-threads':
            out.append(a)
    return [arm['binary']] + out


def run(args):
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    for row, manifest in ROWS.items():
        m = json.load(open(Path(args.manifests) / manifest))
        params = next(i['params'] for i in m['instances'] if i['name'] == row)
        for arm in m['arms']:
            for rep in range(args.reps):
                stem = out / f"{row.replace('/', '_')}.{arm['name']}.{rep}"
                cmd = ['taskset', '-c', args.cpus, args.tasktrace, f'{stem}.trace.jsonl', '--'] + argv(arm, params)
                with open(f'{stem}.report.json', 'w') as rep_out:
                    rc = subprocess.run(cmd, stdout=rep_out, stderr=subprocess.DEVNULL).returncode
                print(row, arm['name'], rep, f'rc={rc}', flush=True)


def analyse(trace):
    samples, tasks = [], []
    for line in open(trace):
        d = json.loads(line)
        if d['kind'] == 'sweeps':
            sweep_us = d['us'] / max(d['count'], 1)
            continue
        (samples if d['kind'] == 'sample' else tasks).append(d)
    tasks.sort(key=lambda t: t['first_us'])
    main, workers = tasks[0]['tid'], tasks[1:]
    # A team is the threads born before any of them is gone: a birth after a member's last sighting
    # starts the next team.
    teams, team_of = [], {}
    for t in workers:
        if not teams or min(teams[-1]['last']) < t['first_us']:
            teams.append(dict(start=t['first_us'], last=[], tids=[]))
        teams[-1]['last'].append(t['last_us'])
        teams[-1]['tids'].append(t['tid'])
        team_of[t['tid']] = len(teams) - 1
    for tm in teams:
        tm['finish'] = max(tm['last'])
    r = dict(max_running_total=0, max_running_workers=0, max_alive_workers=0, over_cap_samples=0,
             over_cap_running_workers=0, over_cap_live_team_alive=0, over_cap_from_ended_teams=0)
    for s in samples:
        run_w = [tid for tid in s['running'] if tid != main]
        alive_w = s['alive'] - 1
        r['max_running_total'] = max(r['max_running_total'], len(s['running']))
        r['max_running_workers'] = max(r['max_running_workers'], len(run_w))
        r['max_alive_workers'] = max(r['max_alive_workers'], alive_w)
        if alive_w > CAP:
            # Teams started by now; the newest is the live one, any older one has begun exiting.
            newest = max((k for k, tm in enumerate(teams) if tm['start'] <= s['us']), default=None)
            live = sum(1 for k, tm in enumerate(teams) if k == newest and tm['start'] <= s['us'] <= tm['finish']
                       for _ in tm['tids'])
            r['over_cap_samples'] += 1
            r['over_cap_running_workers'] = max(r['over_cap_running_workers'], len(run_w))
            r['over_cap_live_team_alive'] = max(r['over_cap_live_team_alive'], min(live, alive_w))
            r['over_cap_from_ended_teams'] = max(r['over_cap_from_ended_teams'], alive_w - min(live, alive_w))
    r['sweep_us'] = round(sweep_us, 1)
    r['teams'] = len(teams)
    r['largest_team'] = max((len(t['tids']) for t in teams), default=0)
    r['team_overlaps'] = sum(1 for a, b in zip(teams, teams[1:]) if b['start'] <= a['finish'])
    return r


def report(args):
    out = Path(args.out)
    agg = {}
    for trace in sorted(out.glob('*.trace.jsonl')):
        row, arm, _rep, _ = trace.name.split('.', 3)
        r = analyse(trace)
        report = json.loads((trace.parent / trace.name.replace('trace.jsonl', 'report.json')).read_text() or '{}')
        a = agg.setdefault((row.replace('_', '/'), arm), dict(runs=0, status=set(), team=set()))
        a['runs'] += 1
        a['status'].add(report.get('status'))
        a['team'].add(report.get('team'))
        for k, v in r.items():
            a[k] = a.get(k, 0) + v if k == 'over_cap_samples' else max(a.get(k, 0), v)
    cols = ['max_running_workers', 'max_running_total', 'max_alive_workers', 'over_cap_samples',
            'over_cap_running_workers', 'over_cap_from_ended_teams', 'largest_team', 'team_overlaps', 'sweep_us']
    print(f'Cap {CAP}. Maxima over runs, except over_cap_samples (summed). `workers` excludes the calling '
          'thread; `total` includes it. over_cap_* describe samples with more than the cap of workers alive.\n')
    print('| Row | Arm | Runs | Status | ' + ' | '.join(cols) + ' |')
    print('|---|---|---:|---|' + '---:|' * len(cols))
    for (row, arm), a in sorted(agg.items()):
        print(f"| {row} | {arm} | {a['runs']} | {','.join(map(str, sorted(a['status'], key=str)))} | "
              + ' | '.join(str(a[c]) for c in cols) + ' |')


def main(argv_=None):
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest='cmd', required=True)
    r = sub.add_parser('run')
    r.add_argument('--manifests', required=True)
    r.add_argument('--tasktrace', required=True)
    r.add_argument('--out', required=True)
    r.add_argument('--reps', type=int, default=10)
    r.add_argument('--cpus', default='24-39')
    s = sub.add_parser('report')
    s.add_argument('--out', required=True)
    a = p.parse_args(argv_)
    (run if a.cmd == 'run' else report)(a)


if __name__ == '__main__':
    sys.exit(main())
