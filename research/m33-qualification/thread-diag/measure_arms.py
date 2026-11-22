"""Is F2's extra running thread on the shipping F4 the stage-measurement recording of #993?

Runs the two session-2 failing rows, shipping F4 at 16 workers, under `tasktrace`, in three arms:
F0, F2 with `--measure-stages` and F2 without. Teams follow `classify.py` (a birth after a member
is gone starts the next team). Per run it takes the most workers in state R at once (`total`) and
the most in state R within one team (`team`); the excess is `total - 16` clipped at 0.
Usage: measure_arms.py run --f0 BIN --f2 BIN --tasktrace BIN --out DIR [--reps 20] [--cpus 24-39];
measure_arms.py report --out DIR.
"""
import argparse
import json
import subprocess
from pathlib import Path

CAP = 16
ROWS = {
    'grevlex/gf32003/noon-7': ['--field', 'gf32003', '--name', 'noon-7', '--order', 'grevlex'],
    'grlex/m31/mq-random-10-s10': ['--field', 'm31', '--name', 'mq-random-10-s10', '--order', 'grlex'],
}
COMMON = ['--engine', 'f4', '--workers', str(CAP), '--wall-s', '180']


def arms(a):
    return {'f0': [a.f0], 'f2-measure-on': [a.f2, '--measure-stages'], 'f2-measure-off': [a.f2]}


def run(a):
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    for rep in range(a.reps):  # arms interleaved within each repetition
        for row, argv in ROWS.items():
            for arm, (binary, *extra) in arms(a).items():
                stem = out / f"{row.replace('/', '_')}.{arm}.{rep}"
                cmd = ['taskset', '-c', a.cpus, a.tasktrace, f'{stem}.trace.jsonl', '--', binary, *argv, *COMMON, *extra]
                with open(f'{stem}.report.json', 'w') as rep_out:
                    rc = subprocess.run(cmd, stdout=rep_out, stderr=subprocess.DEVNULL).returncode
                print(row, arm, rep, f'rc={rc}', flush=True)


def peaks(trace):
    rows = [json.loads(line) for line in open(trace)]
    tasks = sorted((d for d in rows if d['kind'] == 'task'), key=lambda t: t['first_us'])
    main, teams = tasks[0]['tid'], []
    for t in tasks[1:]:
        if not teams or min(x['last_us'] for x in teams[-1]) < t['first_us']:
            teams.append([])
        teams[-1].append(t)
    team_of = {t['tid']: k for k, tm in enumerate(teams) for t in tm}
    total = team = 0
    for s in (d for d in rows if d['kind'] == 'sample'):
        run_w = [tid for tid in s['running'] if tid != main and tid in team_of]
        total = max(total, len(run_w))
        per = {}
        for tid in run_w:
            per[team_of[tid]] = per.get(team_of[tid], 0) + 1
        team = max([team, *per.values()])
    return total, team


def report(a):
    agg = {}
    for trace in sorted(Path(a.out).glob('*.trace.jsonl')):
        row, arm, _ = trace.name.split('.', 2)
        total, team = peaks(trace)
        status = json.loads(Path(str(trace).replace('trace.jsonl', 'report.json')).read_text() or '{}').get('status')
        g = agg.setdefault((row.replace('_', '/'), arm), dict(runs=0, team=0, excess=0, over=0, status=set()))
        g['runs'] += 1
        g['team'] = max(g['team'], team)
        g['excess'] = max(g['excess'], max(0, total - CAP))
        g['over'] += total > CAP
        g['status'].add(status)
    print(f'Shipping F4, {CAP} workers. team = most workers running within one team; excess = most '
          f'workers running at once beyond {CAP}; runs over = runs with any excess.\n')
    print('| Row | Arm | Runs | Status | Max per-team running | Max excess | Runs over |')
    print('|---|---|---:|---|---:|---:|---:|')
    for (row, arm), g in sorted(agg.items()):
        print(f"| {row} | {arm} | {g['runs']} | {','.join(sorted(map(str, g['status'])))} | {g['team']} | "
              f"{g['excess']} | {g['over']} |")


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest='cmd', required=True)
    r = sub.add_parser('run')
    for flag in ('--f0', '--f2', '--tasktrace', '--out'):
        r.add_argument(flag, required=True)
    r.add_argument('--reps', type=int, default=20)
    r.add_argument('--cpus', default='24-39')
    s = sub.add_parser('report')
    s.add_argument('--out', required=True)
    a = p.parse_args()
    (run if a.cmd == 'run' else report)(a)


if __name__ == '__main__':
    main()
