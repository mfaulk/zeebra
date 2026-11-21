"""For each sample with more than CAP workers in state R: how many of them belong to the newest team
started by then, and how many to an earlier team (one already losing members, so exiting), and how
long each earlier-team thread has left before its last sighting. Usage: classify.py OUT_DIR."""
import collections
import json
import sys
from pathlib import Path

CAP = 16


def teams_of(tasks):
    teams = []
    for t in tasks:
        if not teams or min(x['last_us'] for x in teams[-1]) < t['first_us']:
            teams.append([])
        teams[-1].append(t)
    return teams


agg = collections.defaultdict(lambda: dict(over=0, max_new=0, max_old=0, old_left_us=[]))
for trace in sorted(Path(sys.argv[1]).glob('*.trace.jsonl')):
    row, arm = trace.name.split('.')[:2]
    rows = [json.loads(line) for line in open(trace)]
    tasks = sorted((d for d in rows if d['kind'] == 'task'), key=lambda t: t['first_us'])
    main, teams = tasks[0]['tid'], teams_of(tasks[1:])
    team_of = {t['tid']: k for k, tm in enumerate(teams) for t in tm}
    last = {t['tid']: t['last_us'] for t in tasks}
    a = agg[row.replace('_', '/'), arm]
    for s in (d for d in rows if d['kind'] == 'sample'):
        run_w = [tid for tid in s['running'] if tid != main and tid in team_of]
        if len(run_w) <= CAP:
            continue
        newest = max(team_of[t] for t in run_w)
        old = [t for t in run_w if team_of[t] != newest]
        a['over'] += 1
        a['max_new'] = max(a['max_new'], len(run_w) - len(old))
        a['max_old'] = max(a['max_old'], len(old))
        a['old_left_us'] += [last[t] - s['us'] for t in old]

print(f'Samples with more than {CAP} workers in state R. new = running workers of the newest team; '
      "old = running workers of an earlier team; left = µs from the sample to that thread's last sighting.\n")
print('| Row | Arm | Samples | max new | max old | old left µs (median / max) |')
print('|---|---|---:|---:|---:|---|')
for (row, arm), a in sorted(agg.items()):
    left = sorted(a['old_left_us'])
    lm = f'{left[len(left) // 2]} / {left[-1]}' if left else '-'
    print(f"| {row} | {arm} | {a['over']} | {a['max_new']} | {a['max_old']} | {lm} |")
