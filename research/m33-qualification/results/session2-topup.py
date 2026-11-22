"""Session 2 top-up, void-aware: pool only non-void jobs; a void job is re-run whole from its own
manifest (§11.2); short cells get one job per (suite, row) until none is short."""
import math
import os
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

WT = Path('/home/mfaulk/projects/zeebra/.claude/worktrees/agent-a92c6b7de73f694f2')
B = Path('/buildcache/cargo-target/zeebra-974')
Q = WT / 'research/m33-qualification'
sys.path.insert(0, str(Q))
import summarize  # noqa: E402

bs = summarize.bs
F2 = 'db181c5126f095fa1a2e71809357b55b46ded4ca'
ARGS = ['--f0-study', str(B / 'bin/31e334bda226/m33_qualify'), '--f2-study', str(B / 'bin/db181c5126f0/m33_qualify'),
        '--f2', F2, '--harness', 'dd57bc4e']
SUITE_OF = {'grevlex/goldilocks/katsura-11': 'regression-G', 'grevlex/wide64/noon-8': 'regression-G',
            'grevlex/m31/eco-11': 'regression-M'}
env = dict(os.environ, ZEEBRA_BENCH_JOBS=str(B / 'jobs'), TMPDIR=str(B / 'tmp'))
agent = subprocess.run([str(WT / 'scripts/agent/zb-claim.sh'), 'id'], capture_output=True, text=True, cwd=WT).stdout.strip()
jobs = {'regression': ['0162de844b66', '66ff78bb4821'], 'small': ['35d0bb84eeb2', 'aa4e0948ead9']}
earlier = {'f5b7d91d6f16': 'small', '78e334642071': 'small', '903cf9a28b5a': 'small', 'e5b385cada2b': 'regression',
           '82ca5790cfb3': 'regression', '9440fdaf0931': 'small', '6d861173f26a': 'small',
           'e9b4407fdfbc': 'regression'}


def void(jid):
    records = summarize.attempts(B / 'jobs' / jid)
    dirty = sum(r['contaminated'] for r in records)
    return bs.session_void(len(records) - dirty, dirty)


def log(msg):
    print(msg, flush=True)
    with open(B / 'q2-jobs.txt', 'a') as f:
        f.write(msg + '\n')


def run_manifest(man, kind, tries=3):
    import json
    for t in range(tries):
        if t:
            m = json.loads(man.read_text())
            m['context']['attempt'] = m['context'].get('attempt', 1) + 1
            man = man.with_name(man.stem.split('.try')[0] + f'.try{t + 1}.json')
            man.write_text(json.dumps(m, indent=2))
        jid = subprocess.run([str(WT / 'tools/bench-job'), 'submit', str(man)], capture_output=True, text=True,
                             cwd=WT, env=env, check=True).stdout.strip().splitlines()[-1]
        with open(B / f'q2-{jid}.log', 'w') as out:
            rc = subprocess.run([str(WT / 'tools/bench-job'), 'run', jid], stdout=out, stderr=subprocess.STDOUT,
                                cwd=WT, env=env).returncode
        v = void(jid)
        log(f'  {man.name} -> {jid} rc={rc} void={v}')
        if not v:
            jobs[kind].append(jid)
            return
    log(f'  {man.name}: void {tries} times, left out')


for jid, kind in earlier.items():
    if void(jid):
        log(f'void {jid}: re-run whole')
        copy = B / f'q2-rerun-{jid}.json'
        m = __import__('json').loads((B / 'jobs' / jid / 'manifest.json').read_text())
        m['context']['rerun_of'] = jid
        m['context']['attempt'] = 2 if jid == 'b2e860b81d5a' else 1
        copy.write_text(__import__('json').dumps(m, indent=2))
        run_manifest(copy, kind)
    else:
        jobs[kind].append(jid)


def summary():
    cmd = ['python3', str(Q / 'summarize.py'), 'regression'] + [str(B / 'jobs' / j) for j in jobs['regression']] \
        + ['--small'] + [str(B / 'jobs' / j) for j in jobs['small']]
    out = subprocess.run(cmd, capture_output=True, text=True, cwd=WT).stdout
    (B / 'q2-regression.md').write_text(out)
    return out


for rnd in range(1, 5):
    out = summary()
    cells = [(m[1], m[2], int(m[3]), int(m[4]), int(m[5])) for m in
             re.finditer(r'\| (\S+) \| (\w+) \| (\d+) \| [^|]+ \| wall stopped: n = (\d+) < (\d+) \|', out)]
    log(f'round {rnd}: {len(cells)} short cells')
    if not cells:
        break
    groups = defaultdict(list)
    cells = [c for c in cells if c[0] != 'grevlex/wide64/katsura-9']  # void 3 of 3 under the clock rule
    if not cells:
        break
    for c in cells:
        groups[c[0]].append(c)
    for row, cs in groups.items():
        suite = SUITE_OF.get(row) or ('small-G' if '/wide64/' in row else 'small-M')
        reps = math.ceil(max(full - n for *_, n, full in cs) * 1.4) + 2
        man = B / f'q2-topup2-{rnd}-{row.replace("/", "_")}.json'
        cmd = ['python3', str(Q / 'campaign.py'), 'manifest', '--suite', suite, *ARGS, '--agent', agent,
               '--rows', row, '--engines', *sorted({c[1] for c in cs}),
               '--workers', *map(str, sorted({c[2] for c in cs})), '--reps', str(reps)]
        man.write_text(subprocess.run(cmd, capture_output=True, text=True, cwd=WT, check=True).stdout)
        run_manifest(man, 'regression' if suite.startswith('regression') else 'small')
summary()
log(f'final jobs: regression {" ".join(jobs["regression"])} small {" ".join(jobs["small"])}')
