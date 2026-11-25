"""Telemetry-overhead A/A for #1105: does recording the #1105 snapshot fields move timed walls?

Usage (inside a reservation, from bench-reserve run):
  python3 -I aa.py <repo> <sig_f4_study> <out.jsonl> [pairs]

Each attempt is what tools/bench-job's run_attempt does: harness moved to the spare CPUs of
run.cpus=8-23 when there are any, a cpu-context.sh snapshot before and after, the frequency
sampler, perf stat -p, rss-guard and GNU time. The arms differ only in ZEEBRA_CPU_CONTEXT_TELEMETRY
(1 = on, 0 = off), which every snapshot child inherits. Arm order alternates per pair."""
import json, os, sys, tempfile, importlib.util
from pathlib import Path

repo, binary, out = Path(sys.argv[1]), sys.argv[2], Path(sys.argv[3])
pairs = int(sys.argv[4]) if len(sys.argv) > 4 else 9
spec = importlib.util.spec_from_file_location('bench_campaign', repo / 'tools/bench_campaign.py')
campaign = importlib.util.module_from_spec(spec)
spec.loader.exec_module(campaign)

RUN_CPUS = set(range(8, 24))
CELLS = [  # (instance, field, workers, cpus) as #968/#985
    ('gf32003/mq-random-10', 'gf32003', 'mq-random-10', 16, '8-23'),
    ('wide64/eco-12', 'wide64', 'eco-12', 1, '8'),
]


def expand(cpus):
    out = set()
    for p in cpus.split(','):
        a, _, b = p.partition('-')
        out |= set(range(int(a), int(b or a) + 1))
    return out


rss, perf = campaign.gnu_time(), campaign.perf_stat()
scratch = Path(tempfile.mkdtemp(dir=os.environ.get('TMPDIR')))
saved = os.sched_getaffinity(0)
with out.open('a') as f:
    for rep in range(pairs):
        for name, field, inst, w, cpus in CELLS:
            order = ('on', 'off') if (rep + len(name)) % 2 == 0 else ('off', 'on')
            for arm in order:
                os.environ['ZEEBRA_CPU_CONTEXT_TELEMETRY'] = '1' if arm == 'on' else '0'
                spare = RUN_CPUS - expand(cpus)
                if spare:
                    os.sched_setaffinity(0, spare)
                argv = [binary, '--field', field, '--name', inst, '--engine', 'entry', '--workers', str(w), '--wall-s', '600']
                try:
                    r = campaign.run_child(argv, cpus, 600, 60, guard=(Path(binary).name[:15], binary, 16 * 1024 * 1024),
                                           scratch_dir=scratch, rss_reporter=rss, perf=perf)
                finally:
                    os.sched_setaffinity(0, saved)
                rec = dict(rep=rep, cell=f'{name}@{w}w', arm=arm, exit=r['returncode'], wall_s=r['process_wall_ns'] / 1e9,
                           cpu_s=r['cpu_seconds'], spare=len(spare), perf=r.get('perf'), freq=r.get('freq'),
                           telemetry_before='telemetry' in (r.get('before') or {}), at=(r.get('after') or {}).get('at'))
                f.write(json.dumps(rec) + '\n')
                f.flush()
                print(rec['cell'], rep, arm, round(rec['wall_s'], 4), rec['exit'], flush=True)
