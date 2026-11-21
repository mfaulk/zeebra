#!/usr/bin/env python3
"""#966 deliverable 4: how many threads msolve and grobx actually compute on (plan §11.5).

Each attempt samples every thread's user+system ticks (`/proc/<pid>/task/*/stat`) every 50 ms.
`active` counts threads that gained a tick over the attempt; `concurrent` is the most threads
that gained a tick within one 50 ms interval, a lower bound on simultaneous use.

    census.py --study BIN --msolve BIN --grobx BIN[,BIN] --output census.jsonl
"""
import argparse
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import admission  # noqa: E402

MSOLVE_ROWS = [('gf32003', 'mq-random-10'), ('m31', 'mq-random-10'), ('gf32003', 'katsura-11'), ('m31', 'katsura-11')]
GROBX_ROWS = [('wide64', 'eco-12'), ('wide64', 'katsura-11'), ('goldilocks', 'mq-random-11')]
MSOLVE_WORKERS = (1, 4, 8, 16)
REPS = 3
PERIOD_S = 0.05


def ticks(pid):
    out = {}
    for task in Path(f'/proc/{pid}/task').iterdir():
        try:
            fields = task.joinpath('stat').read_text().rsplit(')', 1)[1].split()
            out[task.name] = int(fields[11]) + int(fields[12])
        except (FileNotFoundError, ProcessLookupError, IndexError):
            pass
    return out


def sampled(argv, cpus):
    started = time.monotonic_ns()
    child = subprocess.Popen(['taskset', '-c', cpus, *argv], stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    first, last, concurrent, seen = {}, {}, 0, 0
    while child.poll() is None:
        try:
            now = ticks(child.pid)
        except FileNotFoundError:
            break
        seen = max(seen, len(now))
        concurrent = max(concurrent, sum(1 for t, v in now.items() if v > last.get(t, v)))
        for t, v in now.items():
            first.setdefault(t, v)
        last.update(now)
        time.sleep(PERIOD_S)
    child.wait()
    active = sum(1 for t in last if last[t] > first[t])
    return dict(rc=child.returncode, process_wall_ns=time.monotonic_ns() - started, threads_seen=seen,
                active=active, concurrent=concurrent)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--study', required=True)
    p.add_argument('--msolve', required=True)
    p.add_argument('--grobx', required=True, help='comma-separated drivers, one per pin')
    p.add_argument('--cpus', default='8-23')
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    with args.output.open('a') as out, tempfile.TemporaryDirectory(dir=os.environ.get('TMPDIR')) as d:
        def emit(**record):
            out.write(json.dumps(record) + '\n')
            out.flush()
            print(record['solver'], record['field'], record['name'], record['workers'], record['active'],
                  record['concurrent'], flush=True)
        for rep in range(REPS):
            for field, name in MSOLVE_ROWS:
                case = json.loads(subprocess.check_output(
                    [args.study, '--field', field, '--name', name, '--engine', 'f4', '--input-only'], text=True))
                src = Path(d, 'in.ms')
                src.write_text(','.join(case['variables']) + '\n' + case['modulus'] + '\n'
                               + ',\n'.join(case['generators']) + '\n')
                for w in MSOLVE_WORKERS:
                    r = sampled([args.msolve, '-f', str(src), '-o', str(Path(d, 'out.ms')), '-t', str(w), '-g', '2'],
                                args.cpus)
                    emit(solver='msolve', rep=rep, field=field, name=name, digest=case['digest'], workers=w, **r)
            for binary in args.grobx.split(','):
                for field, name in GROBX_ROWS:
                    case = json.loads(subprocess.check_output(
                        [args.study, '--field', field, '--name', name, '--engine', 'f4', '--input-only'], text=True))
                    req = Path(d, 'g.json')
                    req.write_text(json.dumps(dict(
                        variables=case['variables'], modulus=int(case['modulus']), order='grevlex', workers=16,
                        threads_probe=True, generators=case['generators'], mode='raw',
                        wall_ns=admission.CAP_S * 10**9, rss_bytes=admission.CAP_BYTES)))
                    r = sampled([binary, str(req)], args.cpus)
                    emit(solver='grobx', driver=binary, rep=rep, field=field, name=name, digest=case['digest'],
                         workers=16, **r)


if __name__ == '__main__':
    main()
