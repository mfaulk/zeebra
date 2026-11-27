"""#1107: run one session (§5.4), or one (cohort, workload) job (§8.6's run.sh), under the signed protocol.

  session.py session <label> [--seed YYYYMMDD]    W0, the shuffled loaded workloads, W0; both cohorts each
  session.py one <cohort> <workload> <label>       one bench-job job plus its background load

The load runs only while the job is `running` and is killed by process group when it ends (§2). Stops
(§7.3, #1107): a digest that differs from references.json stops the campaign; an idle A/A outside
its gate stops the session (two such sessions stop the campaign); W4-32 not moving `m5` stops it. A
heavy window (W2, W4-32, W5) never starts beside another agent's queued or held bench job. Held-out
results are never printed here (§8.5): only pass/fail of the stop checks.
"""
import argparse
import gzip
import json
import os
import re
import signal
import subprocess
import sys
import time
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(HERE))
import calib  # noqa: E402
import bench_stats as bs  # noqa: E402

W = calib.W
REST = '0-7,24-71,88-127'  # §5.3: every job mixes 1- and 16-worker cells, so CCDs 1-2
SRC = W / 'src'
JOB, RESERVE = REPO / 'tools/bench-job', REPO / 'tools/bench-reserve.sh'
ENV = dict(os.environ, ZEEBRA_BENCH_JOBS=str(W / 'jobs'), RUSTC_WRAPPER='', TMPDIR=str(W / 'tmp'))
LOG = Path(os.path.expanduser('~/.zeebra/benchlock.log'))
EXIT_CORRECTNESS, EXIT_INSTRUMENT, EXIT_CONTROL = 3, 4, 5


def loads(workload):
    cargo = f'cd {SRC} && export RUSTC_WRAPPER= TMPDIR={W}/tmp; '
    w = {
        'W0': [],
        'W1': [cargo + f'while :; do touch src/lib.rs; CARGO_TARGET_DIR={W}/load-w1 cargo build -q -j8 --tests; done'],
        'W2': [cargo + f'while :; do CARGO_TARGET_DIR={W}/load-w2 cargo clean -q; '
                       f'CARGO_TARGET_DIR={W}/load-w2 cargo build -q -j48 --tests; done'],
        'W3': [cargo + f'while :; do CARGO_TARGET_DIR={W}/load-w3 cargo test -q -j16 --lib -- --test-threads=16; done'],
        'W4-8': [f'exec {W}/bin/stream 8'], 'W4-16': [f'exec {W}/bin/stream 16'], 'W4-32': [f'exec {W}/bin/stream 32'],
    }
    w['W5'] = w['W2'] + w['W4-16']
    return w[workload]


class Session:
    def __init__(self, label):
        self.label = label
        self.dir = W / 'sessions' / label
        self.dir.mkdir(parents=True, exist_ok=True)
        self.agent = subprocess.run([REPO / 'scripts/agent/zb-claim.sh', 'id'], capture_output=True, text=True).stdout.strip()

    def log(self, msg):
        line = f"{time.strftime('%Y-%m-%dT%H:%M:%S%z')} {msg}"
        print(line, flush=True)
        with (self.dir / 'events.log').open('a') as f:
            f.write(line + '\n')

    def uptime(self):
        return Path('/proc/loadavg').read_text().split()[0]


def others_busy(own_prefix='bench-job-'):
    """Other agents' bench jobs queued or holding a benchlock, from benchlock.log (START/END/QUEUED)."""
    state = {}
    for line in LOG.read_text().splitlines()[-2000:]:
        parts = line.split()
        if len(parts) < 3:
            continue
        kind, owner = parts[1], parts[2]
        pid = next((p[4:] for p in parts if p.startswith('pid=')), None)
        if kind in ('QUEUED', 'START'):
            state[(owner, pid)] = kind
        elif kind in ('END', 'ABORT', 'TIMEOUT'):
            state.pop((owner, pid), None)
    live = {}
    for (owner, pid), kind in state.items():
        if pid and Path(f'/proc/{pid}').exists():
            live[owner] = kind
    return live


def run_job(s, cohort, workload, slot):
    m = calib.manifest(cohort, workload, s.label, calib.Paths(W), agent=s.agent)
    m['context']['slot'] = slot
    path = s.dir / f'manifest-{slot:02d}-{cohort}-{workload}.json'
    done = s.dir / f'job-{slot:02d}-{cohort}-{workload}'
    if done.exists():
        job = done.read_text().strip()
        s.log(f'{cohort} {workload}: reusing finished job={job}')
        return job
    if path.exists():
        m = json.loads(path.read_text())  # a resumed slot keeps its manifest (and so its job id)
    else:
        path.write_text(json.dumps(m, indent=1) + '\n')
    sub = subprocess.run([JOB, 'submit', path], env=ENV, capture_output=True, text=True)
    found = re.search(r'job ([0-9a-f]{12})', sub.stderr)  # "already submitted": resume that job
    job = sub.stdout.strip() or (found.group(1) if found else None)
    if not job:
        raise SystemExit(f'{cohort} {workload}: submit failed: {sub.stderr.strip()}')
    verb = 'resume' if (W / 'jobs' / job / 'started').exists() else 'run'
    runner = subprocess.Popen([JOB, verb, job], env=ENV, stdout=(s.dir / f'run-{job}.log').open('a'),
                              stderr=subprocess.STDOUT)
    s.log(f'{cohort} {workload}: job={job} {verb} load1={s.uptime()}')
    groups = []
    cmds = loads(workload)
    if cmds:
        while True:
            st = subprocess.run([JOB, 'status', job, '--json'], env=ENV, capture_output=True, text=True).stdout
            if json.loads(st or '{}').get('state') == 'running':
                break
            if runner.poll() is not None:
                raise SystemExit(f'{cohort} {workload}: runner exited before running')
            time.sleep(2)
        for c in cmds:
            p = subprocess.Popen(['taskset', '-c', REST, 'bash', '-c', c], start_new_session=True,
                                 stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=ENV)
            groups.append(p)
            s.log(f'{cohort} {workload}: load pgid={p.pid} on {REST}: {c} load1={s.uptime()}')
    try:
        rc = runner.wait()
    finally:
        for p in groups:
            stop_group(s, p)
    s.log(f'{cohort} {workload}: job={job} rc={rc} load1={s.uptime()}')
    if rc != 0:
        raise SystemExit(f'{cohort} {workload}: job {job} rc={rc}')
    done.write_text(job + '\n')
    return job


def stop_group(s, p):
    for sig, wait in ((signal.SIGTERM, 10), (signal.SIGKILL, 5)):
        try:
            os.killpg(p.pid, sig)
        except ProcessLookupError:
            break
        end = time.time() + wait
        while time.time() < end and group_alive(p.pid):
            time.sleep(0.5)
        if not group_alive(p.pid):
            break
    p.wait()
    if group_alive(p.pid):
        s.log(f'WARNING: load group {p.pid} still has members after SIGKILL')
    else:
        s.log(f'load pgid={p.pid} stopped')


def group_alive(pgid):
    return subprocess.run(['pgrep', '-g', str(pgid)], capture_output=True).returncode == 0


def extract(s, job, cohort, workload, slot):
    recs = calib.records(W / 'jobs' / job)
    out = s.dir / f'records-{slot:02d}-{cohort}-{workload}-{job}.jsonl.gz'
    out.write_bytes(gzip.compress(''.join(json.dumps(r, sort_keys=True) + '\n' for r in recs).encode(), mtime=0))
    return recs


def check_correctness(s, recs):
    refs = json.loads((HERE / 'references.json').read_text())
    bad = [r for r in recs if r['status'] == 'ok' and r['digest'] != refs[r['instance']][
        'raw' if r['role'] in calib.M29_ROLES else 'm33']]
    failed = [r for r in recs if r['status'] != 'ok']
    if failed:
        s.log(f'note: {len(failed)} attempt(s) not ok: ' + ', '.join(sorted({r["status"] for r in failed})))
    if bad:
        s.log(f'CORRECTNESS STOP: {len(bad)} attempt(s) with a digest that is not the reference, e.g. '
              f'{bad[0]["attempt"]} {bad[0]["cell"]}.{bad[0]["role"]}')
        raise SystemExit(EXIT_CORRECTNESS)


def walls(recs):
    out = defaultdict(dict)
    for r in recs:
        if r['status'] == 'ok' and r['wall_s']:
            out[(r['cell'], r['role'])][r['rep']] = r['wall_s']
    return out


def idle_aa_ok(s, recs, cohort):
    """§7.3 instrument check on an idle job: pass/fail per cell, values not printed for held-out."""
    v, failed = walls(recs), []
    for c in calib.CELLS:
        if c.cohort != cohort:
            continue
        base = next(r for r in c.roles if r in calib.AA)
        ci = bs.paired_ratio(bs.paired_ratios(v[(c.name, calib.AA[base])], v[(c.name, base)]), seed=f'{c.name} aa')
        g = calib.aa_gate(ci, c.workers)
        if not g.ok:
            failed.append(c.name if cohort == 'held-out' else f'{c.name}: {"; ".join(g.why)}')
    s.log(f'{cohort} idle A/A: ' + ('pass' if not failed else 'FAIL ' + ' | '.join(failed)))
    return not failed


def m5_moved(s, idle_recs, loaded_recs):
    """#1107 stop: W4-32 must perturb m5 (C-E1): loaded − idle m5/a shift with its CI above 0."""
    vi, vl = walls(idle_recs), walls(loaded_recs)
    ri = bs.paired_ratios(vi[('C-E1', 'm5')], vi[('C-E1', 'a')])
    rl = bs.paired_ratios(vl[('C-E1', 'm5')], vl[('C-E1', 'a')])
    d = calib.diff_ci(ri, rl, 'C-E1 m5 W4-32')
    s.log(f'm5 positive control under W4-32: shift {d.median:+.4f} [{d.lo:+.4f}, {d.hi:+.4f}]')
    return d.lo > 0


def wait_for_machine(s, heavy=False, reserved=False):
    while True:
        busy = others_busy()
        mine = {o for o in busy if o.startswith('bench-job-') and (W / 'jobs' / o[len('bench-job-'):]).exists()}
        others = {o: k for o, k in busy.items() if o not in mine}
        released = subprocess.run([RESERVE, 'status'], capture_output=True).returncode == 1
        if (reserved or released) and not (heavy and others):
            return
        s.log(f'waiting: reservation {"up" if not released else "free"}, other bench jobs {others or "none"}')
        time.sleep(60)


def failures():
    p = W / 'sessions' / 'instrument-failures.json'
    return json.loads(p.read_text()) if p.exists() else []


def session(label, seed):
    s = Session(label)
    if len(failures()) >= 2:
        raise SystemExit('two instrument failures already: the campaign is stopped (§7.3)')
    order = calib.session_order(seed)
    s.log(f'session {label} start, seed {seed}, order {order}, C={calib.C}, agent={s.agent}')
    wait_for_machine(s)
    r = subprocess.run([RESERVE, 'reserve', '1,2'], capture_output=True, text=True)
    s.log(f'reserve rc={r.returncode} {r.stdout.strip()}')
    if r.returncode:
        raise SystemExit(2)
    idle = {}
    try:
        for slot, wl in enumerate(order):
            for cohort in ('calibration', 'held-out'):
                wait_for_machine(s, heavy=wl in calib.HEAVY, reserved=True)
                if wl in calib.HEAVY:
                    s.log(f'heavy window {wl} {cohort} begins (announced on #1107)')
                job = run_job(s, cohort, wl, slot)
                recs = extract(s, job, cohort, wl, slot)
                check_correctness(s, recs)
                if wl == 'W0':
                    if not idle_aa_ok(s, recs, cohort):
                        f = failures() + [dict(session=label, slot=slot, cohort=cohort, job=job)]
                        (W / 'sessions' / 'instrument-failures.json').write_text(json.dumps(f, indent=1) + '\n')
                        s.log(f'INSTRUMENT STOP: session {label} labeled instrument-failure ({len(f)} of 2)')
                        raise SystemExit(EXIT_INSTRUMENT)
                    if slot == 0:
                        idle[cohort] = recs
                if wl == 'W4-32' and cohort == 'calibration' and not m5_moved(s, idle['calibration'], recs):
                    s.log('CONTROL STOP: W4-32 did not perturb m5 (#1107 stop condition)')
                    raise SystemExit(EXIT_CONTROL)
        s.log(f'session {label} complete')
    finally:
        r = subprocess.run([RESERVE, 'release'], capture_output=True, text=True)
        s.log(f'release rc={r.returncode} {r.stdout.strip()} {r.stderr.strip()}')


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest='cmd', required=True)
    a = sub.add_parser('session')
    a.add_argument('label')
    a.add_argument('--seed', type=int, default=int(time.strftime('%Y%m%d')))
    b = sub.add_parser('one')
    b.add_argument('cohort', choices=['calibration', 'held-out'])
    b.add_argument('workload', choices=['W0'] + calib.WORKLOADS)
    b.add_argument('label')
    args = p.parse_args()
    if args.cmd == 'session':
        session(args.label, args.seed)
    else:
        s = Session(args.label)
        job = run_job(s, args.cohort, args.workload, 99)
        check_correctness(s, extract(s, job, args.cohort, args.workload, 99))


if __name__ == '__main__':
    main()
