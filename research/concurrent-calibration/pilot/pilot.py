"""#1106 exploratory pilot (protocol §7.1): decides nothing; sizes n, tunes m5, qualifies H-S16.

Usage: python3 -I pilot.py <repo> <workdir> <out>
<workdir> holds target/release/examples/{sig_f4_study,m29_cost_model} built at C, and
bin/{sweep,stream}. Every measurement is a dev-mode bench-job inside a CCD 1-2 reservation that this
script takes once the machine is released, and releases at the end. Held-out cells run idle only.
Progress goes to <out>/events.log, one line per step, so an interrupted pilot is resumable by hand.
"""
import hashlib, json, math, os, random, statistics as st, subprocess, sys, time
from pathlib import Path

REPO, W, OUT = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
OUT.mkdir(parents=True, exist_ok=True)
C = (W / 'C').read_text().strip()
SIG, M29 = W / 'target/release/examples/sig_f4_study', W / 'target/release/examples/m29_cost_model'
SWEEP, STREAM = W / 'bin/sweep', W / 'bin/stream'
REST = '0-7,24-71,88-127'
JOB, RESERVE = REPO / 'tools/bench-job', REPO / 'tools/bench-reserve.sh'
ENV = dict(os.environ, ZEEBRA_BENCH_JOBS=str(W / 'jobs'), RUSTC_WRAPPER='', TMPDIR=str(W / 'tmp'))
REPS = 9
AGENT = subprocess.run([REPO / 'scripts/agent/zb-claim.sh', 'id'], capture_output=True, text=True).stdout.strip()


def log(msg):
    line = f"{time.strftime('%Y-%m-%dT%H:%M:%S%z')} {msg}"
    print(line, flush=True)
    with (OUT / 'events.log').open('a') as f:
        f.write(line + '\n')


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def arm(name, binary, argv, recipe, workers=None, comparand=None):
    a = dict(name=name, commit=C, binary=str(binary), sha256=sha(binary),
             build=dict(profile='release', flags='.cargo/config.toml (x86-64-v3, fat LTO, 1 CGU)', recipe=recipe), argv=argv)
    if comparand:  # a binary not built from C's archive names its own provenance
        a['build']['comparand'] = comparand
    if workers:
        a['workers'] = workers
    return a


SIG_ARGV = ['--field', '{field}', '--name', '{name}', '{flag1}', '--engine', 'entry', '--workers', '{workers}',
            '--digest-only', '--wall-s', '600']
SIG_RECIPE = f'git archive {C} | tar -x; cargo build --release --locked --features research-sigf4 --example sig_f4_study'
M29_RECIPE = f'git archive {C} | tar -x; cargo build --release --locked --features external-runners --example m29_cost_model'


def sig_inst(field, name, generate=False, **extra):
    return dict(name=f'{field}/{name}', params=dict(field=field, name=name, flag1='--generate' if generate else '--digest-only', **extra))


def manifest(label, condition, arms, instances, workers):
    return {'schema': 'bench-job-manifest-v1', 'mode': 'dev',
            'context': dict(issue=1106, label='pilot', step=label, condition=condition, agent=AGENT, commit=C,
                            session=time.strftime('%Y-%m-%dT%H:%M:%S%z')),
            'arms': arms, 'instances': instances,
            'run': dict(workers=workers, cpus='8-23', repetitions=REPS, interleave='rotate', seeds=[0], retries=0,
                        limits=dict(wall_seconds=600, kill_after_seconds=60, rss_bytes=17179869184, live_bytes=None))}


def run_job(label, m, load=None):
    done = OUT / f'job-{label}'
    if done.exists():  # resume: a finished job is kept, never re-run
        job = done.read_text().strip()
        log(f'{label}: reusing done job={job}')
        return job
    path = OUT / f'manifest-{label}.json'
    path.write_text(json.dumps(m, indent=1) + '\n')
    job = subprocess.run([JOB, 'submit', path], env=ENV, capture_output=True, text=True, check=True).stdout.strip()
    log(f'{label}: job={job} load={load or "W0"}')
    runner = subprocess.Popen([JOB, 'run', job], env=ENV, stdout=(OUT / f'run-{label}.log').open('w'), stderr=subprocess.STDOUT)
    loader = None
    if load:
        while json.loads(subprocess.run([JOB, 'status', job, '--json'], env=ENV, capture_output=True, text=True).stdout or '{}').get('state') != 'running':
            if runner.poll() is not None:
                raise SystemExit(f'{label}: runner exited before starting')
            time.sleep(2)
        loader = subprocess.Popen(['setsid', 'taskset', '-c', REST, str(STREAM), '32'], start_new_session=True)
        log(f'{label}: W4-32 started pid={loader.pid}')
    rc = runner.wait()
    if loader:
        os.killpg(loader.pid, 15)
        loader.wait()
    log(f'{label}: rc={rc}')
    if rc == 0:
        done.write_text(job + '\n')
    return job


def walls(job):
    """{(instance, workers, arm): {rep: wall_s}} over exit-0 attempts."""
    out = {}
    for line in (W / 'jobs' / job / 'journal' / 'journal.jsonl').open():
        r = json.loads(line)
        md = r.get('metadata') or {}
        if r.get('kind') == 'exit' and md.get('exit') == 0:
            c = r['cell']
            out.setdefault((c['instance'], c['workers'], c['arm']), {})[c['rep']] = md['wall_seconds']
    return out


def med(d):
    return st.median(d.values())


def main():
    log(f'pilot start C={C} agent={AGENT}')
    aa = REPO / 'research/bench-telemetry-overhead/session-1/events.log'
    Z = Path(f'/sys/fs/cgroup/user.slice/user-{os.getuid()}.slice/user@{os.getuid()}.service/zbbench.slice')
    while True:  # after #1105's A/A has had its window, and with nobody else's reservation up
        released = subprocess.run([RESERVE, 'status'], capture_output=True).returncode == 1
        busy = any(p.read_text().strip() for p in Z.glob('*/cgroup.procs'))
        if released and not busy and aa.exists() and 'release rc=' in aa.read_text():
            break
        time.sleep(20)
    r = subprocess.run([RESERVE, 'reserve', '1,2'], capture_output=True, text=True)
    log(f'reserve rc={r.returncode} {r.stdout.strip()}')
    if r.returncode:
        raise SystemExit(2)
    results = dict(C=C, binaries={p.name: sha(p) for p in (SIG, M29, SWEEP, STREAM)}, reservation='CCDs 1-2 (fallback, §5.3)')
    try:
        sig_a = lambda *n: [arm(x, SIG, SIG_ARGV, SIG_RECIPE) for x in n]
        one = [sig_inst('wide64', 'eco-12'), sig_inst('gf32003', 'mq-random-10'), sig_inst('wide64', 'cyclic-7')]
        sixteen = [sig_inst('gf32003', 'mq-random-10'), sig_inst('gf32003', 'katsura-11'),
                   sig_inst('gf31', 'mq-dense-15-s15', generate=True)]
        jobs = {}
        jobs['S1-W0'] = run_job('S1-W0', manifest('S1', 'W0', sig_a('a', 'a2'), one, [1]))
        jobs['S16-W0'] = run_job('S16-W0', manifest('S16', 'W0', sig_a('a', 'a2'), sixteen, [16]))
        m29 = lambda name, pm: arm(name, M29, ['--target', '{target}', '--workers', '{workers}', '--pair-multiples', pm,
                                               '--wall-s', '600'], M29_RECIPE)
        p_arms = [m29('every', 'every'), m29('distinct', 'distinct'), m29('distinct2', 'distinct')]
        p_inst = [dict(name=t, params=dict(target=t)) for t in ('mq10-32003', 'cyclic7-wide64', 'katsura11-wide64', 'katsura11-m31')]
        jobs['P-W0'] = run_job('P-W0', manifest('P', 'W0', p_arms, p_inst, [16]))
        src = REPO / 'research/concurrent-calibration/sweep.c'
        sw = [arm(f'sweep{p}-{mib}', SWEEP, ['{workers}', str(p), str(mib)], f'cc -O2 -pthread {src.relative_to(REPO)}',
                  comparand=f'sweep.c sha256 {sha(src)} (#1106 pilot; not in {C[:8]})')
              for mib in (64, 32) for p in (0, 1)]
        jobs['SW-W0'] = run_job('SW-W0', manifest('SW', 'W0', sw, [dict(name='sweep', params={})], [1, 16]))

        # §4.2 steps 1-3
        idle = {**walls(jobs['S1-W0']), **walls(jobs['S16-W0'])}
        swp = walls(jobs['SW-W0'])
        tuning = {}
        for (inst, w, a), d in idle.items():
            if a != 'a':
                continue
            t_a = med(d)
            for mib in (64, 32):  # §4.2: halve the arrays once if allocation alone exceeds the 5% budget
                t0, t1 = med(swp[('sweep', w, f'sweep0-{mib}')]), med(swp[('sweep', w, f'sweep1-{mib}')])
                if t0 <= 0.05 * t_a:
                    break
            passes = max(1, round((0.05 * t_a - t0) / (t1 - t0)))
            tuning[f'{inst}@{w}w'] = dict(threads=w, t_A=t_a, t_0=t0, t_1=t1, passes=passes, mib=mib,
                                          t0_exceeds=t0 > 0.05 * t_a)
        log('m5 tuning ' + json.dumps(tuning))

        # §4.2 step 4: validate, rescale once
        wrapper = W / 'bin/m5.sh'
        wrapper.write_text(f'#!/bin/sh\np=$1; t=$2; m=$3; shift 3\n"{SIG}" "$@"; rc=$?\n"{SWEEP}" "$t" "$p" "$m"\nexit $rc\n')
        wrapper.chmod(0o755)
        m5_argv = ['{passes}', '{workers}', '{mib}', *SIG_ARGV]
        for attempt in (1, 2):
            for w, insts in ((1, one), (16, sixteen)):
                todo = [dict(i, params=dict(i['params'], passes=tuning[f"{i['name']}@{w}w"]['passes'], mib=tuning[f"{i['name']}@{w}w"]['mib'])) for i in insts
                        if not tuning[f"{i['name']}@{w}w"].get('accepted')]
                if not todo:
                    continue
                label = f'V{w}-try{attempt}'
                job = run_job(label, manifest(label, 'W0', [arm('a', SIG, SIG_ARGV, SIG_RECIPE),
                                                            arm('m5', wrapper, m5_argv, SIG_RECIPE + '; m5 wrapper + sweep')], todo, [w]))
                v = walls(job)
                for i in todo:
                    key = f"{i['name']}@{w}w"
                    ratio = st.median(b / a for r, a in v[(i['name'], w, 'a')].items()
                                      if (b := v.get((i['name'], w, 'm5'), {}).get(r)) is not None)
                    t = tuning[key]
                    t[f'validation{attempt}'] = ratio
                    if 1.04 <= ratio <= 1.06:
                        t['accepted'] = True
                    elif attempt == 1:
                        t['passes'] = max(1, round(t['passes'] * 0.05 / (ratio - 1))) if ratio > 1 else t['passes'] * 2
                    else:
                        t['untuned'] = True
        log('m5 validated ' + json.dumps(tuning))
        results['m5'] = tuning

        # The calibration A/A under W4-32 (held-out cells never run loaded). §4.3's qualification is
        # read from P-W0 afterwards, by summarize.py.
        jobs['S1-W4'] = run_job('S1-W4', manifest('S1', 'W4-32', sig_a('a', 'a2'), one[:2], [1]), load='W4-32')
        jobs['S16-W4'] = run_job('S16-W4', manifest('S16', 'W4-32', sig_a('a', 'a2'), sixteen[:1], [16]), load='W4-32')
        jobs['P-W4'] = run_job('P-W4', manifest('P', 'W4-32', p_arms, p_inst[:1], [16]), load='W4-32')
        results['jobs'] = jobs
    finally:
        r = subprocess.run([RESERVE, 'release'], capture_output=True, text=True)
        log(f'release rc={r.returncode} {r.stdout.strip()} {r.stderr.strip()}')
        (OUT / 'results.json').write_text(json.dumps(results, indent=1) + '\n')


if __name__ == '__main__':
    main()
