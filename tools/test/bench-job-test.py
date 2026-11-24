import hashlib
import importlib.machinery
import importlib.util
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest

TOOLS = Path(__file__).resolve().parents[1]
BENCH_JOB = TOOLS / 'bench-job'
_loader = importlib.machinery.SourceFileLoader('bench_job', str(BENCH_JOB))
_spec = importlib.util.spec_from_loader('bench_job', _loader)
bj = importlib.util.module_from_spec(_spec)
_loader.exec_module(bj)
aj = bj.aj

# A synthetic child: its first argument picks the behaviour, so one binary covers every outcome.
CHILD = '''#!/bin/sh
case "$1" in
  ok) echo '{"status":"ok"}' ;;
  emit) echo '{"selection_outcome":"'"$2"'","verified":'"$3"'}' ;;
  report) echo '{"status":"complete","basis_sha256":"'"$2"'","statistics":{"symbolic_ns":2000000,"elimination_ns":3000000}}' ;;
  fail) echo boom >&2; exit 1 ;;
  selfkill) kill -TERM $$ ;;
  sleep) exec sleep "$2" ;;
  once) [ -e "$2" ] && exit 0; : > "$2"; [ "$3" = fail ] && exit 1; exec sleep 30 ;;
  spin) i=0; while [ "$i" -lt "$2" ]; do i=$((i + 1)); done; echo '{"status":"ok"}' ;;
esac
'''
FAKE_RESERVE = ('#!/bin/sh\n[ "$1" = run ] || exit 64\nshift 3\n'
                '[ -z "${RESERVE_LOG:-}" ] || echo "exclusive=${ZEEBRA_BENCH_RESERVE_EXCLUSIVE:-}" >"$RESERVE_LOG"\n'
                'exec "$@"\n')
COMMIT = 'c0ffee' * 6 + 'c0ff'
FIXTURE = TOOLS / 'test' / 'fixtures' / 'bench-job-competitive.json'
K4 = dict(problem='katsura-4', problem_digest='ab' * 32, family='katsura', task='reduced-grobner-basis',
          field=dict(name='GF(18446744069414584321)', characteristic=18446744069414584321, extension_degree=1,
                     defining_polynomial=None), order='grevlex', variable_count=5)
REFS = {'goldilocks/katsura-4': dict(basis_digest='d1', checked_against='Singular std, redSB',
                                     invariants=dict(basis_cardinality=2, leading_monomials=['x0^2', 'x1']))}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class BenchJobTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix='bench-job-test-'))
        self.jobs = self.tmp / 'jobs'
        self.child = self.tmp / 'build' / 'child'
        self.child.parent.mkdir()
        self.child.write_text(CHILD)
        self.child.chmod(0o755)
        reserve = self.tmp / 'fake-reserve.sh'
        reserve.write_text(FAKE_RESERVE)
        reserve.chmod(0o755)
        context = self.tmp / 'fake-context.sh'
        context.write_text('echo \'{"fake":true}\'\n')
        # Cycle counting is off unless a test turns it on: it attaches a perf process to every attempt.
        self.env = dict(os.environ, ZEEBRA_BENCH_JOBS=str(self.jobs), ZEEBRA_BENCH_JOB_RESERVE=str(reserve),
                        ZEEBRA_CPU_CONTEXT=str(context), ZEEBRA_BENCH_PERF='')
        self.saved = dict(os.environ)
        os.environ.update(self.env)

    def tearDown(self):
        os.environ.clear()
        os.environ.update(self.saved)
        shutil.rmtree(self.tmp)

    def manifest(self, instances=(('i1', ['ok']), ('i2', ['ok'])), reps=2, retries=0, wall=30, **over):
        arm = lambda name: dict(name=name, commit=COMMIT, binary=str(self.child), sha256=sha(self.child),
                                build=dict(profile='release', flags='-C target-cpu=x86-64-v3',
                                           recipe=f'git archive {COMMIT} | tar -x -C src && cargo build --release'),
                                argv=['{a0}', '{a1}', '{a2}'])
        m = dict(schema=bj.SCHEMA, mode='dev', context=dict(issue=967, agent='test@branch'),
                 arms=[arm('a'), arm('b')],
                 instances=[dict(name=n, params=dict(zip(('a0', 'a1', 'a2'), list(a) + ['', '', '']))) for n, a in instances],
                 run=dict(workers=[1], cpus='0', repetitions=reps, interleave='rotate', seeds=[0], retries=retries,
                          limits=dict(wall_seconds=wall, kill_after_seconds=2, rss_bytes=None, live_bytes=None)))
        for k, v in over.items():
            m[k] = v
        return m

    def submit(self, manifest):
        path = self.tmp / 'manifest.json'
        path.write_text(json.dumps(manifest))
        return self.cli('submit', str(path))

    def cli(self, *args, check=None):
        r = subprocess.run([sys.executable, str(BENCH_JOB), *args], env=self.env, capture_output=True, text=True,
                           timeout=120)
        if check is not None:
            self.assertEqual(r.returncode, check, r.stderr)
        return r

    def job(self, manifest):
        r = self.submit(manifest)
        self.assertEqual(r.returncode, 0, r.stderr)
        return r.stdout.split()[-1]

    def state(self, job):
        return aj.load(self.jobs / job / 'journal')

    def background(self, job, *extra):
        return subprocess.Popen([sys.executable, str(BENCH_JOB), 'run', job, *extra], env=self.env,
                                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    def wait_current(self, job, timeout=30):
        current = self.jobs / job / 'current.json'
        deadline = time.time() + timeout
        while time.time() < deadline:
            try:
                return json.loads(current.read_text())
            except (OSError, ValueError):
                time.sleep(0.05)
        self.fail('no attempt started')

    # Submit refuses a binary whose SHA-256 differs from the manifest, and an unknown mode.
    def test_submit_refuses_hash_mismatch_and_bad_mode(self):
        m = self.manifest()
        m['arms'][0]['sha256'] = '0' * 64
        r = self.submit(m)
        self.assertEqual(r.returncode, 64)
        self.assertIn('sha256', r.stderr)
        r = self.submit(self.manifest(mode='fast'))
        self.assertEqual(r.returncode, 64)
        self.assertIn('mode', r.stderr)
        self.assertFalse(any(p.is_dir() for p in self.jobs.glob('*')) if self.jobs.exists() else False)

    # Submit refuses a binary inside a git checkout with uncommitted changes, and a recipe without git archive.
    def test_submit_refuses_dirty_tree_and_non_archive_recipe(self):
        repo = self.tmp / 'build'
        git = lambda *a: subprocess.run(['git', '-C', str(repo), *a], check=True, capture_output=True)
        git('init', '-q')
        git('-c', 'user.name=t', '-c', 'user.email=t@t', 'add', 'child')
        git('-c', 'user.name=t', '-c', 'user.email=t@t', 'commit', '-qm', 'x')
        (repo / 'child').write_text(CHILD + '\n')
        m = self.manifest()
        for arm in m['arms']:
            arm['sha256'] = sha(self.child)
        r = self.submit(m)
        self.assertEqual(r.returncode, 64)
        self.assertIn('dirty', r.stderr)
        shutil.rmtree(repo / '.git')
        m['arms'][1]['build']['recipe'] = 'cargo build --release'
        r = self.submit(m)
        self.assertEqual(r.returncode, 64)
        self.assertIn('git archive', r.stderr)

    # Submit copies the binary, names the job by the manifest digest, queues it, and refuses a resubmit.
    def test_submit_copies_and_queues(self):
        m = self.manifest()
        job = self.job(m)
        self.assertEqual(job, hashlib.sha256(bj.canonical(m)).hexdigest()[:12])
        self.assertEqual(sha(self.jobs / job / 'bin' / 'a' / 'child'), sha(self.child))
        self.assertIn(job, (self.jobs / 'queue').read_text())
        self.assertEqual(bj.job_status(self.jobs / job)['state'], 'queued')
        self.assertEqual(self.submit(m).returncode, 64)

    # The plan is a pure function of the manifest: instances x workers x seeds in turn, arms rotated per rep.
    def test_plan_is_deterministic(self):
        m = self.manifest(reps=3)
        cells = bj.expand(m)
        self.assertEqual(cells, bj.expand(json.loads(json.dumps(m))))
        self.assertEqual(len(cells), 3 * 2 * 2)
        self.assertEqual([c['arm'] for c in cells if c['instance'] == 'i1'], ['a', 'b', 'b', 'a', 'a', 'b'])
        self.assertEqual(bj.attempt_id('abc', 4, 1), 'abc:4:1')

    # A job runs to done, and resuming a finished job repeats nothing.
    def test_run_then_resume_repeats_nothing(self):
        job = self.job(self.manifest())
        self.cli('run', job, check=0)
        self.assertEqual(bj.job_status(self.jobs / job)['state'], 'done')
        self.cli('resume', job, check=0)
        state = self.state(job)
        self.assertEqual([a['status'] for a in state['attempts']], ['ok'] * 8)
        self.assertEqual(state['stop']['reason'], 'complete')
        self.assertEqual(state['attempts'][0]['metadata']['attempt_id'], f'{job}:0:0')
        self.assertEqual(state['attempts'][0]['stdout'], b'{"status":"ok"}\n')

    # A runner killed mid-attempt resumes from the first index without a recorded exit, duplicating none.
    def test_sigkill_then_resume_completes_without_duplicates(self):
        job = self.job(self.manifest(instances=(('i1', ['sleep', '0.4']), ('i2', ['ok']))))
        proc = self.background(job)
        deadline = time.time() + 30
        while time.time() < deadline:
            current = self.wait_current(job)
            if current['index'] >= 2:
                break
            time.sleep(0.05)
        os.kill(current['runner_pid'], signal.SIGKILL)
        proc.wait(timeout=30)
        self.assertEqual(bj.job_status(self.jobs / job)['state'], 'interrupted')
        self.cli('resume', job, check=0)
        state = self.state(job)
        self.assertEqual(sorted(a['index'] for a in state['attempts']), list(range(8)))
        self.assertTrue(all(a['status'] == 'ok' and a['try'] == 0 for a in state['attempts']))

    # Cancel stops a running attempt by SIGINT, journals a stop, and resume needs --force-uncancel.
    def test_cancel_records_stop_and_blocks_resume(self):
        marker = self.tmp / 'marker'
        job = self.job(self.manifest(instances=(('i1', ['once', str(marker)]),), reps=1))
        proc = self.background(job)
        self.wait_current(job)
        started = time.time()
        self.cli('cancel', job, check=0)
        proc.wait(timeout=30)
        self.assertLess(time.time() - started, 12)
        self.assertEqual(bj.job_status(self.jobs / job)['state'], 'cancelled')
        state = self.state(job)
        self.assertEqual(state['stop']['reason'], 'cancelled')
        self.assertEqual(state['attempts'][0]['status'], 'cancelled')
        self.assertNotEqual(self.cli('resume', job).returncode, 0)
        self.cli('resume', job, '--force-uncancel', check=0)
        state = self.state(job)
        self.assertEqual([(a['index'], a['try'], a['status']) for a in state['attempts']],
                         [(0, 0, 'cancelled'), (0, 1, 'ok'), (1, 0, 'ok')])
        self.assertEqual(bj.job_status(self.jobs / job)['state'], 'done')

    # A child past its wall limit is stopped by timeout and journaled as a timeout, not a failure.
    def test_timeout_is_journaled(self):
        job = self.job(self.manifest(instances=(('i1', ['sleep', '20']),), reps=1, wall=1))
        self.cli('run', job, check=0)
        attempts = self.state(job)['attempts']
        self.assertEqual([a['status'] for a in attempts], ['timeout', 'timeout'])
        # 124 when the child honours timeout's SIGINT; ubuntu-latest's timeout/sleep reach --kill-after (137).
        self.assertIn(attempts[0]['metadata']['exit'], (124, 137))

    # Failed tries are retried up to the manifest's budget and every try is kept with its output.
    def test_failures_are_preserved_and_retried(self):
        marker = self.tmp / 'flaky'
        job = self.job(self.manifest(instances=(('bad', ['fail']), ('flaky', ['once', str(marker), 'fail'])),
                                     reps=1, retries=1))
        self.cli('run', job, check=0)
        rows = [(a['cell']['instance'], a['cell']['arm'], a['try'], a['status']) for a in self.state(job)['attempts']]
        self.assertEqual(rows, [('bad', 'a', 0, 'failed'), ('bad', 'a', 1, 'failed'),
                                ('bad', 'b', 0, 'failed'), ('bad', 'b', 1, 'failed'),
                                ('flaky', 'a', 0, 'failed'), ('flaky', 'a', 1, 'ok'), ('flaky', 'b', 0, 'ok')])
        self.assertEqual(self.state(job)['attempts'][0]['stderr'], b'boom\n')
        self.assertEqual(bj.job_status(self.jobs / job)['outcomes'], dict(failed=5, ok=2))

    # A byte changed in a submitted binary makes the next attempt refuse with a typed stop record.
    def test_tampered_binary_is_refused(self):
        job = self.job(self.manifest())
        copy = self.jobs / job / 'bin' / 'b' / 'child'
        copy.chmod(0o755)
        copy.write_bytes(copy.read_bytes() + b'#')
        r = self.cli('run', job, check=3)
        self.assertIn('binary-mismatch', r.stderr)
        state = self.state(job)
        self.assertEqual(state['stop']['reason'], 'binary-mismatch')
        self.assertEqual(state['stop']['arm'], 'b')
        self.assertEqual(len(state['attempts']), 1)
        self.assertEqual(bj.job_status(self.jobs / job)['state'], 'failed')

    # run --next takes the oldest queued job and leaves the rest queued.
    def test_run_next_takes_the_oldest(self):
        first = self.job(self.manifest(reps=1))
        second = self.job(self.manifest(reps=2))
        self.cli('run', '--next', check=0)
        self.assertEqual(bj.job_status(self.jobs / first)['state'], 'done')
        self.assertEqual(bj.job_status(self.jobs / second)['state'], 'queued')
        self.assertIn(second, self.cli('status', check=0).stdout)

    def fake_context(self, **over):
        snap = dict(at='2026-11-21T00:00:00.000Z', load1=0.5, compilers=0, runner_workers=0, benchlock_open=[],
                    clock='boost', rapl_uj=None, cpus=[dict(cpu=0, khz=4000000)],
                    stat=[dict(cpu=0, role='bench', busy=10, total=100), dict(cpu=64, role='sibling', busy=0, total=100)],
                    rest_stat=dict(busy=0, total=100, cpus=1))
        snap.update(over)
        (self.tmp / 'fake-context.sh').write_text(f"echo '{json.dumps(snap)}'\n")

    # Each attempt's exit metadata carries the §11.2 verdict, and the complete stop the session's.
    def test_contamination_is_journaled_per_attempt_and_session(self):
        self.fake_context()
        job = self.job(self.manifest(reps=1))
        self.cli('run', job, check=0)
        state = self.state(job)
        c = state['attempts'][0]['metadata']['contamination']
        self.assertEqual(c['verdict']['contaminated'], False)
        self.assertEqual(c['mode'], 'dev')
        self.assertIn('bench_foreign', c['metrics'])
        # #1105: the child tree's switches and faults are journaled, and the telemetry keys exist,
        # None here because the fake snapshot predates them.
        rusage = state['attempts'][0]['metadata']['rusage']
        self.assertEqual(set(rusage), {'nvcsw', 'nivcsw', 'majflt', 'minflt', 'inblock', 'oublock'})
        self.assertEqual(c['metrics']['rusage'], rusage)
        self.assertIsNone(c['metrics']['psi'])
        session = state['stop']['contamination']
        self.assertEqual((session['contaminated'], session['total'], session['void']), (0, 4, False))

    # Without usable snapshots the verdict is an explicit error, never a silent clean bill.
    def test_contamination_without_snapshots_is_an_error(self):
        c = bj.contamination(dict(before=dict(fake=True), after=dict(fake=True), cpu_seconds=1.0, freq=None),
                             self.manifest(), 'job')
        self.assertEqual(c['verdict'], None)
        self.assertIn('error', c)

    # The child's CPU time is what separates its own bench busy time from foreign time.
    def test_contamination_uses_own_cpu_time(self):
        before = dict(at='2026-11-21T00:00:00Z', load1=0, compilers=0, cpus=[dict(cpu=0, khz=1)],
                      stat=[dict(cpu=0, role='bench', busy=0, total=0)], rest_stat=None)
        after = dict(before, at='2026-11-21T00:00:10Z', stat=[dict(cpu=0, role='bench', busy=1000, total=1000)])
        r = dict(before=before, after=after, cpu_seconds=9.0, freq=None)
        self.assertTrue(bj.contamination(r, self.manifest(), 'job')['verdict']['contaminated'])
        r['cpu_seconds'] = 10.0
        self.assertFalse(bj.contamination(r, self.manifest(), 'job')['verdict']['contaminated'])
        # Harness time on the attempt's CPUs (own_cpu_s, when no spare CPU could take it) is own time too.
        r.update(cpu_seconds=9.0, own_cpu_s=10.0)
        self.assertFalse(bj.contamination(r, self.manifest(), 'job')['verdict']['contaminated'])

    # The clock rule's groups are arms within a cell: instance, worker count and arm each split a group.
    def test_clock_group(self):
        c = dict(instance='x', workers=1, arm='a')
        for other in (dict(c, instance='y'), dict(c, workers=16), dict(c, arm='b')):
            self.assertNotEqual(bj.clock_group(c), bj.clock_group(other))
        self.assertEqual(bj.clock_group(c), bj.clock_group(dict(c, rep=3, seed=1)))

    @staticmethod
    def clock_rows(khz_by_arm):
        """(attempt_id, cell, contamination) rows in one cell, clean but for the clock: arm -> per-rep kHz."""
        rows = []
        for arm, khz in khz_by_arm.items():
            for rep, k in enumerate(khz):
                metrics = dict(sibling_busy={}, bench_foreign=0.0, median_khz=k, rest_load=0.0, load1=0.0,
                               compilers=0, runner_workers=0, benchlock_owners=[])
                rows.append((f'job:{len(rows)}:0', dict(instance='wide64/eco-12', workers=1, rep=rep, arm=arm),
                             dict(metrics=metrics)))
        return rows

    # A mixed-solver cell whose arms each hold a steady clock is clean, though the arms' clocks differ.
    def test_mixed_solver_cell_with_steady_arms_is_not_void(self):
        rows = self.clock_rows(dict(grobx=[2670000] * 5, sig=[3990000] * 5, grs=[4540000] * 5))
        s = bj.session_verdict_of(rows, 'dev', 'bench-job-job')
        self.assertEqual((s['contaminated'], s['total'], s['void']), (0, 15, False))
        self.assertEqual((s['version'], s['grouping']), (bj.VERDICT_VERSION, 'arm'))
        self.assertEqual(s['median_khz']['wide64/eco-12@1w/grobx'], 2670000)
        # The same attempts judged per cell, as verdict v1 did, void the session on clock alone.
        self.assertTrue(bj.session_verdict_of(rows, 'dev', 'bench-job-job', grouping='cell')['void'])

    # One arm whose clock drifts across its repetitions is contaminated, and here voids the session.
    def test_mixed_solver_cell_with_a_drifting_arm_is_void(self):
        rows = self.clock_rows(dict(grobx=[2000000, 2400000, 2670000, 3000000, 3400000],
                                    sig=[3990000] * 5, grs=[4540000] * 5))
        s = bj.session_verdict_of(rows, 'dev', 'bench-job-job')
        self.assertEqual((s['contaminated'], s['void']), (4, True))
        self.assertEqual(set(s['flagged']), {'job:0:0', 'job:1:0', 'job:3:0', 'job:4:0'})

    # The harness runs on run.cpus outside the attempt when there are any; otherwise none are spare.
    def test_harness_cpus(self):
        m = self.manifest()
        m['run']['cpus'] = '8-11'
        self.assertEqual(bj.harness_cpus(m, '8'), {9, 10, 11})
        self.assertEqual(bj.harness_cpus(m, '8-11'), set())

    # Publication mode refuses to start while a compiler runs, and journals the refusal.
    def test_publication_refuses_with_a_compiler(self):
        self.fake_context(compilers=1)
        job = self.job(self.manifest(mode='publication'))
        r = self.cli('run', job)
        self.assertEqual(r.returncode, bj.EXIT_REFUSED, r.stderr)
        stop = self.state(job)['stop']
        self.assertEqual(stop['reason'], 'mode-refused')
        self.assertIn('1 compiler process(es)', stop['refusals'])
        self.assertEqual(self.state(job)['attempts'], [])

    def run_with_refusals(self, job, busy_after, clears):
        """`run_job` in process, on a fake clock, with a compiler that appears after each attempt in
        `busy_after` and clears after the next of `clears` polls (None: never). Returns the attempt
        starts as (fake seconds, busy) and the JobError `run_job` raised, if any."""
        clock = dict(now=0.0, busy=False, sleeps=0)
        clears = list(clears)
        starts = []

        class FakeTime:
            monotonic = staticmethod(lambda: clock['now'])
            time = staticmethod(time.time)

            @staticmethod
            def sleep(seconds):
                clock['now'] += seconds
                clock['sleeps'] += 1
                if clears[0] is not None and clock['sleeps'] >= clears[0]:
                    clock['busy'], clock['sleeps'] = False, 0
                    clears.pop(0)

        def snapshot(cpus):
            return dict(at='2026-11-23T00:00:00.000Z', load1=0.5, compilers=int(clock['busy']), runner_workers=0,
                        benchlock_open=[], clock='boost', rapl_uj=None, cpus=[dict(cpu=0, khz=4000000)],
                        stat=[dict(cpu=0, role='bench', busy=10, total=100)],
                        rest_stat=dict(busy=0, total=100, cpus=1))

        def run_attempt(m, command, cpus, *_args, **_kw):
            starts.append((clock['now'], clock['busy']))
            if len(starts) - 1 in busy_after:
                clock['busy'] = True
            quiet = snapshot(cpus)
            return dict(cpus=cpus, process_wall_ns=1_000_000, returncode=0, cpu_seconds=0.001,
                        peak_rss_bytes=1 << 20, solver_peak_rss_bytes=None, rss_guard_rc=None,
                        rss_guard_stderr='', before=quiet, after=quiet, freq=None, perf=None, stopped=False,
                        stdout=b'{"status":"ok"}\n', stderr=b'', harness_cpu_seconds=0.0, own_cpu_s=0.001)

        saved = bj.time, bj.run_attempt, bj.campaign.snapshot
        bj.time, bj.run_attempt, bj.campaign.snapshot = FakeTime, run_attempt, snapshot
        try:
            bj.run_job(self.jobs / job)
            return starts, None
        except bj.JobError as e:
            return starts, e
        finally:
            bj.time, bj.run_attempt, bj.campaign.snapshot = saved

    # A compiler that starts between attempts holds the next attempt until it clears (#1090).
    def test_publication_waits_for_a_refusal_between_attempts(self):
        m = self.manifest(mode='publication', reps=1)
        m['run']['mode_wait_seconds'] = 600
        job = self.job(m)
        starts, error = self.run_with_refusals(job, busy_after={0}, clears=[3])
        self.assertIsNone(error)
        self.assertEqual(len(starts), 4)
        self.assertEqual([busy for _, busy in starts], [False] * 4)
        self.assertEqual(starts[1][0], 3 * bj.MODE_POLL_SECONDS)
        state = self.state(job)
        self.assertEqual(state['stop']['reason'], 'complete')
        waits = [a['metadata']['mode_wait'] for a in state['attempts']]
        self.assertEqual(waits[0], dict(waited_seconds=0, refusals=[]))
        self.assertEqual(waits[1]['waited_seconds'], 3 * bj.MODE_POLL_SECONDS)
        self.assertIn('1 compiler process(es)', waits[1]['refusals'])

    # The wait budget is the job's, not each attempt's: once spent, the job stops mode-refused (#1090).
    def test_publication_wait_exhausts_the_remaining_budget(self):
        m = self.manifest(mode='publication', reps=1)
        m['run']['mode_wait_seconds'] = 2.5 * bj.MODE_POLL_SECONDS
        job = self.job(m)
        # One poll's wait before attempt 1 leaves 1.5 polls; before attempt 2 the compiler never clears.
        starts, error = self.run_with_refusals(job, busy_after={0, 1}, clears=[1, None])
        self.assertEqual(starts, [(0, False), (bj.MODE_POLL_SECONDS, False)])
        self.assertIsNotNone(error)
        self.assertEqual(error.code, bj.EXIT_REFUSED)
        state = self.state(job)
        self.assertEqual(len(state['attempts']), 2)
        stop = state['stop']
        self.assertEqual(stop['reason'], 'mode-refused')
        self.assertEqual(stop['attempt'], bj.attempt_id(job, 2, 0))
        self.assertIn('1 compiler process(es)', stop['refusals'])
        # A per-attempt budget would have waited two polls here.
        self.assertEqual(stop['waited_seconds'], bj.MODE_POLL_SECONDS)

    # Publication mode starts when the machine is quiet, under an exclusive rather than CCD lock.
    def test_publication_runs_exclusive_when_quiet(self):
        self.fake_context()
        log = self.tmp / 'reserve.log'
        self.env['RESERVE_LOG'] = str(log)
        job = self.job(self.manifest(mode='publication', reps=1))
        self.cli('run', job, check=0)
        self.assertEqual(log.read_text().strip(), 'exclusive=1')
        dev = self.job(self.manifest(reps=1, instances=(('i3', ['ok']),)))
        self.cli('run', dev, check=0)
        self.assertEqual(log.read_text().strip(), 'exclusive=')

    # An arm with its own `workers` runs only at those counts; a count outside run.workers is refused.
    def test_arm_workers_restrict_the_plan(self):
        m = self.manifest(reps=1)
        m['run'].update(workers=[1, 2], cpus='0-1')
        m['arms'][1]['workers'] = [2]
        cells = [(c['instance'], c['workers'], c['arm']) for c in bj.expand(m)]
        self.assertEqual([c for c in cells if c[0] == 'i1'], [('i1', 1, 'a'), ('i1', 2, 'a'), ('i1', 2, 'b')])
        m['arms'][1]['workers'] = [4]
        with self.assertRaisesRegex(bj.JobError, 'workers'):
            bj.validate(m)

    # The manifest's output budget reaches the journal's limits; a non-positive or non-integer one is refused (#1020).
    def test_output_budget_is_read_and_validated(self):
        m = self.manifest(reps=1)
        self.assertEqual(bj.journal_limits(m)['output_bytes'], 1 << 30)
        m['run']['limits']['output_bytes'] = 4 << 30
        bj.validate(m)
        self.assertEqual(bj.journal_limits(m)['output_bytes'], 4 << 30)
        for bad in (0, 1.5, '4G', None):
            m['run']['limits']['output_bytes'] = bad
            with self.assertRaisesRegex(bj.JobError, 'output_bytes'):
                bj.validate(m)

    # Named per-instance inputs are copied and re-hashed, reach argv as {inputs[key]}, and a changed one is refused.
    def test_named_inputs_are_copied_and_templated(self):
        src = self.tmp / 'in.ms'
        src.write_text('x,y\n7\nx+y\n')
        m = self.manifest(reps=1, instances=(('i1', ['ok']),))
        m['instances'][0]['inputs'] = dict(ms=dict(path=str(src), sha256=sha(src)))
        m['arms'][0]['argv'] = ['ok', '{inputs[ms]}']
        job = self.job(m)
        copied = self.jobs / job / 'inputs' / 'i1' / 'ms' / 'in.ms'
        self.assertEqual(sha(copied), sha(src))
        cell = next(c for c in bj.expand(m) if c['arm'] == 'a')
        self.assertEqual(bj.argv(m, cell, self.jobs / job)[-1], str(copied))
        m['instances'][0]['inputs']['ms']['sha256'] = '0' * 64
        with self.assertRaisesRegex(bj.JobError, 'input'):
            bj.validate(m)

    # An externally provisioned comparand may replace the git-archive recipe with a named provenance, never omit both.
    def test_comparand_build_replaces_git_archive(self):
        m = self.manifest(reps=1)
        m['arms'][1]['build'].update(recipe='tools/external/provision.sh', comparand='msolve 0.11.0 tarball')
        bj.validate(m)
        del m['arms'][1]['build']['comparand']
        with self.assertRaisesRegex(bj.JobError, 'git archive'):
            bj.validate(m)

    # The job root may not live under $HOME, where heavy writes reach the system drive.
    def test_jobs_root_under_home_is_refused(self):
        self.env['ZEEBRA_BENCH_JOBS'] = str(Path.home() / 'bench-jobs-should-not-exist')
        r = self.submit(self.manifest())
        self.assertEqual(r.returncode, 64)
        self.assertIn('HOME', r.stderr)
        self.assertFalse((Path.home() / 'bench-jobs-should-not-exist').exists())


    def synthetic(self, walls, mode='dev', flagged=()):
        """A loaded-journal shape: `walls` maps arm -> per-repetition seconds, one instance at 1 worker."""
        m = self.manifest(mode=mode)
        m['instances'] = [dict(name='goldilocks/katsura-4', params={}, competitive=K4)]
        m['arms'][0].update(library='zeebra', library_version='zeebra 0.1.0')
        attempts = []
        for rep in range(max(map(len, walls.values()))):
            for arm, values in walls.items():
                if rep < len(values):
                    aid = f'job:{len(attempts)}:0'
                    report = dict(status='complete', basis_sha256='d1', statistics=dict(symbolic_ns=int(values[rep] * 4e8)))
                    attempts.append(dict(index=len(attempts), try_=0, status='ok', stdout=json.dumps(report).encode(),
                                         cell=dict(instance='goldilocks/katsura-4', workers=1, seed=0, rep=rep, arm=arm),
                                         metadata=dict(attempt_id=aid, process_wall_ns=int(values[rep] * 1e9),
                                                       observed_peak_rss_bytes=40 << 20, solver_peak_rss_bytes=1 << 20,
                                                       before=dict(clock='boost'))))
        stop = dict(reason='complete', contamination=dict(contaminated=len(flagged), total=len(attempts), void=False,
                                                          median_khz={'goldilocks/katsura-4@1w': 4000000}, flagged={f: ['x'] for f in flagged}))
        header = dict(bench_job=dict(job_id='job', manifest_sha256='m' * 64, mode=mode, context=m['context']))
        return dict(header=header, stop=stop, stops=[stop], attempts=attempts, journal_sha256='j' * 64), m

    # The report renders every section from a real job, with stages and digests parsed from the child.
    def test_report_renders_every_section(self):
        job = self.job(self.manifest(instances=(('i1', ['report', 'd1']),), reps=2))
        self.cli('run', job, check=0)
        doc = json.loads(self.cli('report', job, '--json', check=0).stdout)
        self.assertEqual(doc['counts'], dict(attempts=4, statuses=dict(ok=4), contaminated=0, void=False,
                                             stopped=False, inconclusive=0,
                                             selection={'completed-unverified': 4}))
        a = next(r for r in doc['cells'] if r['arm'] == 'a')
        self.assertEqual((a['n'], a['stages_ms']), (2, dict(symbolic=2.0, elimination=3.0)))
        self.assertEqual(doc['digests'], {'i1': ['d1']})
        self.assertEqual(doc['ratios'][0]['verdict']['outcome'], 'stopped')
        self.assertEqual(doc['provenance']['arms'][0]['commit'], COMMIT)
        md = self.cli('report', job, check=0).stdout
        for heading in ('## Provenance', '## Attempts', '## Wall and RSS', '## Stages', '## Scaling',
                        '## Ratios', '## Verification', '## Interference'):
            self.assertIn(heading, md)

    # The report summarizes each attempt's interference telemetry (#1105), and says when there is none.
    def test_report_interference_summary(self):
        state, m = self.synthetic(dict(a=[1.0, 1.0]))
        self.assertIn('No interference telemetry', bj.render(bj.summarize(state, m)))
        metrics = dict(telemetry=1, compilers=3, compilers_on_bench=1, compilers_elsewhere=2,
                       psi=dict(cpu=dict(some=0.012, full=None), memory=dict(unavailable='no pressure/memory'),
                                io=dict(some=0.0, full=0.0)),
                       vmstat=dict(pgscan=40, pswpin=0), ccd_load={'0-7': 0.5, '8-15': 3.25},
                       bench_running=['stress-ng'], rusage=dict(nivcsw=17, majflt=2))
        state['attempts'][1]['metadata']['contamination'] = dict(metrics=metrics)
        doc = bj.summarize(state, m)
        row = doc['interference'][0]
        self.assertEqual((row['attempt'], row['compilers'], row['psi_cpu_some'], row['psi_memory_some']),
                         ('job:1:0', '1/2', 0.012, 'n/a'))
        self.assertEqual((row['pgscan'], row['max_ccd_load'], row['nivcsw'], row['bench_running']),
                         (40, 3.25, 17, ['stress-ng']))
        self.assertEqual(len(doc['interference']), 1)  # the attempt without telemetry is not a row
        md = bj.render(doc)
        self.assertIn('| `job:1:0` | a | goldilocks/katsura-4 | 1 | 1 | 1/2 | 1.2% | n/a | 0.0% | 40 | 3.25 | 17 | 2 | stress-ng |', md)

    # Ratios are paired per repetition through bench_stats; contaminated attempts are excluded and counted.
    def test_report_ratio_and_contamination(self):
        a = [1.00, 1.01, 0.99, 1.00, 1.02, 0.98, 1.00, 1.01, 0.99, 5.0]
        state, m = self.synthetic(dict(a=a, b=[x * 2 for x in a[:9]] + [2.0]), flagged=('job:18:0', 'job:19:0'))
        doc = bj.summarize(state, m)
        r = doc['ratios'][0]
        self.assertEqual((r['arm'], r['baseline'], r['n']), ('b', 'a', 9))
        self.assertAlmostEqual(r['median'], 2.0)
        self.assertEqual(r['verdict']['outcome'], 'regression')
        self.assertEqual(doc['counts']['contaminated'], 2)
        self.assertEqual(len(doc['verification']), 20)
        # Contamination spoils a time, not an answer: a flagged attempt's digest is still checked.
        state, m = self.synthetic(dict(a=[1.0]), flagged=('job:0:0',))
        self.assertEqual(bj.summarize(state, m)['digests'], {'goldilocks/katsura-4': ['d1']})
        # A machine without cpufreq (GitHub runners) has no median clock; the report still renders.
        state['stop']['contamination']['median_khz'] = {'goldilocks/katsura-4@1w': None}
        self.assertIn('median clock (kHz) goldilocks/katsura-4@1w —', bj.render(bj.summarize(state, m)))

    # The report names the clock rule's grouping: a v2 verdict's own, and per cell for a verdict without one.
    def test_report_names_the_clock_grouping(self):
        state, m = self.synthetic(dict(a=[1.0]))
        self.assertEqual(bj.summarize(state, m)['provenance']['clock_grouping'], 'cell')
        self.assertIn('clock rule grouped per cell', bj.render(bj.summarize(state, m)))
        state['stop']['contamination'].update(version=bj.VERDICT_VERSION, grouping='arm')
        self.assertEqual(bj.summarize(state, m)['provenance']['clock_grouping'], 'arm')
        self.assertIn('clock rule grouped per arm', bj.render(bj.summarize(state, m)))
        state['stop'] = dict(reason='cancelled')
        self.assertIsNone(bj.summarize(state, m)['provenance']['clock_grouping'])

    # GNU time's `-f %M` report: the figure is the last line, a signal death is named before it.
    def test_parse_time_report(self):
        p = bj.campaign.parse_time_report
        self.assertEqual(p('12345\n'), (12345, None))
        self.assertEqual(p('Command terminated by signal 2\n4567\n'), (4567, 2))
        self.assertEqual(p('Command exited with non-zero status 1\n890\n'), (890, None))
        self.assertEqual(p(''), (None, None))
        self.assertEqual(p('garbage'), (None, None))
        self.assertIsNone(bj.campaign.gnu_time(str(self.tmp / 'no-such-time')))

    # An attempt's peak is the solver's own when GNU time recorded it, the wrapper tree's bound otherwise.
    def test_peak_rss_prefers_the_solver(self):
        self.assertEqual(bj.peak_rss(dict(observed_peak_rss_bytes=40, solver_peak_rss_bytes=5)),
                         dict(rss=5, rss_basis=bj.RSS_SOLVER))
        self.assertEqual(bj.peak_rss(dict(observed_peak_rss_bytes=40, solver_peak_rss_bytes=None)),
                         dict(rss=40, rss_basis=bj.RSS_TREE))
        self.assertEqual(bj.peak_rss(dict(observed_peak_rss_bytes=40)), dict(rss=40, rss_basis=bj.RSS_TREE))

    # A journal from before #990 has only the tree figure: the scoreboard labels it a bound, the report marks it.
    def test_tree_only_peaks_are_labelled_upper_bounds(self):
        state, m = self.synthetic(dict(a=[1.0, 1.2, 1.1]), mode='publication')
        for a in state['attempts']:
            del a['metadata']['solver_peak_rss_bytes']
        row = bj.competitive_rows(state, m, machine='fixture', scored='a')[0]
        self.assertEqual((row['peak_rss_bytes'], row['peak_rss_basis']), (40 << 20, bj.RSS_TREE))
        self.assertIn('| ≤ 40', bj.render(bj.summarize(state, m)))

    # A real run records the binary's own peak beside the tree's, and the tree's carries the runner (#990).
    def test_run_records_the_solver_peak(self):
        if bj.campaign.gnu_time() is None:
            self.skipTest('GNU time is not installed')
        job = self.job(self.manifest(instances=(('i1', ['ok']), ('i2', ['selfkill'])), reps=1))
        self.cli('run', job)
        by_instance = {a['cell']['instance']: a['metadata'] for a in self.state(job)['attempts']}
        ok = by_instance['i1']
        self.assertGreater(ok['solver_peak_rss_bytes'], 0)
        self.assertLess(ok['solver_peak_rss_bytes'], ok['observed_peak_rss_bytes'])
        # GNU time's 128+N for a signalled binary reads back as -N, as it does without the reporter.
        self.assertEqual(by_instance['i2']['exit'], -signal.SIGTERM)

    # perf's `-x,` report: the user-only events this box's paranoid level gives, hybrid PMUs summed, gaps None.
    def test_parse_perf_stat(self):
        p = bj.campaign.parse_perf_stat
        here = ('# started on Sun Nov 22 15:12:20 2026\n\n'
                '1431043761,,cycles:u,335480602,100.00,,\n335.48,msec,task-clock:u,335480602,100.00,,\n')
        self.assertEqual(p(here), dict(cycles=1431043761, task_clock_ms=335.48, cycles_event='cycles:u'))
        hybrid = ('100,,cpu_core/cycles/u,1,100.00,,\n50,,cpu_atom/cycles/u,1,100.00,,\n'
                  '0.10,msec,task-clock,1,100.00,,\n')
        self.assertEqual(p(hybrid)['cycles'], 150)
        self.assertEqual(p('<not counted>,,cycles:u,0,0.00,,\n1.0,msec,task-clock:u,1,100.00,,\n'),
                         dict(cycles=None, task_clock_ms=1.0, cycles_event='cycles:u'))
        self.assertEqual(p('# started on Sun Nov 22 15:14:17 2026\n\n'),
                         dict(cycles=None, task_clock_ms=None, cycles_event=None))

    # Cycles per task-clock millisecond is kHz; either count missing, or no CPU time, gives no clock.
    def test_effective_khz(self):
        e = bj.campaign.effective_khz
        self.assertEqual(e(1431043761, 335.48), 4265660)
        for cycles, ms in ((None, 1.0), (1000, None), (1000, 0.0)):
            self.assertIsNone(e(cycles, ms))

    # perf is used only where perf_event_paranoid lets this user count its own processes (2 or lower).
    def test_perf_gating(self):
        allowed = bj.campaign.perf_permitted
        self.assertEqual([allowed(t) for t in ('-1\n', '0', '1', '2\n', '3', '4', '', 'x')],
                         [True, True, True, True, False, False, False, False])
        paranoid = self.tmp / 'paranoid'
        paranoid.write_text('3\n')
        self.assertIsNone(bj.campaign.perf_stat(shutil.which('perf') or '/usr/bin/perf', paranoid))
        self.assertIsNone(bj.campaign.perf_stat(str(self.tmp / 'no-such-perf')))
        self.assertIsNone(bj.campaign.perf_stat())  # ZEEBRA_BENCH_PERF='' turns it off

    # The attempt's clock is the cycle count's where perf produced one, else the sampled median, else the snapshots'.
    def test_attempt_clock_fallback(self):
        clock = bj.campaign.attempt_clock
        freq = dict(median_khz=1430000)
        self.assertEqual(clock(dict(perf=dict(effective_khz=4100000), freq=freq)), (4100000, 'perf-cycles'))
        self.assertEqual(clock(dict(perf=dict(effective_khz=None), freq=freq)), (1430000, 'sampled'))
        self.assertEqual(clock(dict(perf=None, freq=freq)), (1430000, 'sampled'))
        self.assertEqual(clock(dict(freq=freq)), (1430000, 'sampled'))
        self.assertEqual(clock(dict(perf=None, freq=None)), (None, 'snapshot'))

    # The solver pid is the first descendant of the runner's child that is no longer a wrapper (#328 class).
    def test_solver_pid(self):
        pid = bj.campaign.solver_pid
        wrappers = {'taskset', 'timeout', 'time'}
        tree = {101: (100, 'time'), 102: (101, 'child'), 103: (1, 'child'), 104: (102, 'worker')}
        self.assertEqual(pid(tree, 100, wrappers), 102)
        self.assertEqual(pid({101: (100, 'child'), 103: (1, 'child')}, 100, wrappers), 101)  # no GNU time
        # Forked but not yet exec'd: the child still carries its parent's wrapper name.
        self.assertIsNone(pid({101: (100, 'time'), 102: (101, 'time')}, 100, wrappers))
        self.assertIsNone(pid({103: (1, 'child')}, 100, wrappers))

    # Attempts are judged against attempts clocked the same way: a sampled straggler is not compared with cycle counts.
    def test_clock_sources_are_grouped_apart(self):
        rows = self.clock_rows(dict(grobx=[4100000] * 4 + [1430000]))
        for i, (_, _, c) in enumerate(rows):
            c['clock_source'] = 'perf-cycles' if i < 4 else 'sampled'
        s = bj.session_verdict_of(rows, 'dev', 'bench-job-job')
        self.assertEqual((s['contaminated'], s['void'], s['version']), (0, False, 3))
        self.assertEqual(s['median_khz'], {'wide64/eco-12@1w/grobx/perf-cycles': 4100000,
                                           'wide64/eco-12@1w/grobx': 1430000})
        self.assertEqual(s['clock_sources'], {'perf-cycles': 4, 'sampled': 1})
        # A journal from before cycle counting has no source and keeps version 2's keys.
        legacy = bj.session_verdict_of(self.clock_rows(dict(grobx=[4100000] * 3)), 'dev', 'bench-job-job')
        self.assertEqual(list(legacy['median_khz']), ['wide64/eco-12@1w/grobx'])

    # contamination() feeds the cycle-count clock to the clock rule and names its source.
    def test_contamination_records_the_clock_source(self):
        before = dict(at='2026-11-21T00:00:00Z', load1=0, compilers=0, cpus=[dict(cpu=0, khz=1)],
                      stat=[dict(cpu=0, role='bench', busy=0, total=0)], rest_stat=None)
        after = dict(before, at='2026-11-21T00:00:10Z', stat=[dict(cpu=0, role='bench', busy=1000, total=1000)])
        r = dict(before=before, after=after, cpu_seconds=10.0, freq=dict(median_khz=1430000),
                 perf=dict(effective_khz=4100000))
        c = bj.contamination(r, self.manifest(), 'job')
        self.assertEqual((c['clock_source'], c['metrics']['median_khz']), ('perf-cycles', 4100000))
        r['perf'] = None
        c = bj.contamination(r, self.manifest(), 'job')
        self.assertEqual((c['clock_source'], c['metrics']['median_khz']), ('sampled', 1430000))

    def perf_or_skip(self):
        os.environ['ZEEBRA_BENCH_PERF'] = shutil.which('perf') or '/usr/bin/perf'
        perf = bj.campaign.perf_stat()
        if perf is None:
            self.skipTest('perf cannot count this user\'s processes here')
        return perf

    # Counting attaches to the solver itself: the guard still watches it, and the timeout's INT still stops it.
    def test_run_child_counts_cycles_without_moving_the_guard_or_the_signal(self):
        perf = self.perf_or_skip()
        r = bj.campaign.run_child([str(self.child), 'spin', '100000000'], '0', 1, kill_after_s=5,
                                  guard=('child', str(self.child), 1 << 30), rss_reporter=bj.campaign.gnu_time(),
                                  perf=perf)
        self.assertEqual(r['returncode'], 124)  # the timeout reached the solver under counting
        self.assertLess(r['process_wall_ns'], 4e9)
        self.assertEqual(r['rss_guard_rc'], 0, r['rss_guard_stderr'])  # 1 would be "guarded nothing"
        self.assertIsNotNone(r['perf']['pid'])
        self.assertGreater(r['perf']['task_clock_ms'], 100)
        self.assertGreater(r['perf']['effective_khz'], 100000)
        self.assertEqual(bj.campaign.attempt_clock(r)[1], 'perf-cycles')

    # A job run with perf available records the counts and judges the clock from them.
    def test_run_records_cycle_counts(self):
        self.perf_or_skip()
        self.env['ZEEBRA_BENCH_PERF'] = os.environ['ZEEBRA_BENCH_PERF']
        self.fake_context()
        job = self.job(self.manifest(instances=(('i1', ['spin', '300000']),), reps=1))
        self.cli('run', job, check=0)
        md = self.state(job)['attempts'][0]['metadata']
        self.assertGreater(md['perf']['effective_khz'], 100000)
        self.assertEqual(md['contamination']['clock_source'], 'perf-cycles')
        self.assertEqual(md['contamination']['metrics']['median_khz'], md['perf']['effective_khz'])

    def publication(self, cells, workers=(1,), arms=None):
        """A publication job's loaded journal from `cells`: (arm, workers, wall seconds, digest) per
        clean attempt. `arms` maps arm name -> manifest overrides (library, workers, commit)."""
        state, m = self.synthetic(dict(a=[]), mode='publication')
        m['run']['workers'] = list(workers)
        base = {k: v for k, v in m['arms'][1].items() if k not in ('library', 'library_version')}
        m['arms'] = [dict(base, name=name, **over) for name, over in arms.items()]
        state['attempts'] = [
            dict(index=i, try_=0, status='ok',
                 stdout=json.dumps(dict(status='complete', basis_sha256=digest)).encode(),
                 cell=dict(instance='goldilocks/katsura-4', workers=w, seed=0, rep=i, arm=arm),
                 metadata=dict(attempt_id=f'job:{i}:0', process_wall_ns=int(wall * 1e9),
                               observed_peak_rss_bytes=40 << 20, solver_peak_rss_bytes=1 << 20,
                               before=dict(clock='boost')))
            for i, (arm, w, wall, digest) in enumerate(cells)]
        return state, m

    # The scoreboard bridge emits the committed CompetitiveRecord fixture that board.rs's test loads:
    # a Zeebra row and a competitor row that pair, both carrying the reference's invariants.
    def test_competitive_rows_match_the_fixture(self):
        state, m = self.publication(
            [('zeebra', 1, 1.0, 'd1'), ('msolve', 1, 2.1, 'd1'), ('zeebra', 1, 1.2, 'd1'),
             ('msolve', 1, 2.0, 'd1'), ('zeebra', 1, 1.1, 'd1')],
            arms=dict(zeebra=dict(library='zeebra', library_version='zeebra 0.1.0'),
                      msolve=dict(library='msolve', library_version='msolve 0.11.0', commit='a1b2c3d4e5')))
        rows = bj.competitive_rows(state, m, machine='fixture', references=REFS)
        self.assertEqual(rows, json.loads(FIXTURE.read_text())['rows'])
        dev_state, dev = self.synthetic(dict(a=[1.0]))
        with self.assertRaises(bj.JobError):
            bj.competitive_rows(dev_state, dev, machine='fixture')

    # Rows cover only the worker counts each arm ran: an arm with its own `workers` list gets no row,
    # and so no false "failed", at a count it never ran.
    def test_competitive_rows_cover_only_the_workers_each_arm_ran(self):
        state, m = self.publication([('z', 1, 1.0, 'd1'), ('m', 1, 2.0, 'd1'), ('m', 4, 0.9, 'd1')],
                                    workers=(1, 4), arms=dict(z=dict(workers=[1]), m=dict(library='msolve')))
        rows = bj.competitive_rows(state, m, machine='x')
        self.assertEqual(sorted((r['library'], r['limits']['workers']) for r in rows),
                         [('msolve', 1), ('msolve', 4), ('zeebra', 1)])
        self.assertTrue(all(r['outcome'] == 'complete' for r in rows))

    # A competitor row pairs with the scored Zeebra arm: the same environment.commit and policy
    # (board.rs `comparable_with`), whatever its own upstream commit and however many attempts each
    # arm kept. Any other Zeebra arm is labelled apart, so it never pairs by accident.
    def test_competitive_rows_pair_with_the_scored_arm(self):
        cells = [('z', 1, 1.0, 'd1'), ('z', 1, 1.1, 'd1'), ('z', 1, 1.2, 'd1'), ('m', 1, 2.0, 'd1'),
                 ('m', 1, 2.2, 'd1'), ('z2', 1, 0.9, 'd1')]
        arms = dict(z=dict(), m=dict(library='msolve', commit='a1b2c3d4e5'), z2=dict(commit='beef' * 10))
        state, m = self.publication(cells, arms=arms)
        with self.assertRaisesRegex(bj.JobError, 'several Zeebra arms'):
            bj.competitive_rows(state, m, machine='x')
        with self.assertRaisesRegex(bj.JobError, 'not a Zeebra arm'):
            bj.competitive_rows(state, m, machine='x', scored='m')
        rows = {r['library'] + r['environment']['commit']: r for r in
                bj.competitive_rows(state, m, machine='x', scored='z')}
        z, comp, z2 = rows['zeebra' + COMMIT[:8]], rows['msolve' + COMMIT[:8]], rows['zeebrabeefbeef']
        for k in ('commit', 'policy', 'machine', 'cpu', 'build'):
            self.assertEqual(z['environment'][k], comp['environment'][k], k)
        self.assertNotEqual(z['environment']['policy'], z2['environment']['policy'])
        self.assertIn('(z2 arm)', z2['environment']['policy'])

    # With a reference, a row is timed only over attempts whose basis digest equals it and carries the
    # reference's invariants; an arm none of whose attempts match is failed, never timed.
    def test_competitive_rows_carry_reference_checked_invariants(self):
        cells = [('z', 1, 1.0, 'd1'), ('z', 1, 9.0, 'WRONG'), ('z', 1, 1.2, 'd1'), ('m', 1, 2.0, 'WRONG'),
                 ('g', 1, 3.0, None)]
        state, m = self.publication(cells, arms=dict(z=dict(), m=dict(library='msolve'), g=dict(library='grobx')))
        rows = {r['library']: r for r in bj.competitive_rows(state, m, machine='x', references=REFS,
                                                              attempt_digests={'job:4:0': 'd1'})}
        z = rows['zeebra']
        self.assertEqual((z['outcome'], z['wall_nanos']), ('complete', 1_100_000_000))
        self.assertEqual(z['invariants'], REFS['goldilocks/katsura-4']['invariants'])
        self.assertEqual(z['verification'], dict(checked_against='Singular std, redSB', shared_invariants=2,
                                                 note='basis digest equal to the reference on 2/3 clean attempts'))
        self.assertEqual((rows['msolve']['outcome'], rows['msolve']['outcome_detail']),
                         ('failed', 'no attempt matched the independent reference'))
        self.assertNotIn('invariants', rows['msolve'])
        # A digest supplied by the caller stands in for a child that prints none.
        self.assertEqual((rows['grobx']['outcome'], rows['grobx']['wall_nanos']), ('complete', 3_000_000_000))
        # Without a reference nothing is claimed checked.
        bare = bj.competitive_rows(state, m, machine='x')
        self.assertTrue(all('invariants' not in r and 'verification' not in r for r in bare))

    # A child that exits 0 but reports a refusal is counted by its selection status and never timed.
    def test_refusal_reported_with_exit_zero_is_not_timed(self):
        state, m = self.synthetic(dict(a=[1.0, 1.0], b=[2.0, 2.0]))
        state['attempts'][1]['stdout'] = json.dumps(dict(status='refused', error='Unsupported { reason: "x" }')).encode()
        doc = bj.summarize(state, m)
        self.assertEqual(doc['counts']['selection'], {'completed-unverified': 3, 'unsupported': 1})
        b = next(c for c in doc['cells'] if c['arm'] == 'b')
        self.assertEqual(b['n'], 1)
        self.assertEqual(doc['selection'][1]['status'], 'unsupported')
        self.assertIn('## Selection outcomes', bj.render(doc))

    # A real job reaches each child-reported status plus the harness's timeout and process failure.
    def test_a_job_reports_every_selection_status_it_can_reach(self):
        cases = (('verified', ['emit', 'complete', 'true']), ('unverified', ['emit', 'complete', 'false']),
                 ('unsupported', ['emit', 'unsupported', 'false']), ('memory', ['emit', 'memory-refusal', 'false']),
                 ('time-stop', ['emit', 'time-stop', 'false']), ('wrong', ['emit', 'incorrect-output', 'false']),
                 ('crash', ['fail']), ('slow', ['sleep', '20']))
        job = self.job(self.manifest(instances=cases, reps=1, wall=1))
        self.cli('run', job, check=0)
        doc = json.loads(self.cli('report', job, '--json', check=0).stdout)
        by_instance = {s['instance']: s['status'] for s in doc['selection'] if s['arm'] == 'a'}
        self.assertEqual(by_instance, {'verified': 'completed-verified', 'unverified': 'completed-unverified',
                                       'unsupported': 'unsupported', 'memory': 'memory-refusal',
                                       'time-stop': 'timeout', 'wrong': 'incorrect-output',
                                       'crash': 'process-failure', 'slow': 'timeout'})
        self.assertEqual({c['instance'] for c in doc['cells']}, {'verified', 'unverified'})
        slow = next(s for s in doc['selection'] if s['instance'] == 'slow')
        self.assertEqual((slow['completion_ms'], slow['censored_at_ms']), (None, 1000.0))

    # An arm's task contract and configuration id, and an instance's lineage keys, reach every record.
    def test_selection_records_carry_contract_configuration_and_lineage(self):
        m = self.manifest(instances=(('i1', ['ok']),), reps=1)
        m['arms'][0].update(contract='T-GB', configuration='conv-w1')
        m['instances'][0]['lineage'] = dict(family_id='katsura', formulation_id='katsura-4')
        job = self.job(m)
        self.cli('run', job, check=0)
        doc = json.loads(self.cli('report', job, '--json', check=0).stdout)
        a = next(s for s in doc['selection'] if s['arm'] == 'a')
        self.assertEqual((a['contract'], a['configuration'], a['lineage']),
                         ('T-GB', 'conv-w1', dict(family_id='katsura', formulation_id='katsura-4')))
        b = next(s for s in doc['selection'] if s['arm'] == 'b')
        self.assertEqual((b['contract'], b['configuration']), (None, 'b'))
        for key, value in (('contract', 'T-FAST'), ('configuration', 'has space')):
            bad = self.manifest(instances=(('i1', ['ok']),), reps=1)
            bad['arms'][0][key] = value
            self.assertNotEqual(self.submit(bad).returncode, 0, key)
        bad = self.manifest(instances=(('i1', ['ok']),), reps=1)
        bad['instances'][0]['lineage'] = dict(family_id=3)
        self.assertNotEqual(self.submit(bad).returncode, 0)

    # With references, a matching digest is verified and a wrong one is incorrect-output and untimed.
    def test_references_verify_attempts(self):
        state, m = self.synthetic(dict(a=[1.0, 1.0]))
        state['attempts'][1]['stdout'] = json.dumps(dict(status='complete', basis_sha256='bad')).encode()
        doc = bj.summarize(state, m, references={'goldilocks/katsura-4': 'd1'})
        self.assertEqual(doc['counts']['selection'], {'completed-verified': 1, 'incorrect-output': 1})
        self.assertEqual(doc['cells'][0]['n'], 1)


class SelectionOutcomeTest(unittest.TestCase):
    """The selection-grade status of one attempt (#1008; plan §8.4)."""

    MD = dict(process_wall_ns=2_000_000_000, wall_seconds=2.0)

    def outcome(self, run_status='ok', child=None, cap=30, reference=None, md=None):
        return bj.selection_outcome(run_status, md or self.MD, child or {}, cap, reference)

    # Every harness status and every child report shape maps to exactly one of the nine statuses.
    def test_every_status_is_reachable(self):
        cases = [
            (('ok', dict(selection_outcome='complete', verified=True)), 'completed-verified'),
            (('ok', dict(selection_outcome='complete')), 'completed-unverified'),
            (('ok', {}), 'completed-unverified'),
            (('timeout', {}), 'timeout'),
            (('ok', dict(selection_outcome='time-stop')), 'timeout'),
            (('ok', dict(selection_outcome='memory-refusal')), 'memory-refusal'),
            (('rss-limit', {}), 'rss-limit'),
            (('ok', dict(selection_outcome='unsupported')), 'unsupported'),
            (('failed', {}), 'process-failure'),
            (('ok', dict(selection_outcome='incorrect-output')), 'incorrect-output'),
            (('cancelled', {}), 'not-run'),
        ]
        for (run_status, child), status in cases:
            self.assertEqual(self.outcome(run_status, child)['status'], status, (run_status, child))
        self.assertEqual({s for _, s in cases}, set(bj.SELECTION_STATUSES))

    # A censored attempt carries its cap and never a finite completion time, in-solver stops included.
    def test_a_timeout_has_no_completion_time(self):
        for run_status, child in (('timeout', {}), ('ok', dict(selection_outcome='time-stop'))):
            o = self.outcome(run_status, child, cap=30)
            self.assertIsNone(o['completion_ms'])
            self.assertEqual(o['censored_at_ms'], 30_000.0)
        self.assertEqual(self.outcome()['completion_ms'], 2000.0)
        for status in ('memory-refusal', 'unsupported', 'incorrect-output'):
            self.assertIsNone(self.outcome('ok', dict(selection_outcome=status))['completion_ms'], status)

    # m33_qualify's `status`/`error`, RunStatus tags and the grobx driver's `stopped`/`certified` classify unaided.
    def test_legacy_child_reports_classify(self):
        legacy = [
            (dict(status='complete'), 'completed-unverified'),
            (dict(status='refused', error='Unsupported { reason: "graded orders only" }'), 'unsupported'),
            (dict(status='stopped', error='Budget(TooManyRows { limit: 10 })'), 'memory-refusal'),
            (dict(status='stopped', error='TooManyBasisElements { elements: 9, limit: 8 }'), 'memory-refusal'),
            (dict(status='stopped', error='TimeBudgetExceeded { progress: .. }'), 'timeout'),
            (dict(status='stopped', error='CertificationFailed { reason: "x" }'), 'incorrect-output'),
            (dict(status='stopped', error='InvalidOptions { reason: "x" }'), 'process-failure'),
            (dict(status='stopped', error='something new'), 'process-failure'),
            (dict(status='verified'), 'completed-verified'),
            (dict(status='unsupported'), 'unsupported'),
            (dict(status='failed', error='x'), 'process-failure'),
            (dict(status='stopped-by-limit', error='the computation did not finish within 30000 ms, and had '
                  'reached degree 4 after 30001 ms'), 'timeout'),
            (dict(status='stopped-by-limit', detail='the computation did not finish within 8 batches'),
             'memory-refusal'),
            (dict(status='ok'), 'completed-unverified'),
            # r1cs_import's and whole_route's own `outcome` key is theirs, not this schema's.
            (dict(outcome='refused'), 'completed-unverified'),
            (dict(stopped='deadline'), 'timeout'),
            (dict(stopped='memory'), 'memory-refusal'),
            (dict(stopped='cancel'), 'not-run'),
            (dict(certified=True, basis='[x]:\n'), 'completed-verified'),
            (dict(certified=False, flaw='not reduced'), 'incorrect-output'),
            (dict(certified=None, basis='[x]:\n'), 'completed-unverified'),
        ]
        for child, status in legacy:
            self.assertEqual(self.outcome('ok', child)['status'], status, child)

    # An independent reference upgrades a completion to verified on a match and makes a mismatch incorrect.
    def test_reference_digest_verifies_or_convicts(self):
        match = self.outcome('ok', dict(basis_sha256='d1'), reference='d1')
        self.assertEqual((match['status'], match['verified_by']), ('completed-verified', 'reference'))
        both = self.outcome('ok', dict(basis_sha256='d1', verified=True), reference='d1')
        self.assertEqual(both['verified_by'], 'runtime+reference')
        wrong = self.outcome('ok', dict(basis_sha256='d2', verified=True), reference='d1')
        self.assertEqual((wrong['status'], wrong['completion_ms']), ('incorrect-output', None))
        # No digest to compare is not a conviction: the completion stays unverified by reference.
        self.assertEqual(self.outcome('ok', {}, reference='d1')['status'], 'completed-unverified')

    # Charged costs come from the child; the independent audit is recorded apart and never charged.
    def test_costs_are_split_into_charged_and_audit(self):
        child = dict(selection_outcome='complete', costs_ns=dict(feature=1_000_000, verification=3_000_000, audit=5_000_000))
        o = self.outcome('ok', child)
        self.assertEqual(o['charged_ms'], dict(feature=1.0, verification=3.0))
        self.assertEqual(o['audit_ms'], dict(audit=5.0))
        with self.assertRaises(bj.JobError):
            self.outcome('ok', dict(selection_outcome='complete', costs_ns=dict(made_up=1)))

    # The record is plain JSON, versioned, and survives a round trip unchanged.
    def test_record_round_trips(self):
        o = self.outcome('ok', dict(selection_outcome='complete', acceptance='probabilistic', costs_ns=dict(probe=7)))
        self.assertEqual(o['schema'], bj.SELECTION_SCHEMA)
        self.assertEqual(json.loads(json.dumps(o)), o)
        self.assertEqual(o['acceptance'], 'probabilistic')
        with self.assertRaises(bj.JobError):
            self.outcome('ok', dict(selection_outcome='complete', acceptance='usually'))

    # An unknown `selection_outcome` is a harness bug, refused rather than folded into a status.
    def test_unknown_outcome_is_refused(self):
        with self.assertRaises(bj.JobError):
            self.outcome('ok', dict(selection_outcome='mostly-done'))


if __name__ == '__main__':
    unittest.main()
