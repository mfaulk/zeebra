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
  report) echo '{"status":"complete","basis_sha256":"'"$2"'","statistics":{"symbolic_ns":2000000,"elimination_ns":3000000}}' ;;
  fail) echo boom >&2; exit 1 ;;
  sleep) exec sleep "$2" ;;
  once) [ -e "$2" ] && exit 0; : > "$2"; [ "$3" = fail ] && exit 1; exec sleep 30 ;;
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
        self.env = dict(os.environ, ZEEBRA_BENCH_JOBS=str(self.jobs), ZEEBRA_BENCH_JOB_RESERVE=str(reserve),
                        ZEEBRA_CPU_CONTEXT=str(context))
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

    # The clock rule's groups are cells: two instances at one worker count are different groups.
    def test_cell_group(self):
        self.assertNotEqual(bj.cell_group(dict(instance='x', workers=1)), bj.cell_group(dict(instance='y', workers=1)))
        self.assertNotEqual(bj.cell_group(dict(instance='x', workers=1)), bj.cell_group(dict(instance='x', workers=16)))

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
                                                       observed_peak_rss_bytes=1 << 20, before=dict(clock='boost'))))
        stop = dict(reason='complete', contamination=dict(contaminated=len(flagged), total=len(attempts), void=False,
                                                          median_khz=4000000, flagged={f: ['x'] for f in flagged}))
        header = dict(bench_job=dict(job_id='job', manifest_sha256='m' * 64, mode=mode, context=m['context']))
        return dict(header=header, stop=stop, stops=[stop], attempts=attempts, journal_sha256='j' * 64), m

    # The report renders every section from a real job, with stages and digests parsed from the child.
    def test_report_renders_every_section(self):
        job = self.job(self.manifest(instances=(('i1', ['report', 'd1']),), reps=2))
        self.cli('run', job, check=0)
        doc = json.loads(self.cli('report', job, '--json', check=0).stdout)
        self.assertEqual(doc['counts'], dict(attempts=4, statuses=dict(ok=4), contaminated=0, void=False,
                                             stopped=False, inconclusive=0))
        a = next(r for r in doc['cells'] if r['arm'] == 'a')
        self.assertEqual((a['n'], a['stages_ms']), (2, dict(symbolic=2.0, elimination=3.0)))
        self.assertEqual(doc['digests'], {'i1': ['d1']})
        self.assertEqual(doc['ratios'][0]['verdict']['outcome'], 'stopped')
        self.assertEqual(doc['provenance']['arms'][0]['commit'], COMMIT)
        md = self.cli('report', job, check=0).stdout
        for heading in ('## Provenance', '## Attempts', '## Wall and RSS', '## Stages', '## Scaling',
                        '## Ratios', '## Verification'):
            self.assertIn(heading, md)

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

    # The scoreboard bridge emits the committed CompetitiveRecord fixture that board.rs's test loads.
    def test_competitive_rows_match_the_fixture(self):
        state, m = self.synthetic(dict(a=[1.0, 1.2, 1.1], b=[]), mode='publication')
        rows = bj.competitive_rows(state, m, machine='fixture')
        self.assertEqual(rows, json.loads(FIXTURE.read_text())['rows'])
        dev_state, dev = self.synthetic(dict(a=[1.0]))
        with self.assertRaises(bj.JobError):
            bj.competitive_rows(dev_state, dev, machine='fixture')


if __name__ == '__main__':
    unittest.main()
