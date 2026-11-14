#!/usr/bin/env python3
import gzip
import importlib.util
import json
import os
from pathlib import Path
import signal
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('whole_route', ROOT / 'tools/external/whole-route-study.py')
study = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(study)
aj = study.load('attempt_journal')


class WholeRouteStudy(unittest.TestCase):
    # The explicit native amendment keeps the verified two-cell prefix within its original budgets.
    def test_native_amendment_is_one_time_and_cumulative(self):
        cells=list(study.plan('native'))
        identity={key:key for key in ('binary_sha256','build_commit','cargo_lock_sha256','cargo_config_sha256','rustc','machine','affinity','build','topology')}
        identity['commit']=study.NATIVE_PREFIX_CONTROLLER
        previous=dict(phase='native',plan=cells,identity=identity,references={},
            refusal=dict(reason='compiler'),attempts=[dict(zip(('repeat','problem','modulus','route','arm'),cell),status='verified') for cell in cells[:2]])
        current=dict(phase='native',plan=cells,identity=dict(identity),references={})
        with self.assertRaises(ValueError): study.resume_prefix(previous,current)
        self.assertEqual(study.resume_prefix(previous,current,native_amendment=True),2)
        self.assertEqual(study.native_remaining_seconds(),880)
        self.assertLessEqual(study.native_remaining_seconds()+study.NATIVE_PRIOR_CHARGE_SECONDS,900)
        current['identity']['binary_sha256']='changed'
        with self.assertRaises(ValueError): study.resume_prefix(previous,current,native_amendment=True)
        current['identity']=dict(identity)
        previous['attempts'][0]['problem']='wrong'
        with self.assertRaises(ValueError): study.resume_prefix(previous,current,native_amendment=True)
        previous['attempts'][0]['problem']=cells[0][1]
        previous['resumptions']=[{}]
        with self.assertRaises(ValueError): study.resume_prefix(previous,current,native_amendment=True)
        previous.pop('resumptions')
        previous['attempts'][0]['status']='contaminated'
        with self.assertRaises(ValueError): study.resume_prefix(previous,current,native_amendment=True)
    # Idle IDE language servers do not gate a window; any cargo, rustc, clippy or linker process still does.
    def test_build_gate_ignores_language_servers_only(self):
        active=[('1','rust-analyzer'),('2','cargo'),('3','rustc'),('4','clippy-driver'),('5','rust-lld'),('6','ld.lld')]
        self.assertEqual(study.build_processes(lambda: active),active[1:])
        self.assertEqual(study.build_processes(lambda: [('9','rust-analyzer')]),[])


    # Relative and absolute repository archive paths produce the same durable provenance path.
    def test_archive_path_is_normalized_before_relativizing(self):
        path=Path('research/m28-current-baseline/pilot.json.gz')
        self.assertEqual(study.repository_path(path),str(path))
        self.assertEqual(study.repository_path(ROOT/path),str(path))
        with self.assertRaises(ValueError): study.repository_path(Path('/tmp/outside-repository.json.gz'))

    # A continuation accepts the exact verified prefix and rejects binary or cell drift.
    def test_continuation_preserves_frozen_prefix(self):
        cells=list(study.plan('pilot'))
        identity={key:key for key in ('binary_sha256','build_commit','cargo_lock_sha256','cargo_config_sha256','rustc','machine','affinity','build','topology')}
        previous=dict(phase='pilot',plan=cells,identity=identity,references={},
            refusal=dict(reason='compiler'),attempts=[dict(zip(('repeat','problem','modulus','route','arm'),cells[0]),status='verified')])
        current=dict(phase='pilot',plan=cells,identity=dict(identity),references={})
        self.assertEqual(study.resume_prefix(previous,current),1)
        current['identity']['binary_sha256']='changed'
        with self.assertRaises(ValueError): study.resume_prefix(previous,current)
        current['identity']=dict(identity)
        previous['attempts'][0]['problem']='wrong'
        with self.assertRaises(ValueError): study.resume_prefix(previous,current)

    # Unexpected process failures stay failures rather than becoming favorable resource refusals.
    def test_terminal_causes_distinguish_resource_limits_and_bugs(self):
        self.assertEqual(study.terminal_kind(-9,'wall',''), 'incomplete-resource-refusal')
        self.assertEqual(study.terminal_kind(-9,'output-128MiB',''), 'incomplete-resource-refusal')
        self.assertEqual(study.terminal_kind(101,None,'TooManyNonzeros { limit: 3 }'), 'incomplete-resource-refusal')
        self.assertEqual(study.terminal_kind(101,None,'panicked at an invariant'), 'failed')

    # A reported basis refusal is retained without checking a nonexistent complete basis.
    def test_reported_refusal_is_not_a_complete_basis(self):
        raw = dict(problem='mq-random-10', modulus=32003, route='fglm', outcome='basis-refusal',
                   basis=None, point=None, measured=True, work=None, digest='expected')
        study.validate_response(raw, dict(digest='expected',modulus=32003), 'mq-random-10', 32003, 'fglm', 'stage-on')

    # A killed later stage preserves its complete source checkpoint without inventing a solve.
    def test_checkpoint_is_not_a_final_answer(self):
        records = study.responses('{"checkpoint":"source-basis","basis":["x"]}\n')
        self.assertIsNone(records['final'])
        self.assertEqual(records['source']['basis'], ['x'])
        with self.assertRaises(ValueError):
            study.responses('{"checkpoint":"source-basis"}\nnot json')

    # Independent modular substitution rejects a point violating any original equation.
    def test_independent_modular_substitution(self):
        raw = dict(modulus=13, input=dict(variables=['x','y'], generators=['x^2-1','y-x']), point=['1','1'])
        study.check_point(raw)
        raw['point'] = ['1','2']
        with self.assertRaises(ValueError): study.check_point(raw)
        raw['input']['generators'] = ['__import__("os")']
        with self.assertRaises(ValueError): study.check_point(raw)

    # Staged and unstaged runs are repeated in alternating order without pooling work diagnostics.
    def test_plan_is_interleaved_and_bounded(self):
        cells = list(study.plan())
        self.assertEqual(len(cells), len(set(cells)))
        self.assertEqual({c[0] for c in cells if c[-1] != 'work'}, set(range(5)))
        self.assertEqual(study.limits()['rss_bytes'], 2 * 1024**3)
        self.assertEqual(study.limits()['aggregate_wall_seconds'], 900)
        self.assertEqual(study.child_wall(120),60)
        self.assertEqual(study.child_wall(7.8),7)
        with self.assertRaises(ValueError): study.child_wall(.5)


CELLS = [[r, 'katsura-6', 32003, 'basis', 'stage-on'] for r in range(6)]
IDENTITY = {key: key for key in ('commit','binary_sha256','build_commit','cargo_lock_sha256','cargo_config_sha256','rustc','machine','affinity','build','topology')}


def basis_stdout(cell, width=64):
    repeat, problem, modulus, _, arm = cell
    return json.dumps(dict(problem=problem, modulus=modulus, basis=['x%d+%d' % (repeat, i) for i in range(width)],
                           measured=arm != 'stage-off', work=None)) + '\n'


def child(cell, index, stdout=None, **overrides):
    result = dict(command=['mq10_profile', str(cell[2])], cpus=[3], process_wall_ns=1_000_000_000 + index,
                  process_cpu_ns=900_000_000 + index, observed_tree_peak_bytes=50_000_000 + index, stop=None, exit=0,
                  interrupt_exit=None, output_bytes=0, stdout=basis_stdout(cell) if stdout is None else stdout,
                  stderr='', cpu_seconds=0.9 + index / 1e9)
    result.update(overrides)
    return result


class JournaledWindow(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.dir = Path(self.scratch.name) / 'journal'
        self.cohort = dict(schema=1, phase='native', identity=IDENTITY, limits=study.limits(), plan=CELLS,
                           attempts=[], references={})

    def tearDown(self):
        self.scratch.cleanup()

    def window(self, launch=None, compilers=lambda: [], load=lambda: 0.5, remaining_wall=lambda: 500,
               output_remaining=lambda: 1 << 30, cohort=None, native_amendment=False):
        cohort = cohort or self.cohort
        self.journal = study.open_journal(self.dir, cohort, study.limits())
        launch = launch or (lambda index, cell, wall, limit: child(cell, index))
        study.measure(self.journal, len(cohort['attempts']), {}, launch, compilers, load,
                      remaining_wall, output_remaining, native_amendment=native_amendment, log=lambda *_, **__: None)
        return self.journal

    def render(self, name='cohort.json.gz'):
        out = Path(self.scratch.name) / name
        study.render(self.dir, out)
        return out.read_bytes(), json.loads(gzip.decompress(out.read_bytes()))

    # A watchdog SIGKILL while checking a child keeps every earlier attempt and that child's exact exit metadata.
    def test_kill_during_checking_keeps_durable_attempts(self):
        calls = []
        def compilers():
            calls.append(1)
            if len(calls) == 8: os.kill(os.getpid(), signal.SIGKILL)  # post-child gate of attempt 3
            return []
        pid = os.fork()
        if pid == 0:
            try: self.window(compilers=compilers)
            finally: os._exit(0)
        _, status = os.waitpid(pid, 0)
        self.assertTrue(os.WIFSIGNALED(status))
        self.assertEqual(os.WTERMSIG(status), signal.SIGKILL)
        state = aj.load(self.dir)
        self.assertIsNone(state['stop'])
        self.assertEqual([a['status'] for a in state['attempts']], ['complete-needs-independent-basis-check'] * 3 + ['unverified'])
        first, cohort = self.render()
        self.assertEqual(first, self.render('again.json.gz')[0])
        killed = child(CELLS[3], 3)
        row = cohort['attempts'][3]
        self.assertEqual(row['status'], 'unverified')
        self.assertEqual(row['stdout'], killed['stdout'])
        for key in ('process_wall_ns', 'process_cpu_ns', 'observed_tree_peak_bytes', 'exit', 'stop', 'cpu_seconds'):
            self.assertEqual(row[key], killed[key])
        self.assertEqual(row['observed_peak_rss_bytes'], killed['observed_tree_peak_bytes'])
        self.assertEqual(cohort['plan'], CELLS)
        self.assertNotIn('refusal', cohort)

    # The exit is recorded before any parsing, so an interruption inside response checking leaves it durable.
    def test_exit_is_recorded_before_responses_are_parsed(self):
        with mock.patch.object(study, 'responses', side_effect=SystemExit(143)):
            with self.assertRaises(SystemExit): self.window()
        state = aj.load(self.dir)
        self.assertEqual(len(state['attempts']), 1)
        self.assertEqual(state['attempts'][0]['status'], 'unverified')
        self.assertEqual(state['attempts'][0]['stdout'], basis_stdout(CELLS[0]).encode())

    # An interrupted publication leaves no partial cohort, and the rerun from the journal is byte-identical.
    def test_interrupted_render_is_reproducible_offline(self):
        self.window()
        with mock.patch.object(study.gzip, 'compress', side_effect=SystemExit(137)):
            with self.assertRaises(SystemExit): self.render()
        self.assertFalse((Path(self.scratch.name) / 'cohort.json.gz').exists())
        first, cohort = self.render()
        self.assertEqual(first, self.render()[0])
        self.assertEqual(len(cohort['attempts']), len(CELLS))
        self.assertEqual(cohort['attempts'][2]['responses']['final']['basis'][0], 'x2+0')
        self.assertEqual(cohort['journal']['journal_sha256'], aj.load(self.dir)['journal_sha256'])

    # Pre-child compiler/load gates, the aggregate wall and the output budget become journaled stops rendered as the refusal.
    def test_refusals_are_journaled_stops(self):
        for found, busy, reason in (([], 9.0, 'load-or-aggregate'), ([('1', 'rustc')], 0.5, 'compiler')):
            with self.subTest(reason=reason):
                self.tearDown(); self.setUp()
                calls = []
                def compilers():
                    calls.append(1)
                    return found if len(calls) == 5 else []
                self.window(compilers=compilers, load=lambda: busy if len(calls) >= 5 else 0.5)
                _, cohort = self.render()
                self.assertEqual(len(cohort['attempts']), 2)
                self.assertEqual(cohort['refusal']['reason'], reason)
        self.tearDown(); self.setUp()
        budget = iter([1 << 20, 1 << 20, 0])
        self.window(output_remaining=lambda: next(budget, 0))
        self.assertEqual(aj.load(self.dir)['stop']['reason'], 'output-bytes')
        self.tearDown(); self.setUp()
        self.window(remaining_wall=lambda: 0.5)
        self.assertEqual(aj.load(self.dir)['stop']['reason'], 'load-or-aggregate')
        self.assertEqual(aj.load(self.dir)['attempts'], [])

    # A launcher signal keeps the interrupted attempt and its verdict, then stops the window and exits.
    def test_launcher_signal_records_attempt_then_stop(self):
        launch = lambda index, cell, wall, limit: child(cell, index, stdout='', exit=-9, stop='launcher-signal-15', interrupt_exit=143)
        with self.assertRaises(SystemExit) as raised: self.window(launch=launch)
        self.assertEqual(raised.exception.code, 143)
        state = aj.load(self.dir)
        self.assertEqual([a['status'] for a in state['attempts']], ['incomplete-resource-refusal'])
        self.assertEqual(state['stop'], dict(reason='launcher-signal', exit=143))

    # A failed validation is retained with its reason before the controller stops.
    def test_failed_validation_is_retained(self):
        bad = '{"problem":"wrong","modulus":1,"basis":[]}\n'
        with self.assertRaises(RuntimeError): self.window(launch=lambda index, cell, wall, limit: child(cell, index, stdout=bad))
        state = aj.load(self.dir)
        self.assertEqual(state['attempts'][0]['status'], 'failed')
        self.assertEqual(state['attempts'][0]['verdict']['failure'], 'problem identity drift')
        self.assertEqual(state['stop']['reason'], 'failed-validation')

    # A resumed window keeps the frozen prefix byte-identical in the header and journals only the tail.
    def test_resumed_prefix_is_preserved(self):
        prefix = [dict(child(CELLS[0], 0), repeat=0, problem='katsura-6', modulus=32003, route='basis', arm='stage-on', status='verified')]
        cohort = dict(self.cohort, attempts=prefix, limits=dict(study.limits(), aggregate_wall_seconds=900),
                      resumptions=[dict(accepted_prefix=1)])
        journal = self.window(cohort=cohort)
        self.assertEqual(journal.header['plan'], CELLS[1:])
        _, rendered = self.render()
        self.assertEqual(rendered['attempts'][0], prefix[0])
        self.assertEqual(len(rendered['attempts']), len(CELLS))
        self.assertEqual(rendered['limits']['aggregate_wall_seconds'], 900)
        self.assertEqual(rendered['resumptions'], [dict(accepted_prefix=1)])
        with self.assertRaises(ValueError): journal.record_exit(0, CELLS[1], b'', b'', {})

    # Journal bytes per attempt stay flat as the cohort grows, unlike rewriting the whole archive per child.
    def test_controller_write_volume_is_linear(self):
        self.cohort['plan'] = [[r, 'katsura-6', 32003, 'basis', 'stage-on'] for r in range(40)]
        written = []
        def launch(index, cell, wall, limit):
            written.append(self.journal.bytes_written)
            return child(cell, index, stdout=basis_stdout(cell, width=2000))
        self.window(launch=launch)
        deltas = [b - a for a, b in zip(written, written[1:])]
        self.assertEqual(len(deltas), 39)
        self.assertLess(max(deltas), 1.2 * min(deltas))

    # A SIGTERM arriving during a journal append is deferred until the record is complete.
    def test_signal_during_append_is_deferred(self):
        journal = study.open_journal(self.dir, self.cohort, study.limits())
        def interrupted(signum, _): raise SystemExit(128 + signum)
        previous = signal.signal(signal.SIGTERM, interrupted)
        try:
            with self.assertRaises(SystemExit):
                with study.deferred_signals():
                    os.kill(os.getpid(), signal.SIGTERM)
                    journal.record_stop('probe')
        finally:
            signal.signal(signal.SIGTERM, previous)
        self.assertEqual(aj.load(self.dir)['stop'], dict(reason='probe'))


if __name__ == '__main__': unittest.main()
