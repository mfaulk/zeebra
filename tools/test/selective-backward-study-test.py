#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('study', Path(__file__).resolve().parents[1] / 'external/selective-backward-study.py')
study = importlib.util.module_from_spec(spec)
spec.loader.exec_module(study)


class Acceptance(unittest.TestCase):
    # Complete coefficients, input identity and the selected policy all belong to acceptance.
    def test_answer_and_policy(self):
        ref = dict(digest='d', modulus=13, basis=['x+2*y'])
        raw = dict(ref, problem='mq-random-10', backward=dict(mode='dense-selected', batches=[{}]))
        study.validate(raw, ref, 'dense-selected', 'mq-random-10')
        for key, value in [('basis', ['x+3*y']), ('digest', 'wrong'), ('modulus', 7),
                           ('backward', None), ('backward', dict(mode='full', batches=[{}])),
                           ('backward', dict(mode='dense-selected', batches=[]))]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                study.validate(dict(raw, **{key: value}), ref, 'dense-selected', 'mq-random-10')

    # Adoption compares shipping routes and rejects an experimental observer presented as production.
    def test_production_route(self):
        ref = dict(digest='d', modulus=13, basis=['x+2*y'])
        raw = dict(ref, problem='mq-random-10', backward=None, parallel=None,
                   statistics=dict(batches=2, candidate_reduction=dict(batches=2, targets=1)))
        study.validate(raw, ref, 'production', 'mq-random-10')
        for changed in [dict(backward=dict(mode='dense-selected')), dict(parallel={}),
                        dict(statistics=dict(batches=2,candidate_reduction=dict(batches=0)))]:
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                study.validate(dict(raw, **changed), ref, 'production', 'mq-random-10')

    # Adoption timing keeps no-feature and feature-off production arms separate from work diagnostics.
    def test_adoption_plan(self):
        native=list(study.plan('adoption'))
        self.assertEqual(len(native),90)
        self.assertEqual({c[-1] for c in native},{'stock','production','feature-off'})
        self.assertEqual(len(list(study.plan('adoption-work'))),20)
        self.assertEqual(len(list(study.plan('adoption-off'))),20)

    # Interrupting the process-tree supervisor kills and reaps its owned child before propagating.
    def test_guard_interrupt_cleanup(self):
        import tempfile
        from unittest.mock import Mock
        guard=study.load('grobx-work-study')
        memory=Mock();memory.tree_hwm.side_effect=KeyboardInterrupt
        process=Mock(pid=321);process.poll.return_value=None
        with tempfile.TemporaryDirectory() as directory, \
             patch.object(guard,'sibling',return_value=memory), \
             patch.object(guard.subprocess,'Popen',return_value=process), \
             patch.object(guard.os,'killpg') as kill:
            with self.assertRaises(KeyboardInterrupt):
                guard.guarded(['placeholder'],Path(directory)/'attempt',60,1024)
            kill.assert_called_once_with(321,guard.signal.SIGKILL)
            process.wait.assert_called_once()

    # Pair trajectory drift is rejected instead of being credited to the backward kernel.
    def test_trajectory(self):
        stats = {key: 1 for key in study.TRAJECTORY}
        study.check_trajectory(dict(statistics=stats), dict(statistics=stats))
        for key in study.TRAJECTORY:
            with self.subTest(key=key), self.assertRaises(ValueError):
                study.check_trajectory(dict(statistics=dict(stats, **{key: 2})), dict(statistics=stats))

    # A changed mathematical memory peak can select another denominator without changing the F4 trajectory.
    def test_adoption_trajectory_excludes_peak_batch_denominator(self):
        stats={key:1 for key in study.TRAJECTORY}
        changed=dict(stats,max_live_nonzeros_as_built=2)
        study.check_trajectory(dict(statistics=stats),dict(statistics=changed),adoption=True)
        with self.assertRaises(ValueError):study.check_trajectory(dict(statistics=stats),dict(statistics=changed))
        changed=dict(stats,pairs_reduced=2)
        with self.assertRaises(ValueError):study.check_trajectory(dict(statistics=stats),dict(statistics=changed),adoption=True)

    # An ambient compiler blocks timing even when the load average is low.
    def test_environment_gate(self):
        with patch.object(study.os, 'getloadavg', return_value=(0, 0, 0)):
            self.assertEqual(study.environment_refusal(4, [(7, 'rustc')])['reason'], 'compiler')
            self.assertIsNone(study.environment_refusal(4, []))
        with patch.object(study.os, 'getloadavg', return_value=(5, 0, 0)):
            self.assertEqual(study.environment_refusal(4, [])['reason'], 'load')

    # Fixed-budget probe refusals may resume, while failed native timing attempts may not.
    def test_resume_statuses(self):
        self.assertTrue(study.resumable_status('verified', 'native'))
        self.assertTrue(study.resumable_status('incomplete-unverified', 'probe'))
        self.assertTrue(study.resumable_status('completed-needs-independent-reference', 'probe'))
        self.assertFalse(study.resumable_status('incomplete-unverified', 'native'))
        self.assertFalse(study.resumable_status('failed', 'probe'))

    # Native and observation-on measurements remain distinct cells in a fixed five-repeat plan.
    def test_plan(self):
        plan = list(study.plan('native'))
        self.assertEqual(len(plan), 120)
        self.assertEqual(len(set(plan)), 120)
        self.assertEqual({c[-1] for c in plan}, {'stock', 'full', 'dense-all', 'dense-selected'})
        self.assertEqual(len(list(study.plan('work'))), 40)
        with self.assertRaises(ValueError):
            list(study.plan('typo'))


if __name__ == '__main__':
    unittest.main()
