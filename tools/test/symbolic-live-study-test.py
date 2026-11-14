#!/usr/bin/env python3
import importlib.util
import copy
import hashlib
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('symbolic_live', ROOT / 'tools/external/symbolic-live-study.py')
study = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(study)


class SymbolicStudy(unittest.TestCase):
    # The fixed plan interleaves every factor and separates clocks-off/work controls.
    def test_plan_is_complete_and_unique(self):
        cells = list(study.plan())
        self.assertEqual(len(cells), 346)
        self.assertEqual(len(set(cells)), len(cells))
        self.assertEqual(sum(c[0] == 'native' for c in cells), 270)
        self.assertEqual(sum(c[0] == 'work' for c in cells), 36)
        self.assertEqual(sum(c[0] == 'stage-off' for c in cells), 40)
        self.assertEqual([c[-1] for c in cells[:6]], list(study.ARMS))

    # Policy metadata must match the requested arm and cannot hide research elimination overrides.
    def test_policy_validation(self):
        reference = dict(digest='abc', modulus=32003, basis=['x1'])
        raw = dict(reference, problem='mq-random-10', backward=None, parallel=None,
                   symbolic=dict(mode='dedup', batches=1, offered_seeds=4, retained_seeds=3,
                                 peak_seed_capacity=3, peak_order_capacity=0),
                   measured=True, work=None, statistics=dict(batches=1, forward_ns=7, backward_ns=2, elimination_ns=10, candidate_reduction=dict(batches=1)))
        study.validate(raw, reference, 'native', 'mq-random-10', 'dedup')
        for key, value in [('symbolic', None), ('parallel', {}), ('basis', ['wrong']), ('measured', False)]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                study.validate(dict(raw, **{key: value}), reference, 'native', 'mq-random-10', 'dedup')

    # An incomplete or reordered plan cannot produce a complete summary.
    def test_incomplete_cohort_rejected(self):
        with self.assertRaises(ValueError):
            study.check_plan([])
        with self.assertRaises(ValueError):
            study.check_plan([dict(phase='native', repeat=0, problem='mq-random-10', modulus=32003, arm='both')])

    # Resumption accepts only the exact verified prefix and retains immutable source identity.
    def test_resume_checks_prefix_and_terminal_holds(self):
        identity = dict(commit='frozen')
        cohort = dict(identity=identity, attempts=[], refusal=dict(reason='environment'), resumptions=[], active_wall_seconds=1)
        study.verify_prefix(cohort, identity, {})
        for bad in [dict(cohort, identity=dict(commit='different')), dict(cohort, refusal=dict(reason='aggregate-budget')), dict(cohort, resumptions=[{}] * 8)]:
            with self.assertRaises(ValueError):
                study.verify_prefix(bad, identity, {})
        wrong = dict(phase='native', repeat=0, problem='mq-random-10', modulus=32003, arm='both')
        with self.assertRaises(ValueError):
            study.verify_prefix(dict(cohort, attempts=[wrong]), identity, {})

    # A verified accepted response is checked again, and changed coefficients cannot be resumed.
    def test_resume_revalidates_accepted_answers(self):
        reference = dict(digest='abc', modulus=32003, basis=['x1'])
        raw = dict(reference, problem='mq-random-10', backward=None, parallel=None, symbolic=None,
                   measured=True, work=None, statistics=dict(batches=1, forward_ns=7, backward_ns=2,
                   elimination_ns=10, candidate_reduction=dict(batches=1)))
        accepted = dict(phase='native', repeat=0, problem='mq-random-10', modulus=32003, arm='stock',
                        status='verified', exit=0, stop=None, compiler_before=[], compiler_after=[],
                        peak_rss_bytes=1024, process_wall_ns=100, cpu_seconds=0, raw=raw)
        identity = dict(commit='frozen')
        cohort = dict(identity=identity, attempts=[accepted], refusal=dict(reason='environment'), resumptions=[], active_wall_seconds=1)
        refs = {('mq-random-10', 32003): reference}
        study.verify_prefix(cohort, identity, refs)
        changed = dict(accepted, raw=dict(raw, basis=['wrong']))
        with self.assertRaises(ValueError):
            study.verify_prefix(dict(cohort, attempts=[changed]), identity, refs)
        with self.assertRaises(ValueError):
            study.verify_prefix(dict(cohort, attempts=[dict(accepted, compiler_after=[1])]), identity, refs)

    # Signed and nonnegative residues denote identical complete coefficients, while changed coefficients fail.
    def test_public_residues_compare_exactly(self):
        reference = dict(digest='abc', modulus=32003, variables=['x1'], basis=['x1-3'])
        raw = dict(digest='abc', modulus=32003, basis=['x1+32000'], problem='public-eco-4', backward=None,
                   parallel=None, symbolic=None, measured=True, work=None,
                   statistics=dict(batches=1, forward_ns=7, backward_ns=2, elimination_ns=10, candidate_reduction=dict(batches=1)))
        study.validate(raw, reference, 'native', 'public-eco-4', 'stock')
        for basis in [['x1+31999'], ['0'], ['x1+32000', 'x1+32000']]:
            with self.subTest(basis=basis), self.assertRaises(ValueError):
                study.validate(dict(raw, basis=basis), reference, 'native', 'public-eco-4', 'stock')

    # The narrow repair keeps the original failed response, accepts equivalent residues, and refuses real failures.
    def test_signed_reference_repair_preserves_failed_response(self):
        refs, attempts = {}, []
        for phase, repeat, problem, modulus, arm in list(study.plan())[:37]:
            reference = dict(digest=problem, modulus=modulus, basis=['x1'])
            if problem.startswith('public-'):
                reference.update(variables=['x1'], basis=['x1-3'])
            refs[(problem, modulus)] = reference
            symbolic = None if arm in ('stock','feature-off') else dict(mode=arm, batches=1, offered_seeds=4, retained_seeds=3 if arm in ('dedup','both') else 4)
            raw = dict(digest=problem, modulus=modulus, basis=['x1+32000'] if problem.startswith('public-') else ['x1'], problem=problem,
                       symbolic=symbolic, backward=None, parallel=None, work=None, measured=True,
                       statistics=dict(batches=1, forward_ns=7, backward_ns=2, elimination_ns=10, candidate_reduction=dict(batches=1)))
            attempts.append(dict(phase=phase, repeat=repeat, problem=problem, modulus=modulus, arm=arm, status='verified', exit=0, stop=None,
                                 compiler_before=[], compiler_after=[], peak_rss_bytes=1024, process_wall_ns=100, cpu_seconds=0, raw=raw,
                                 stdout=json.dumps(raw)))
        attempts[-1].update(status='failed',failure='full reduced basis differs from the verified reference')
        original = copy.deepcopy(attempts[-1])
        audit = dict(original_failed_attempt=original, original_controller_commit='old', repair_controller_commit='repair',
                     stdout_sha256=hashlib.sha256(original['stdout'].encode()).hexdigest(),
                     raw_sha256=hashlib.sha256(json.dumps(original['raw'],sort_keys=True).encode()).hexdigest())
        initial = dict(identity=dict(commit='old',binaries='same'),attempts=attempts)
        bad = copy.deepcopy(initial)
        bad['attempts'][-1]['exit'] = 1
        with self.assertRaises(ValueError):
            study.repair_signed_reference(bad,audit,dict(commit='new',binaries='same'),refs)
        study.repair_signed_reference(initial,audit,dict(commit='new',binaries='same'),refs)
        self.assertEqual(initial['attempts'][-1]['status'],'verified')
        self.assertEqual(initial['attempts'][-1]['stdout'],original['stdout'])
        self.assertEqual(initial['validator_repairs'][0]['original_failed_attempt'],original)
        self.assertEqual(initial['attempts'][-1]['failure'],original['failure'])


if __name__ == '__main__':
    unittest.main()
