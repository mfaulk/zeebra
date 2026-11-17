#!/usr/bin/env python3
import importlib.util
from collections import Counter
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]


def load():
    path = ROOT / 'tools/external/grobx-signature-study.py'
    spec = importlib.util.spec_from_file_location('grobx_signature_study', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run(engine, outcome, handover='on', rounds=(), echelon=0, inter=0, **summary):
    config = {'engine': engine, 'reduce': 'tests', 'handover': handover}
    rounds = [dict({'zero-rows': 0, 'rows': 1, 'given': 1, 'pivots': 1, 'entries': 1, 'columns': 1,
                    'subtracted': s, 'stages_seconds': dict.fromkeys(load().TRAJECTORY.STAGES, 0.0)})
              for s in rounds]
    r = {'config': config, 'rounds': rounds, 'echelon': {'subtracted': echelon},
         'summary': dict({'outcome': outcome, 'reduced': len(rounds), 'zero': 0}, **summary)}
    if inter:
        r['inter'] = {'subtracted': inter}
    return r


class PlanTests(unittest.TestCase):
    # Every case/arm pair appears once per repetition, and the first attempt rotates between repetitions.
    def test_plan_is_balanced_and_rotated(self):
        study = load()
        cases = list(study.CASES)
        plan = study.plan(5, cases)
        counts = Counter((p['case'], p['arm']) for p in plan)
        self.assertEqual(set(counts.values()), {5})
        self.assertEqual(len(counts), sum(len(study.arms(c)) for c in cases))
        firsts = {(p['case'], p['arm']) for p in plan if plan.index(p) == 0 or plan[plan.index(p) - 1]['repeat'] != p['repeat']}
        self.assertGreater(len(firsts), 1)

    # Combinations are crossed only on the two instances the plan names, and never on the stock control.
    def test_crossed_arms_only_where_declared(self):
        study = load()
        self.assertIn('sig-off-nocomb', study.arms('eco12-wide64'))
        self.assertIn('no-handover-nocomb', study.arms('mq10-m31'))
        self.assertNotIn('default-nocomb', study.arms('mq11-goldilocks'))
        self.assertNotIn('stock-nocomb', study.arms('eco12-wide64'))
        self.assertEqual(study.options('no-handover-nocomb'),
                         {'research_handover': False, 'research_policy': 'none'})


class RouteTests(unittest.TestCase):
    # A handover-off request must stay one signature run; a signatures-off request must be plain only.
    def test_route_matches_request(self):
        study = load()
        raw = {'research_policy': {'plain': True, 'signature_tests': True, 'validate': False,
                                   'signatures': True, 'seed': 0},
               'research_signature': {'handover': False}}
        ok = {'runs': [run('signature', 'basis', handover='off')]}
        study.expected_route(raw, {'research_handover': False}, ok)
        handed = {'runs': [run('signature', 'handover'), run('plain', 'basis')]}
        with self.assertRaises(ValueError):
            study.expected_route(raw, {'research_handover': False}, handed)
        raw_off = dict(raw, research_policy=dict(raw['research_policy'], signatures=False),
                       research_signature={'handover': True})
        with self.assertRaises(ValueError):
            study.expected_route(raw_off, {'research_signatures': False}, ok)
        study.expected_route(raw_off, {'research_signatures': False}, {'runs': [run('plain', 'basis')]})

    # Work from an abandoned signature run counts toward the total and is also reported as discarded.
    def test_ledger_keeps_discarded_work(self):
        study = load()
        trajectory = {'runs': [run('signature', 'handover', rounds=(5, 7), echelon=1),
                               run('plain', 'basis', handover='off', rounds=(100,), echelon=1, inter=10)]}
        ledger = study.ledger(trajectory)
        self.assertEqual(ledger['subtracted_total'], 5 + 7 + 1 + 100 + 1 + 10)
        self.assertEqual(ledger['subtracted_discarded'], 13)
        self.assertEqual([r['outcome'] for r in ledger['runs']], ['handover', 'basis'])


if __name__ == '__main__':
    unittest.main()
