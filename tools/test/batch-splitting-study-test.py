#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest

path = Path(__file__).resolve().parents[1] / 'external/batch-splitting-study.py'
spec = importlib.util.spec_from_file_location('study', path)
study = importlib.util.module_from_spec(spec)
spec.loader.exec_module(study)


class Acceptance(unittest.TestCase):
    # Successful rows require every full reference coefficient and independent submitted-basis checks.
    def test_exact_basis_acceptance(self):
        row = dict(status='complete', basis=['x1+2*x2'], reference_basis=['x1+2*x2'],
                   exact_reference_and_submitted_checks=True)
        self.assertEqual(study.accept_report(row), 'verified')
        for update in (dict(basis=['x1+3*x2']), dict(exact_reference_and_submitted_checks=False)):
            with self.assertRaises(ValueError):
                study.accept_report(dict(row, **update))

    # Refusals retain typed reasons and cannot advertise a partial successful answer.
    def test_refusal_acceptance(self):
        row = dict(status='refused', basis=[], failure=dict(kind='one-pair', detail='rows'))
        self.assertEqual(study.accept_report(row), 'refused')
        for update in (dict(basis=['x1']), dict(failure=None), dict(status='unknown')):
            with self.assertRaises(ValueError):
                study.accept_report(dict(row, **update))

    # The process command leaves address space unconstrained while the existing watcher bounds RSS.
    def test_rss_budget_does_not_change_child_address_space(self):
        cell = ('cyclic-4', 'adaptive', 'rows', 7, 32)
        command = study.solver_command(Path('/binary'), cell)
        self.assertEqual(command, ['/binary', 'cyclic-4', 'adaptive', 'rows', '7', '32'])

    # The frozen study enumerates all controls and boundary cases without implicit extra attempts.
    def test_frozen_plan(self):
        cells = list(study.cells())
        self.assertEqual(len(cells), 74)
        self.assertEqual(len({tuple(cell) for cell in cells}), 74)
        self.assertEqual(sum(cell[1] == 'adaptive' for cell in cells), 14)


if __name__ == '__main__':
    unittest.main()
