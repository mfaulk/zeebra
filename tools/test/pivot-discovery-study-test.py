#!/usr/bin/env python3
"""Check the serial discovery census against a hand-computable dependency fixture."""
import importlib.util
from pathlib import Path
import unittest

PATH = Path(__file__).resolve().parents[1] / 'external/pivot-discovery-study.py'
SPEC = importlib.util.spec_from_file_location('discovery', PATH)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class CensusTests(unittest.TestCase):
    # Physical-core selection excludes SMT siblings and CPUs outside the inherited affinity.
    def test_physical_cpu_mapping(self):
        topology = [(0, 0, 0), (1, 1, 0), (2, 0, 0), (3, 1, 0), (4, 2, 0)]
        self.assertEqual(MODULE.physical_cpus(topology, {0, 1, 2, 3, 4}), [2, 3, 4])
        self.assertEqual(MODULE.physical_cpus(topology, {0, 1}), [0, 1])

    # The census distinguishes new rank, duplicate claim sites, skew and inherited arithmetic.
    def test_census(self):
        rows = [
            dict(row=4, completed=True, elapsed_ns=10, first_claim_column=1,
                 pivot_column=1, inherited_products=5, discovered_products=0, dependencies=[]),
            dict(row=5, completed=True, elapsed_ns=30, first_claim_column=1,
                 pivot_column=2, inherited_products=7, discovered_products=9, dependencies=[4]),
            dict(row=6, completed=True, elapsed_ns=20, first_claim_column=2,
                 pivot_column=None, inherited_products=2, discovered_products=3, dependencies=[5]),
        ]
        result = MODULE.census(rows)
        self.assertEqual(result['new_rank'], 2)
        self.assertEqual(result['zero_rows'], 1)
        self.assertEqual(result['inherited_products'], 14)
        self.assertEqual(result['discovered_products'], 12)
        self.assertEqual(result['duplicate_first_claims'], 1)
        self.assertEqual(result['dependent_rows'], 2)
        self.assertEqual(result['serial_trajectory_dag_ns'], 60)
        self.assertEqual(result['row_sum_ns'], 60)
        self.assertEqual(result['row_max_ns'], 30)

    # An incomplete trace cannot become completed-work evidence.
    def test_refused_row_rejected(self):
        with self.assertRaises(ValueError):
            MODULE.census([dict(completed=False)])


if __name__ == '__main__':
    unittest.main()
