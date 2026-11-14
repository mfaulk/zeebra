#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location('whole_summary',ROOT/'research/m28-current-baseline/summarize.py')
summary=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(summary)


class WholeSummary(unittest.TestCase):
    # Missing entire cells cannot masquerade as a complete repeated campaign.
    def test_missing_cells_are_rejected(self):
        with self.assertRaises(ValueError): summary.validate_plan(dict(phase='pilot',plan=[],attempts=[]))

    # A stated environmental stop accepts only the exact completed prefix of the frozen plan.
    def test_partial_prefix_requires_refusal(self):
        cells=list(summary.study.plan('pilot'))
        cohort=dict(phase='pilot',plan=cells,attempts=[],refusal=dict(reason='compiler'))
        self.assertFalse(summary.validate_plan(cohort))
        cohort['attempts']=[dict(repeat=1,problem='wrong',modulus=13,route='fglm',arm='stage-on')]
        with self.assertRaises(ValueError): summary.validate_plan(cohort)

    # An eligible-stage ceiling uses the full duration from the same attempt and rejects bad clocks.
    def test_same_attempt_ceiling(self):
        self.assertAlmostEqual(summary.ceiling(100,20),1.25)
        for total,part in [(0,0),(10,11),(10,-1)]:
            with self.assertRaises(ValueError): summary.ceiling(total,part)


if __name__=='__main__': unittest.main()
