#!/usr/bin/env python3
import copy
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('adoption_summary', ROOT/'research/candidate-adoption/summary.py')
summary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(summary)
driver = summary.tool('selective-backward-study')


def fixture():
    ref = dict(digest='d', modulus=13, basis=['x'])
    stats = dict.fromkeys(driver.TRAJECTORY, 1)
    stats.update(batches=1, candidate_reduction=dict(batches=1,coefficient_products=1))
    stats.update(dict.fromkeys(('symbolic_ns','construction_ns','elimination_ns','extraction_ns',
                               'interreduction_ns','other_ns'),1))
    raw = dict(ref, problem='mq-random-10', backward=None, parallel=None, statistics=stats,
               f4_call_ns=10, peak_rss_bytes=100,
               work=dict(batches=[dict(forward=dict(coefficient_products=2),backward=dict(coefficient_products=1))]))
    attempt = dict(repeat=0, problem='mq-random-10',modulus=13,arm='production',status='verified',
                   exit=0,stop=None,raw=raw,process_wall_ns=20,observed_peak_rss_bytes=100,cpu_seconds=1)
    cohort = dict(identity=dict(phase='adoption',compiler_gate=True,baseline_commit='a',build_commit='b',binaries={name:dict(sha256='a'*64) for name in ('stock','binary','production')}),attempts=[attempt])
    return dict(adoption=cohort), {('mq-random-10',13):ref}


class AdoptionSummary(unittest.TestCase):
    def run_summary(self, cohorts, refs):
        with patch.object(summary,'tool',return_value=driver), patch.object(driver,'plan',return_value=[(0,'mq-random-10',13,'production')]):
            return summary.summarize(cohorts,refs)

    # Retained full answers, source identity and complete plans are required for a native table.
    def test_verified_attempt_and_tampering(self):
        cohorts,refs=fixture()
        self.assertEqual(len(self.run_summary(cohorts,refs)['rows']),1)
        for key,value in [('status','failed'),('compiler_after',['rustc']),('process_wall_ns',1)]:
            broken=copy.deepcopy(cohorts);broken['adoption']['attempts'][0][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):self.run_summary(broken,refs)
        broken=copy.deepcopy(cohorts);broken['adoption']['attempts'][0]['raw']['basis']=['x+1']
        with self.assertRaises(ValueError):self.run_summary(broken,refs)
        broken=copy.deepcopy(cohorts);broken['adoption']['identity'].pop('baseline_commit')
        with self.assertRaises(ValueError):self.run_summary(broken,refs)
        broken=copy.deepcopy(cohorts);broken['adoption']['identity']['binaries']['production']['sha256']='short'
        with self.assertRaises(ValueError):self.run_summary(broken,refs)
        broken=copy.deepcopy(cohorts);broken['adoption']['attempts']*=2
        with self.assertRaises(ValueError):self.run_summary(broken,refs)


if __name__ == '__main__':
    unittest.main()
