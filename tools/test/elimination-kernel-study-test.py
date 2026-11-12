#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest

path = Path(__file__).resolve().parents[1] / 'external/elimination-kernel-study.py'
spec = importlib.util.spec_from_file_location('kernels', path)
kernels = importlib.util.module_from_spec(spec)
spec.loader.exec_module(kernels)

summary_spec = importlib.util.spec_from_file_location('summary', path.parents[2] / 'research/elimination-kernels/summarize.py')
summary = importlib.util.module_from_spec(summary_spec)
summary_spec.loader.exec_module(summary)


class Acceptance(unittest.TestCase):
    # Every field gets three shapes, four nested masks and every backend, without duplicate cells.
    def test_curve_coverage(self):
        cells = list(kernels.curve_cells())
        self.assertEqual(len(cells), 108)
        self.assertEqual(len(set(cells)), 108)
        self.assertEqual({row[0] for row in cells}, {'m31', 'p64', 'bn254'})

    # Matching rank cannot hide a changed coefficient, source capture, support budget or work count.
    def test_matrix_acceptance(self):
        reference = {key: 'same' for key in kernels.IDENTITY}
        kernels.check_matrix(reference, reference)
        for key in kernels.IDENTITY:
            with self.subTest(key=key), self.assertRaises(ValueError):
                kernels.check_matrix(dict(reference, **{key: 'different'}), reference)
        with self.assertRaises(KeyError):
            kernels.check_matrix({}, reference)

    # A missing or zero RSS report is an unmeasured run rather than evidence of low memory use.
    def test_rss_required(self):
        for report in ({}, {'peak_rss_bytes': None}, {'peak_rss_bytes': 0}):
            with self.subTest(report=report), self.assertRaises(ValueError):
                kernels.check_rss(report)
        kernels.check_rss({'peak_rss_bytes': 1000})

    # Zero remote fills are valid, but absent events or a multiplexed region cannot be accepted.
    def test_region_events(self):
        raw = '\n'.join(f'{0 if "remote" in event else 100};;{event};1000;100.00;;' for event in kernels.EVENTS)
        self.assertEqual(kernels.read_events(raw)[kernels.EVENTS[-1]], 0)
        for invalid in ('', raw.replace(';100.00;', ';50.00;', 1), raw.replace('100;;cycles:u', '0;;cycles:u')):
            with self.subTest(raw=invalid), self.assertRaises(ValueError):
                kernels.read_events(invalid)

    # Paired ratios use each repetition's comparison rather than the ratio of independent medians.
    def test_paired_summary(self):
        rows = []
        for repeat, (baseline, candidate) in enumerate([(1, 2), (100, 50), (100, 200)]):
            for arm, value in [('baseline', baseline), ('candidate', candidate)]:
                rows.append(dict(repeat=repeat, arm=arm, report=dict(time=value, peak_rss_bytes=1000)))
        result = summary.paired(rows, lambda row: row['time'])
        self.assertEqual(result['paired_ratio'], 2)
        self.assertEqual(result['baseline_ms'], 100 / 1e6)
        self.assertEqual(result['candidate_ms'], 50 / 1e6)
        with self.assertRaises(ValueError):
            summary.paired(rows[:-1], lambda row: row['time'])

    # Structural comparisons discard timing fields while retaining observable work counters.
    def test_structural_comparison_excludes_clocks(self):
        self.assertEqual(summary.structural(dict(statistics=dict(row_operations=7, total_ns=100, full_statistics='clocks'))), {'row_operations': 7})
        self.assertEqual(summary.structural(dict(statistics='row_operations: 7,\nelimination: 1ms,')), {'row_operations': '7'})

    # Every retained raw artifact matches the committed SHA256 inventory, with no unlisted files.
    def test_retained_artifact_hashes(self):
        import hashlib
        import json
        root = summary.ROOT / 'results'
        manifest = json.loads((root / 'sha256.json').read_text())
        self.assertEqual({p.name for p in root.iterdir() if p.name != 'sha256.json'}, set(manifest))
        for name, expected in manifest.items():
            with self.subTest(name=name):
                self.assertEqual(hashlib.sha256((root / name).read_bytes()).hexdigest(), expected)


if __name__ == '__main__':
    unittest.main()
