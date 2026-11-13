#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import tempfile
import unittest

HERE = Path(__file__).resolve().parent

def module():
    spec = importlib.util.spec_from_file_location('instrument', HERE / 'instrument.py')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


class InstrumentTests(unittest.TestCase):
    # Missing or moved anchors must refuse instrumentation rather than patching another kernel.
    def test_mismatched_pin_is_refused(self):
        instrument = module()
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory)
            (source / 'src').mkdir()
            (source / 'src/lib.rs').write_text('changed source')
            with self.assertRaisesRegex(ValueError, 'pinned'):
                instrument.instrument(source)

    # Duplicate source anchors are refused rather than instrumenting two unintended kernels.
    def test_duplicate_anchor_is_refused(self):
        with self.assertRaisesRegex(ValueError, 'anchor changed'):
            module().replace('kernel kernel', 'kernel', 'counter kernel')


if __name__ == '__main__':
    unittest.main()
