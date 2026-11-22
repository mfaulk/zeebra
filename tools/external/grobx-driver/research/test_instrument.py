#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import shutil
import sys
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

    # A copy of the normal driver at a newer pin is retargeted to the instrumented source, its REVISION and its lock.
    def test_driver_at_a_newer_pin_is_retargeted_to_the_instrumented_pin(self):
        sys.path.insert(0, str(HERE))
        import provision
        with tempfile.TemporaryDirectory() as directory:
            driver = Path(directory) / 'driver'
            shutil.copytree(HERE.parent, driver, ignore=shutil.ignore_patterns('research', 'target'))
            provision.retarget(driver)
            cargo = (driver / 'Cargo.toml').read_text()
            self.assertIn('grobx = { path = "../source" }', cargo)
            self.assertIn('grobx-checker = { path = "../source/checker" }', cargo)
            self.assertNotIn('code1-de', cargo)
            self.assertIn(f'const REVISION: &str = "{provision.PIN}";', (driver / 'src/main.rs').read_text())
            self.assertEqual((driver / 'Cargo.lock').read_bytes(),
                             (HERE / f'grobx-{provision.PIN[:8]}.Cargo.lock').read_bytes())
            with self.assertRaisesRegex(ValueError, 'REVISION'):
                provision.retarget(driver)


if __name__ == '__main__':
    unittest.main()
