#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent


def load():
    spec = importlib.util.spec_from_file_location('signature_overlay', HERE / 'overlay.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


ENTRY = ('        let handover = engine.signature().then_some(on(!C::TRACKS));\n'
         '                let handover = (!C::TRACKS).then_some(HANDOVER);\n')


class SignatureOverlayTests(unittest.TestCase):
    # Both handover sites gain the same switch, so the report and the engine agree.
    def test_both_handover_sites_gated(self):
        out = load().entry_gate(ENTRY)
        self.assertEqual(out.count('crate::research_sig::handover_enabled()'), 2)
        self.assertEqual(out.count('!C::TRACKS'), 2)

    # The pair tally is inserted once, before the kept pairs are ordered.
    def test_pair_tally_inserted(self):
        out = load().pair_tally('    new.kept.sort_unstable_by_key(|&(place, _, _)| place);\n')
        self.assertTrue(out.startswith('    crate::research_sig::plain_update('))

    # Missing or duplicated anchors fail closed instead of patching another path.
    def test_changed_anchors_refused(self):
        overlay = load()
        for fn, source in [(overlay.entry_gate, ''), (overlay.entry_gate, ENTRY * 2),
                           (overlay.pair_tally, ''), (overlay.driver_main, '')]:
            with self.subTest(fn=fn.__name__), self.assertRaises(ValueError):
                fn(source)


if __name__ == '__main__':
    unittest.main()
