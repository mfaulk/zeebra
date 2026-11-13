#!/usr/bin/env python3
"""The msolve counting recipe patches every pinned site and refuses a source it does not recognize."""
import importlib.util
import pathlib
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    "msolve_count", pathlib.Path(__file__).resolve().parents[1] / "external/msolve-count.py"
)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

SITE = "\n        dts   = pivs[i];"
ENTRY = "static void exact_sparse_reduced_echelon_form_ff_{w}(\n        mat_t *mat,\n        md_t *st\n        )\n{{\n}}\n"
BLOCK = "\n        /* interreduce new pivots */"


def source(width, sites, entries=1, blocks=5):
    return SITE * sites + ENTRY.format(w=width) * entries + BLOCK * blocks + "\n"


def tree(root, sites16=2, sites32=9):
    neogb = pathlib.Path(root)
    (neogb / "gb.c").write_text('#include "la_ff_16.c"\n#include "la_ff_32.c"\n')
    (neogb / "la_ff_16.c").write_text(source(16, sites16))
    (neogb / "la_ff_32.c").write_text(source(32, sites32))
    return neogb


class PatchTests(unittest.TestCase):
    # Every reducer-row site gains a counter, and each phase marker lands once per pinned site.
    def test_pinned_shape_is_patched(self):
        with tempfile.TemporaryDirectory() as root:
            neogb = tree(root)
            module.patch(neogb)
            self.assertIn("uint64_t zb_cnt[3][2];", (neogb / "gb.c").read_text())
            for name, (sites, _, blocks) in module.EXPECTED.items():
                text = (neogb / name).read_text()
                self.assertEqual(text.count("ZB_COUNT(dts[LENGTH]);"), sites)
                self.assertEqual(text.count("zb_phase = 1;"), blocks)
                self.assertEqual(text.count("in_final_reduction_step == 1 ? 2 : 0"), 1)

    # A source whose kernel sites moved is refused rather than counted partially.
    def test_changed_source_is_refused(self):
        with tempfile.TemporaryDirectory() as root:
            neogb = tree(root, sites32=8)
            with self.assertRaises(SystemExit):
                module.patch(neogb)


if __name__ == "__main__":
    unittest.main()
