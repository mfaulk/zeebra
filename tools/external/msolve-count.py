#!/usr/bin/env python3
"""Build a work-counting copy of the provisioned msolve 0.11.0 (#737).

Copies the source tree, inserts pivot-application and coefficient-product counters into
the exact sparse linear algebra (`laopt 2`), and runs `make`. The copy is a modified GPL
program: it is a private measurement instrument, never installed, linked or distributed.
This script contains no msolve source; it edits by pattern and refuses if a pattern's
match count differs from the pinned release's.

Usage: python3 -I tools/external/msolve-count.py <msolve-0.11.0 source> <scratch dir>
Run:   LD_LIBRARY_PATH=<scratch>/src/neogb/.libs <scratch>/.libs/msolve -f in.ms -t 1 -g 2
The counts go to stderr on exit as one `ZB_COUNT ...` line.
"""
import pathlib
import re
import shutil
import subprocess
import sys

COUNTERS = r'''/* zeebra#737 counters: [phase][0] pivot applications, [phase][1] coefficient products.
 * Phase 0: lower rows against known and new pivots. 1: interreduction of new pivots.
 * 2: the final basis reduction. */
#include <stdio.h>
#include <inttypes.h>
uint64_t zb_cnt[3][2];
int zb_phase;
static void zb_report(void) __attribute__((destructor));
static void zb_report(void) {
    fprintf(stderr, "ZB_COUNT forward_apps %" PRIu64 " forward_products %" PRIu64
        " newpiv_apps %" PRIu64 " newpiv_products %" PRIu64
        " final_apps %" PRIu64 " final_products %" PRIu64 "\n",
        zb_cnt[0][0], zb_cnt[0][1], zb_cnt[1][0], zb_cnt[1][1], zb_cnt[2][0], zb_cnt[2][1]);
}
#define ZB_COUNT(len) do { int zp_ = zb_phase; \
    __atomic_fetch_add(&zb_cnt[zp_][0], 1, __ATOMIC_RELAXED); \
    __atomic_fetch_add(&zb_cnt[zp_][1], (uint64_t)(len), __ATOMIC_RELAXED); } while (0)
'''

# file -> (reducer-row sites, exact echelon entry points, new-pivot interreduction blocks)
EXPECTED = {"la_ff_16.c": (2, 1, 5), "la_ff_32.c": (9, 1, 5)}


def patch(neogb: pathlib.Path) -> None:
    gb = neogb / "gb.c"
    text = gb.read_text()
    anchor = '#include "la_ff_16.c"'
    if text.count(anchor) != 1:
        sys.exit(f"{gb}: expected one {anchor!r}")
    gb.write_text(text.replace(anchor, COUNTERS + anchor))
    for name, expected in EXPECTED.items():
        path = neogb / name
        text = path.read_text()
        text, sites = re.subn(
            r"(\n(\s*)dts\s*=\s*pivs\[i\];)", r"\1\n\2ZB_COUNT(dts[LENGTH]);", text
        )
        text, entries = re.subn(
            r"(static void exact_sparse_reduced_echelon_form_ff_(?:16|32)\([^{]*\{)",
            r"\1\n    zb_phase = st->in_final_reduction_step == 1 ? 2 : 0;",
            text,
        )
        text, blocks = re.subn(
            r"(\n\s*/\* interreduce new pivots \*/)", r"\n        zb_phase = 1;\1", text
        )
        if (sites, entries, blocks) != expected:
            sys.exit(f"{path}: matched {(sites, entries, blocks)}, pinned 0.11.0 has {expected}")
        path.write_text(text)


def main() -> None:
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    source, scratch = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
    if scratch.exists():
        sys.exit(f"{scratch} exists; choose a fresh directory")
    shutil.copytree(source, scratch, symlinks=True)
    patch(scratch / "src" / "neogb")
    (scratch / "src" / "neogb" / "gb.c").touch()
    subprocess.run(["make", "-j8"], cwd=scratch, check=True, stdout=subprocess.DEVNULL)
    print(scratch / ".libs" / "msolve")


if __name__ == "__main__":
    main()
