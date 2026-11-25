#!/usr/bin/env python3
"""#1134: the out-of-sample rows, as a corpus-instance-v1 catalog at p31 on stdout.

Every row is built by the #1007 structural-corpus generators (tools/m34_structural_corpus.py) at
parameters no M34 cohort holds, so none is in the development, validation or untouched cohorts. The
list was fixed in README.md before any row was solved. It leans towards wide degree profiles, because
the dispatcher keeps those on conventional F4 (`DegreeSpread`), the route the fallback acts on.

  python3 research/1134-refusal-fallback/candidates.py > research/1134-refusal-fallback/candidates.json
"""
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
import m34_structural_corpus as corpus  # noqa: E402

COL, DET, PD = "zb/graph-3colouring", "zb/determinantal", "zb/planted-dense"
P = corpus.P
CANDIDATES = [
    *[P(f"oos-{name}-{n}", name, name=name, n=n) for name, n in [
        ("reimer", 5), ("reimer", 7), ("cyclic", 8), ("katsura", 11), ("eco", 11), ("noon", 8)]],
    P("oos-col-grid-4x4", COL, graph_kind="grid", rows=4, cols=4, count_colourings=False),
    P("oos-col-gnm-16-24-s1", COL, 1, graph_kind="gnm", n=16, m=24, count_colourings=False),
    P("oos-pd-6-8-d2d4-s1", PD, 1, n=6, degrees=[2] * 4 + [4] * 4),
    P("oos-pd-7-7-d2d4-s1", PD, 1, n=7, degrees=[2] * 4 + [4] * 3),
    P("oos-pd-5-5-d2d5-s1", PD, 1, n=5, degrees=[2] * 3 + [5] * 2),
    P("oos-pd-6-6-d3d5-s1", PD, 1, n=6, degrees=[3] * 4 + [5] * 2),
    P("oos-det-2x5-quad-s1", DET, 1, rows=2, cols=5, n=4, entry_degree=2),
    P("oos-det-2x6-quad-s1", DET, 1, rows=2, cols=6, n=5, entry_degree=2),
]


def main():
    cohorts = json.loads((ROOT / "research/m34-gate-h/s0/cohorts.json").read_text())["assignments"]
    held = {k.split("@")[0] for k in cohorts}
    rows = []
    for problem in CANDIDATES:
        assert problem["id"] not in held, problem["id"]
        rows.append(corpus.record(problem, corpus.build(problem), "p31"))
    sys.stdout.write("[\n" + ",\n".join(json.dumps(r, separators=(",", ":")) for r in rows) + "\n]\n")


if __name__ == "__main__":
    main()
