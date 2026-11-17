import json, sys, statistics as st
rows = [json.loads(l) for l in open(sys.argv[1])]
stages = len(sys.argv) > 2
by = {}
for r in rows:
    by.setdefault((r["target"], r["arm"]), []).append(r)
targets = ["mq10-32003", "mq10-m31", "eco12-wide64", "mq11-goldilocks"]
def med(xs): return st.median(xs)
for t in targets:
    base = by.get((t, "base"), [])
    if not base: continue
    shas = {r["run"]["basis_sha256"] for a in ("base", "new", "basefl") for r in by.get((t, a), []) if r["run"]}
    print(f"{t}: basis digests {len(shas)}")
    bw = med([r["wall_ms"] for r in base]); brss = med([r["rss_kb"] for r in base])
    for a in ("base", "new", "basefl"):
        rs = by.get((t, a), [])
        w = [r["wall_ms"] for r in rs]; f = [r["run"]["f4_call_ns"] / 1e6 for r in rs]
        line = f"  {a:7} wall {med(w):8.1f} [{min(w):.1f},{max(w):.1f}]  f4 {med(f):8.1f}  base/arm {bw/med(w):.3f}x  rss {med([r['rss_kb'] for r in rs])/brss:.3f}x  load {min(r['load'] for r in rs)}-{max(r['load'] for r in rs)}"
        if stages:
            s = lambda k: med([r["run"]["statistics"][k] / 1e6 for r in rs])
            line += f"\n          sym {s('symbolic_ns'):.1f} cons {s('construction_ns'):.1f} fwd {s('forward_ns'):.1f} bwd {s('backward_ns'):.1f} extr {s('extraction_ns'):.1f} interred {s('interreduction_ns'):.1f}"
            cr = rs[0]["run"]["statistics"]["candidate_reduction"]
            line += f"  products {cr['coefficient_products']} reserved {cr['reserved_entries']} req {rs[0]['run']['statistics']['live_entry_requirement']}"
        print(line)
