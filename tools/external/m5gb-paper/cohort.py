"""#1165 development cohort: run the authors' M5GB on each row and verify its basis.

    tools/external/provision-m5gb-paper.sh            # prints the binary
    cargo build --release --example m5gb_paper_reference
    python3 tools/external/m5gb-paper/cohort.py manifest > research/1165-m5gb-paper-reference/manifest.json
    python3 tools/external/m5gb-paper/cohort.py run --variant upstream \
        --sympy-python <python with sympy> > research/1165-m5gb-paper-reference/runs-upstream.jsonl

One M5GB subprocess per row, under a wall cap and an RSS watchdog (`m5gb_paper.run_binary`).
Its `.gb` output is canonicalized (minimized and interreduced, with every output element checked to
reduce to zero) and compared, polynomial for polynomial, with Zeebra's reduced basis
(`examples/m5gb_paper_reference.rs`) and, on small rows, SymPy's (`sympy_ref.py`). Statuses are
kept distinct: `verified`, `wrong`, `unverified` (no reference answered), or the run's own failure
(`signal:*`, `exit:*`, `wall-cap`, `rss-cap`). Laptop timings are development figures only.
"""

import argparse
import hashlib
import json
import os
import random
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import m5gb_paper as m  # noqa: E402

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
PREFIX = os.environ.get(
    "ZEEBRA_M5GB_PREFIX", os.path.expanduser("~/.cache/zeebra-external/m5gb-paper")
)
TARGET = os.environ.get("CARGO_TARGET_DIR", os.path.join(ROOT, "target"))
ZEEBRA = os.path.join(TARGET, "release", "examples", "m5gb_paper_reference")
SEED_BASE = 116500  # fresh seeds: M35's MQ rows use seed = n (research/1162-m35-baseline/panel.json)
# Largest variable count `examples/m5gb_paper_reference.rs` registers per field (31 and 65521
# also register 14 and 16, for the `scale` rows).
ZEEBRA_FIELDS = {31: 16, 101: 12, 32003: 12, 65521: 16, 2147483647: 8, 4294967291: 8}

WALL_CAP_S = 60
RSS_CAP_BYTES = 4 << 30
# The canonicalizer is pure Python; an output above this many terms is left unverified.
CANON_MAX_TERMS = 1_000_000


def names(n):
    return [f"x{i + 1}" for i in range(n)]


def row(name, family, p, n, polys, order="grevlex", source=None, **extra):
    variables = names(n)
    m.set_order(order)
    system = [m.format_zeebra(m.normalize(f, p), variables) for f in polys]
    out = {
        "name": name,
        "family": family,
        "modulus": p,
        "variables": variables,
        "system": system,
        "order": order,
        "n": n,
        "m": len(polys),
    }
    if source:
        out["source"] = source
    out.update(extra)
    return out


def rand_poly(rng, p, n, degree, density=1.0, homogeneous=False):
    poly = {}
    for e in monos(n, degree):
        if homogeneous and sum(e) != degree:
            continue
        if rng.random() <= density:
            poly[e] = rng.randrange(1, p)
    return poly


def monos(n, degree):
    out = [()]
    for _ in range(n):
        out = [e + (k,) for e in out for k in range(degree + 1)]
    return [e for e in out if sum(e) <= degree]


def var(n, i, power=1):
    e = [0] * n
    e[i] = power
    return tuple(e)


ONE = lambda n: (0,) * n  # noqa: E731


def toy_rows(maxn):
    """The authors' GF(101) toys (`code/bench_f101`), read from the fetched tree."""
    bench = os.path.join(PREFIX, "src", "m5gb", "code", "bench_f101")
    rows = []
    for fname in sorted(os.listdir(bench)):
        if not fname.endswith(".ideal"):
            continue
        n = int(fname.split("-n")[1].split("_")[0])
        if n > maxn:
            continue
        path = os.path.join(bench, fname)
        with open(path) as f:
            header = f.readline().split()
            count = int(f.readline())
            polys = [m.parse_mathic(f.readline(), n, int(header[0])) for _ in range(count)]
        with open(path, "rb") as f:
            digest = hashlib.sha256(f.read()).hexdigest()
        rows.append(
            row(
                fname[: -len(".ideal")], "authors-toy", int(header[0]), n, polys,
                source=f"m5gb@16ef968d:code/bench_f101/{fname} sha256={digest}",
            )
        )
    rows.sort(key=lambda r: (r["n"], r["name"]))
    return rows


def dense_row(n, mm, density, seed, p, planted):
    args = [ZEEBRA, "emit-dense", "--n", str(n), "--m", str(mm), "--density", str(density),
            "--seed", str(seed), "--modulus", str(p)]
    if not planted:
        args.append("--unplanted")
    line = json.loads(subprocess.run(args, capture_output=True, text=True, check=True).stdout)
    variables = line["variables"]
    polys = [m.parse_zeebra(s, variables, p) for s in line["system"]]
    tag = "planted" if planted else "unplanted"
    return row(
        f"dense-n{n}-m{mm}-d{density}-s{seed}-p{p}-{tag}", "dense-mq", p, n, polys,
        source=f"corpus::dense_mq_shaped({n}, {mm}, {density}, {seed}, {p}, grevlex, {planted})",
        density=density, seed=seed, planted=planted,
    )


def dense_rows(p, ns, ratios, densities, seeds, planted_options):
    rows = []
    for n in ns:
        for ratio in ratios:
            mm = int(round(ratio * n))
            for density in densities:
                for seed in seeds:
                    for planted in planted_options:
                        rows.append(dense_row(n, mm, density, seed, p, planted))
    return rows


def control_rows(p):
    rng = random.Random(SEED_BASE + p)
    rows = []
    n = 4
    base = [rand_poly(rng, p, n, 2) for _ in range(6)]
    # Planted point: shift constants so (1, 2, 3, 4) is a zero.
    point = (1, 2, 3, 4)
    planted = []
    for f in base:
        value = sum(c * pow(point[0], e[0], p) * pow(point[1], e[1], p) * pow(point[2], e[2], p)
                    * pow(point[3], e[3], p) for e, c in f.items()) % p
        g = dict(f)
        g[ONE(n)] = (g.get(ONE(n), 0) - value) % p
        planted.append(g)
    f1, f2 = planted[0], planted[1]
    combo = {e: (f1.get(e, 0) + 3 * f2.get(e, 0)) % p for e in set(f1) | set(f2)}
    rows.append(row("redundant-combination", "control", p, n, planted[:5] + [combo]))
    rows.append(row("duplicate-generator", "control", p, n, planted[:5] + [planted[0]]))
    rows.append(row("zero-generator", "control", p, n, planted[:5] + [{}]))
    rows.append(row("unit-constant", "control", p, n, planted[:3] + [{ONE(n): 3}]))
    rows.append(row("unit-inconsistent-linear", "control", p, 2,
                    [{var(2, 0): 1}, {var(2, 0): 1, ONE(2): p - 1}]))
    unit = dict(planted[0])
    unit[ONE(n)] = (unit.get(ONE(n), 0) + 1) % p
    rows.append(row("unit-dense", "control", p, n, planted[:5] + [unit]))
    for mm in (3, 4, 5, 7):
        rows.append(row(f"homogeneous-n5-m{mm}", "control", p, 5,
                        [rand_poly(rng, p, 5, 2, homogeneous=True) for _ in range(mm)]))
    rows.append(row("affine-underdetermined-n5-m3", "control", p, 5,
                    [rand_poly(rng, p, 5, 2) for _ in range(3)]))
    rows.append(row("sparse-affine-n6-m8", "control", p, 6,
                    [rand_poly(rng, p, 6, 2, density=0.3) for _ in range(8)]))
    rows.append(row("cubic-affine-n4-m5", "control", p, 4,
                    [rand_poly(rng, p, 4, 3, density=0.5) for _ in range(5)]))
    # Triangular: x1^2 - x2, x2^2 - x3, x3^2 - 1.
    rows.append(row("triangular", "control", p, 3, [
        {var(3, 0, 2): 1, var(3, 1): p - 1},
        {var(3, 1, 2): 1, var(3, 2): p - 1},
        {var(3, 2, 2): 1, ONE(3): p - 1},
    ]))
    # Nonradical: (x1 - 1)^2, (x1 - 1) * (x2 + 2), x2^3.
    rows.append(row("nonradical", "control", p, 2, [
        {var(2, 0, 2): 1, var(2, 0): p - 2, ONE(2): 1},
        {(1, 1): 1, var(2, 0): 2, var(2, 1): p - 1, ONE(2): p - 2},
        {var(2, 1, 3): 1},
    ]))
    rows.append(row("monomial", "control", p, 3, [
        {(2, 0, 0): 1}, {(1, 1, 0): 1}, {(0, 2, 1): 1},
    ]))
    # cyclic-4: positive-dimensional, structured.
    c = [{var(4, 0): 1, var(4, 1): 1, var(4, 2): 1, var(4, 3): 1},
         {(1, 1, 0, 0): 1, (0, 1, 1, 0): 1, (0, 0, 1, 1): 1, (1, 0, 0, 1): 1},
         {(1, 1, 1, 0): 1, (0, 1, 1, 1): 1, (1, 0, 1, 1): 1, (1, 1, 0, 1): 1},
         {(1, 1, 1, 1): 1, ONE(4): p - 1}]
    rows.append(row("cyclic-4", "control", p, 4, c))
    rows.append(row("single-generator", "control", p, 3,
                    [{(2, 1, 0): 1, (0, 0, 2): 5, ONE(3): 7}]))
    return rows


def lex_rows(p):
    return [dict(r, name=r["name"] + "-lex", order="lex") for r in control_rows(p)
            if r["name"] in ("triangular", "nonradical", "redundant-combination", "cyclic-4",
                             "monomial")]


def collision_rows(p):
    """Inputs built on a hash collision of this host's libc (`hash_collision.py`)."""
    import hash_collision as hc

    out = []
    _, pairs = hc.collisions(12, 7, 1)
    if pairs:
        a, b = tuple(pairs[0]["a"]), tuple(pairs[0]["b"])
        n = 12
        out.append(row("collision-two-terms", "hash-collision", p, n, [{a: 1, b: 1}],
                       collision={"a": list(a), "b": list(b)}))
        out.append(row("collision-separate", "hash-collision", p, n, [
            {a: 1, var(n, 0): 1},
            {b: 1, var(n, 1): 1},
            {var(n, 0, 2): 1, var(n, 1): 1},
        ], collision={"a": list(a), "b": list(b)}))
    return out


def manifest():
    rows = []
    rows += toy_rows(8)
    rows += control_rows(101)
    rows += lex_rows(101)
    rows += dense_rows(101, (6, 8, 10), (1.5, 2.0, 3.0), (1000, 500),
                       (SEED_BASE + 1, SEED_BASE + 2), (True, False))
    rows += collision_rows(101)
    for p in (31, 65521):
        rows += [dict(r, family="scale") for r in
                 dense_rows(p, (12,), (1.5, 2.0, 3.0), (1000,), (SEED_BASE + 1,), (True, False))
                 + dense_rows(p, (14, 16), (2.0, 3.0), (1000,), (SEED_BASE + 1,), (True,))]
    for p in (31, 32003, 65521, 2147483647, 4294967291, 4294967311, 9223372036854775783):
        rows += [dict(r, name=f"{r['name']}-p{p}") for r in _repriced(p)]
    return rows


def _repriced(p):
    rows = [r for r in control_rows(p) if r["name"] in (
        "redundant-combination", "triangular", "nonradical", "cyclic-4", "homogeneous-n5-m5",
        "affine-underdetermined-n5-m3", "unit-dense")]
    if p < 2**63:
        rows += dense_rows(p, (6,), (2.0,), (1000,), (SEED_BASE + 1,), (True, False))
        if p <= 65521:
            rows += dense_rows(p, (8,), (1.5, 2.0), (1000,), (SEED_BASE + 1,), (True,))
    return rows


# --- references ---------------------------------------------------------------------------------


def zeebra_answers(rows, wall):
    wanted = [r for r in rows if r["order"] == "grevlex"
              and ZEEBRA_FIELDS.get(r["modulus"], 0) >= r["n"]]
    if not wanted:
        return {}
    payload = "\n".join(json.dumps({k: r[k] for k in ("name", "modulus", "variables", "system")})
                        for r in wanted) + "\n"
    out = subprocess.run([ZEEBRA, "solve", "--wall", str(wall)], input=payload,
                         capture_output=True, text=True)
    answers = {}
    for line in out.stdout.splitlines():
        a = json.loads(line)
        answers[a["name"]] = a
    return answers


def sympy_answer(r, python, wall):
    if not python:
        return None
    script = os.path.join(os.path.dirname(os.path.abspath(__file__)), "sympy_ref.py")
    try:
        out = subprocess.run([python, "-I", script], input=json.dumps(r) + "\n",
                             capture_output=True, text=True, timeout=wall)
    except subprocess.TimeoutExpired:
        return {"status": "wall-cap"}
    if out.returncode != 0:
        return {"status": f"exit:{out.returncode}", "stderr": out.stderr[-300:]}
    return {"status": "complete", **json.loads(out.stdout)}


def canonical_of(basis_text, r):
    p = r["modulus"]
    polys = [m.parse_zeebra(s, r["variables"], p) for s in basis_text]
    reduced, _, _ = m.canonical_reduced(polys, p)
    return m.canonical_text(reduced, r["variables"])


# --- one row ------------------------------------------------------------------------------------


def run_row(r, binary, workdir, zeebra, sympy_python, sympy_max_n, wall_cap=WALL_CAP_S):
    p, n = r["modulus"], r["n"]
    m.set_order(r["order"])
    rundir = os.path.join(workdir, r["name"])
    os.makedirs(rundir, exist_ok=True)
    ideal = os.path.join(rundir, "input.ideal")
    polys = [m.parse_zeebra(s, r["variables"], p) for s in r["system"]]
    m.write_ideal(ideal, polys, n, p)
    with open(ideal, "rb") as f:
        input_sha = hashlib.sha256(f.read()).hexdigest()
    run = m.run_binary(binary, ideal, wall_cap, RSS_CAP_BYTES)
    record = {
        "row": r["name"], "family": r["family"], "n": n, "m": r["m"], "modulus": p,
        "order": r["order"], "input_sha256": input_sha,
        "m5gb": {k: run[k] for k in ("status", "wall_s", "peak_rss_bytes",
                                     "sampled_peak_rss_bytes")},
        "counters": m.parse_counters(run["stdout"]),
    }
    if run["status"] != "ok":
        record["stderr_tail"] = (run["stderr"] or run["stdout"])[-400:]
    refs = {}
    z = zeebra.get(r["name"])
    if z is not None:
        refs["zeebra"] = z["status"]
        # In-process F4Options::default(), one worker; a development figure like M5GB's own.
        record["zeebra_wall_s"] = z["wall_ns"] / 1e9
    sym = None
    if r["n"] <= sympy_max_n:
        sym = sympy_answer({k: r[k] for k in ("modulus", "variables", "system", "order")},
                           sympy_python, WALL_CAP_S)
        if sym is not None:
            refs["sympy"] = sym["status"]
    expected = {}
    if z is not None and z["status"] == "complete":
        expected["zeebra"] = canonical_of(z["basis"], r)
    if sym is not None and sym["status"] == "complete":
        expected["sympy"] = canonical_of(sym["basis"], r)
    record["references"] = refs
    if len(expected) == 2:
        record["references_agree"] = expected["zeebra"] == expected["sympy"]
    gb_path = ideal + ".gb"
    if run["status"] != "ok" or not os.path.exists(gb_path):
        record["verdict"] = run["status"] if run["status"] != "ok" else "no-output"
        return record
    raw = m.parse_gb_file(gb_path, n, p)
    terms = sum(len(g) for g in raw)
    record["raw"] = {"elements": len(raw), "terms": terms}
    if terms > CANON_MAX_TERMS:
        record["verdict"] = "unverified"
        record["detail"] = f"output has {terms} terms, over the canonicalizer's {CANON_MAX_TERMS}"
        return record
    start = time.monotonic()
    reduced, zero, steps = m.canonical_reduced(raw, p)
    canon_s = time.monotonic() - start
    ours = m.canonical_text(reduced, r["variables"])
    record["raw"]["already_reduced"] = m.is_reduced(raw, p)
    record["canonical"] = {"elements": len(reduced), "all_outputs_reduce_to_zero": zero,
                           "reduction_steps": steps, "seconds": round(canon_s, 4)}
    if not expected:
        record["verdict"] = "unverified"
        return record
    bad = [name for name, basis in expected.items() if basis != ours]
    if not bad and zero:
        record["verdict"] = "verified"
        record["verified_by"] = sorted(expected)
    else:
        record["verdict"] = "wrong"
        ref = expected[bad[0]] if bad else next(iter(expected.values()))
        record["detail"] = {
            "against": bad or sorted(expected), "reference_elements": len(ref),
            "zero_check": zero,
            "first_difference": next(([a, b] for a, b in zip(ref, ours) if a != b),
                                     ["<length differs>", ""]),
        }
    return record


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("manifest")
    run = sub.add_parser("run")
    run.add_argument("--variant", default="upstream")
    run.add_argument("--workdir", default=None)
    run.add_argument("--sympy-python", default=None)
    run.add_argument("--sympy-max-n", type=int, default=6)
    run.add_argument("--only", default=None, help="substring filter on row names")
    run.add_argument("--family", default=None, help="comma-separated families to keep")
    run.add_argument("--max-modulus", type=int, default=None)
    run.add_argument("--zeebra-wall", type=int, default=120)
    run.add_argument("--wall-cap", type=int, default=WALL_CAP_S,
                     help="M5GB per-run wall cap in seconds; raise it only for diagnostic variants")
    args = parser.parse_args()

    rows = manifest()
    if args.cmd == "manifest":
        json.dump({
            "issue": 1165, "wall_cap_s": WALL_CAP_S, "rss_cap_bytes": RSS_CAP_BYTES,
            "rows": [{k: v for k, v in r.items() if k != "system"} | {
                "system_sha256": hashlib.sha256("\n".join(r["system"]).encode()).hexdigest()}
                for r in rows],
        }, sys.stdout, indent=1)
        print()
        return
    if args.only:
        rows = [r for r in rows if args.only in r["name"]]
    if args.family:
        rows = [r for r in rows if r["family"] in args.family.split(",")]
    if args.max_modulus:
        rows = [r for r in rows if r["modulus"] <= args.max_modulus]
    binary = os.path.join(PREFIX, "bin", f"runm5gb-{args.variant}")
    with open(binary + ".build") as f:
        build = f.read()
    workdir = args.workdir or os.path.join(PREFIX, "runs", args.variant)
    zeebra = zeebra_answers(rows, args.zeebra_wall)
    print(json.dumps({"variant": args.variant, "build": build, "rows": len(rows),
                      "wall_cap_s": args.wall_cap, "rss_cap_bytes": RSS_CAP_BYTES}), flush=True)
    for r in rows:
        record = run_row(r, binary, workdir, zeebra, args.sympy_python, args.sympy_max_n,
                         args.wall_cap)
        record["variant"] = args.variant
        print(json.dumps(record), flush=True)


if __name__ == "__main__":
    main()
