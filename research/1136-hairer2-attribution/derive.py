#!/usr/bin/env python3
"""#1136: derived presentations of sd-hairer-2@p31 and sd-butcher@p31, written as a catalog.

Each derived record generates the panel record's ideal, or (`*-substituted`) the ideal after its
linear generators eliminate variables. All keep the record's field and grevlex order. They are
attribution probes, not corpus records: they are not admitted to M34 and carry no lineage.

  python3 research/1136-hairer2-attribution/derive.py > research/1136-hairer2-attribution/derived.json
  python3 research/1136-hairer2-attribution/derive.py --development > .../development.json

`--development` writes T1's pairs instead (README): every eligible M34 development record at p31
and its homogenization, `<id>#h`.

Derived ids, under prefix `h2` (sd-hairer-2) and `bu` (sd-butcher):
  h2-orig          the panel record, unchanged (control)
  h2-reversed      generators in reverse order
  h2-substituted   each linear generator solved for its grevlex-leading variable and substituted
                   into the others, that variable dropped (hairer-2: 7 generators in 9 variables)
  h2-sub-reversed  h2-substituted, generators in reverse order
  h2-homogenized   each generator homogenized by a new variable `h`, placed last (smallest under
                   grevlex), so the basis dehomogenizes (h = 1) to a basis of the panel ideal
  h2-sub-homogenized  h2-substituted, homogenized the same way

The panel record already lists its generators by ascending degree, so `h2-reversed` is also the
degree-descending order.
"""
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
SOURCES = [("sd-hairer-2@p31", "h2"), ("sd-butcher@p31", "bu")]


CATALOGS = ["research/m34-public-corpus/catalog.json", "research/m34-structural-corpus/catalog.json"]
FITTED_FAMILY = "sd/runge-kutta-order-conditions"


def records():
    for path in CATALOGS:
        yield from json.loads((ROOT / path).read_text())


def load(record_id):
    for r in records():
        if r["id"] == record_id:
            return r
    raise SystemExit(f"no record {record_id}")


def development():
    """T1's pairs (README): each eligible development record and its homogenization `<id>#h`."""
    cohorts = json.loads((ROOT / "research/m34-gate-h/s0/cohorts.json").read_text())["assignments"]
    out = []
    for base in records():
        rid = base["id"]
        if cohorts.get(rid) != "development" or not rid.endswith("@p31"):
            continue
        polys = [to_poly(eq) for eq in base["equations"]]
        n = len(base["variables"])
        homogeneous = all(len({sum(e) for e in f}) == 1 for f in polys)
        if (homogeneous or n > 13 or base["order"] != "grevlex"
                or base["lineage"]["family_id"] == FITTED_FAMILY):
            continue
        every = range(n)
        out.append(record(base, rid, polys, every, base["normalized_input_digest"]))
        out.append(homogenized_record(base, f"{rid}#h", polys, every, f"{rid} homogenized"))
    return out


def to_poly(equation):
    return {tuple(t["exponents"]): int(t["coefficient"][0]) for t in equation}


def grevlex_key(e):
    """Larger key, larger monomial under grevlex: degree, then reversed exponents negated."""
    return (sum(e), tuple(-x for x in reversed(e)))


def mul(a, b, p):
    out = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = tuple(x + y for x, y in zip(ea, eb))
            out[e] = (out.get(e, 0) + ca * cb) % p
    return {e: c for e, c in out.items() if c}


def add(a, b, p):
    out = dict(a)
    for e, c in b.items():
        out[e] = (out.get(e, 0) + c) % p
    return {e: c for e, c in out.items() if c}


def substitute(poly, var, value, p):
    """`poly` with variable `var` replaced by the polynomial `value`."""
    n = len(next(iter(poly)))
    powers = {0: {tuple([0] * n): 1}}
    out = {}
    for e, c in poly.items():
        k = e[var]
        while k not in powers:
            j = max(powers)
            powers[j + 1] = mul(powers[j], value, p)
        rest = list(e)
        rest[var] = 0
        out = add(out, mul({tuple(rest): c}, powers[k], p), p)
    return out


def degree(f):
    return max(sum(e) for e in f)


def to_equation(poly, keep):
    terms = sorted(poly.items(), key=lambda t: grevlex_key(t[0]), reverse=True)
    return [{"coefficient": [str(c)], "exponents": [e[i] for i in keep]} for e, c in terms]


def record(base, rid, polys, keep, note):
    names = base["variables"] + ["h"]
    return {
        "schema": "corpus-instance-v1",
        "id": rid,
        "order": "grevlex",
        "field": base["field"],
        "variables": [names[i] for i in keep],
        "normalized_input_digest": f"#1136 derived: {note}",
        "equations": [to_equation(f, keep) for f in polys],
    }


def homogenize(f):
    d = degree(f)
    return {e + (d - sum(e),): c for e, c in f.items()}


def homogenized_record(base, rid, polys, keep, note):
    keep = list(keep) + [len(base["variables"])]
    return record(base, rid, [homogenize(f) for f in polys], keep, note)


def eliminate_linear(polys, p):
    """Solve each linear generator for its grevlex-leading variable and substitute it away."""
    rest, dropped = list(polys), []
    while True:
        linear = [f for f in rest if degree(f) == 1]
        if not linear:
            return rest, dropped
        f = linear[0]
        rest.remove(f)
        lead = max((e for e in f if sum(e) == 1), key=grevlex_key)
        var = lead.index(1)
        inv = pow(f[lead], p - 2, p)
        value = {e: (-c * inv) % p for e, c in f.items() if e != lead}
        rest = [g for g in (substitute(g, var, value, p) for g in rest) if g]
        dropped.append(var)


def derive(source, prefix):
    base = load(source)
    p = int(base["field"]["characteristic"])
    every = range(len(base["variables"]))
    polys = [to_poly(eq) for eq in base["equations"]]
    out = [
        record(base, f"{prefix}-orig", polys, every, f"{source} unchanged"),
        record(base, f"{prefix}-reversed", polys[::-1], every, "generators reversed"),
        homogenized_record(base, f"{prefix}-homogenized", polys, every, "homogenized by h, last"),
    ]
    rest, dropped = eliminate_linear(polys, p)
    if dropped:
        keep = [i for i in every if i not in dropped]
        assert all(e[i] == 0 for g in rest for e in g for i in dropped)
        names = [base["variables"][i] for i in dropped]
        out += [
            record(base, f"{prefix}-substituted", rest, keep, f"linear generators eliminated {names}"),
            record(base, f"{prefix}-sub-reversed", rest[::-1], keep, "substituted, reversed"),
            homogenized_record(base, f"{prefix}-sub-homogenized", rest, keep,
                               "substituted, homogenized by h, last"),
        ]
    return out


def main():
    if sys.argv[1:] == ["--development"]:
        out = development()
    else:
        out = [r for source, prefix in SOURCES for r in derive(source, prefix)]
    rows = ",\n".join(json.dumps(r, separators=(",", ":")) for r in out)
    sys.stdout.write("[\n" + rows + "\n]\n")


if __name__ == "__main__":
    main()
