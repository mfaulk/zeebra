"""Independent reference for #1165: SymPy's reduced Groebner basis over GF(p), one row per call.

Run with an interpreter that has SymPy (it is not a repository dependency):

    python3 -I tools/external/m5gb-paper/sympy_ref.py < row.json

Input: one instance line, `{"modulus", "variables", "system", "order"}` (`order` is `grevlex` or
`lex`, with the first variable largest). Output: `{"basis": [...]}` in Zeebra's syntax.
"""

import json
import sys

import sympy


def main():
    row = json.loads(sys.stdin.readline())
    p = row["modulus"]
    gens = sympy.symbols(row["variables"])
    local = {str(g): g for g in gens}
    system = [sympy.sympify(s.replace("^", "**"), locals=local) for s in row["system"]]
    system = [s for s in system if s != 0]
    if not system:
        print(json.dumps({"basis": [], "sympy": sympy.__version__}))
        return
    basis = sympy.groebner(system, *gens, modulus=p, order=row.get("order", "grevlex"))
    out = []
    for poly in basis.polys:
        terms = []
        for exps, coef in poly.terms():
            c = int(coef) % p
            factors = [
                str(g) if e == 1 else f"{g}^{e}" for g, e in zip(gens, exps) if e
            ]
            terms.append("*".join([str(c)] + factors))
        out.append(" + ".join(terms) if terms else "0")
    print(json.dumps({"basis": out, "sympy": sympy.__version__}))


if __name__ == "__main__":
    main()
