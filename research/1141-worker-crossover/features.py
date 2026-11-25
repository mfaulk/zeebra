#!/usr/bin/env python3
"""Pre-solve features of generated rows, read from `sig_f4_study --input-only`: the fields of
`DispatchFeatures` (#1141) plus the counts the candidate rules were drawn from. No solve is run.

    features.py --sig <sig_f4_study> <field/name> ...
"""
import argparse
import json
import re
import subprocess
from math import comb


def monomials(n, d):
    return comb(n + d, d)


def features(sig, row):
    field, name = row.split('/')
    out = subprocess.run([sig, '--field', field, '--name', name, '--generate', '--engine', 'f4',
                          '--input-only'], check=True, capture_output=True, text=True).stdout
    data = json.loads(out)
    used, covered = set(), set()
    terms = quad_terms = quad_gens = 0
    degrees = []
    for g in data['generators']:
        mons = []
        for t in re.split(r'(?<!\^)[+-]', g.replace(' ', '')):
            if not t:
                continue
            exps = {}
            for f in t.split('*'):
                m = re.fullmatch(r'x(\d+)(?:\^(\d+))?', f)
                if m:
                    exps[int(m[1])] = exps.get(int(m[1]), 0) + int(m[2] or 1)
            mons.append(exps)
        deg = max(sum(e.values()) for e in mons)
        degrees.append(deg)
        terms += len(mons)
        quad_gens += deg == 2
        for e in mons:
            used |= set(e)
            quad_terms += sum(e.values()) == 2
            if len(e) == 1 and sum(e.values()) == deg:
                covered |= set(e)
            if not e and deg == 0:
                covered |= set(range(1, 100))
    n = len(used)
    mon = sum(monomials(n, d) for d in degrees)
    uncovered = sorted(used - covered)
    return dict(row=row, digest=data['digest'], variables=n, generators=len(degrees),
                quadratic_generators=quad_gens, max_degree=max(degrees), terms=terms,
                quadratic_terms=quad_terms, monomials=mon, density=round(terms / mon, 4),
                witness=f'x{uncovered[0]}' if uncovered else None, uncovered=len(uncovered))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--sig', required=True)
    p.add_argument('rows', nargs='+')
    for row in p.parse_args().rows:
        print(json.dumps(features(p.parse_args().sig, row)))


if __name__ == '__main__':
    main()
