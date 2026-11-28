#!/usr/bin/env python3
"""#1080's frozen admission predicate for certified zero skipping, evaluated on corpus records.

    predicate.py RECORD.json [...]

Admits a system when all of these hold:
- square: as many generators as variables (m = n);
- homogeneous in degree: every generator has the same total degree d;
- dense: mean support density >= 0.5, where a generator's density is its term count over the
  number of monomials of total degree <= d in n variables.

Prints one JSON line per record with the features and the verdict. The rule was frozen from the
development sweep (bench-job f9874321f431) before any held-out row was generated.
"""
import json
import sys
from math import comb

DENSITY = 0.5
SLACK = 2


def features(record):
    n = len(record['variables'])
    eqs = record['equations']
    degrees = [max(sum(t['exponents']) for t in eq) for eq in eqs]
    density = sum(len(eq) / comb(n + d, d) for eq, d in zip(eqs, degrees)) / len(eqs)
    return dict(n=n, m=len(eqs), degrees=sorted(set(degrees)), density=round(density, 4))


def admits(f):
    return f['m'] == f['n'] and len(f['degrees']) == 1 and f['density'] >= DENSITY


def main():
    for path in sys.argv[1:]:
        for record in json.load(open(path)):
            f = features(record)
            print(json.dumps(dict(id=record['id'], **f, admitted=admits(f),
                                  hilbert=f'certified-zeros+{SLACK}' if admits(f) else 'off')))


if __name__ == '__main__':
    main()
