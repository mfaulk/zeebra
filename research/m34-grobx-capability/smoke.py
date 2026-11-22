#!/usr/bin/env python3
"""#1029: one tiny instance per grobx capability cell, through tools/external/grobx-driver.

    python3 research/m34-grobx-capability/smoke.py DRIVER > research/m34-grobx-capability/smoke.jsonl

Capability, not timing: no duration is written. Each line is one (cell, mode) attempt with the
driver's identity, `ok` / `refused` / `stopped`, the checker's verdict, a basis digest and the
engine route the call report names.
"""
import hashlib
import json
import subprocess
import sys
import tempfile

KATSURA3 = ['x+2*y+2*z-1', 'x^2+2*y^2+2*z^2-x', '2*x*y+2*y*z-y']
CELLS = [
    # (cell, field, order, workers, forced mode, variables, modulus, generators)
    ('gf2', 'GF(2)', 'grevlex', 1, None, ['x', 'y', 'z'], 2, ['x*y+z', 'y*z+x', 'x*z+y+1']),
    ('gf3', 'GF(3)', 'grevlex', 1, None, ['x', 'y', 'z'], 3, KATSURA3),
    ('p32003', 'p < 2^31', 'grevlex', 1, None, ['x', 'y', 'z'], 32003, KATSURA3),
    ('p2^31-1', 'p < 2^31', 'grevlex', 1, None, ['x', 'y', 'z'], 2147483647, KATSURA3),
    ('p2^32+15', '2^31 <= p < 2^64', 'grevlex', 1, None, ['x', 'y', 'z'], 4294967311, KATSURA3),
    ('p2^64-59', '2^31 <= p < 2^64', 'grevlex', 1, None, ['x', 'y', 'z'], 18446744073709551557,
     KATSURA3),
    ('lex-zero-dim', 'p < 2^31', 'lex', 1, None, ['x', 'y', 'z'], 32003, KATSURA3),
    ('lex-positive-dim', 'p < 2^31', 'lex', 1, None, ['x', 'y', 'z'], 32003, ['x*y-z', 'y*z-x']),
    ('lex-wide', '2^31 <= p < 2^64', 'lex', 1, None, ['x', 'y', 'z'], 18446744073709551557,
     KATSURA3),
    ('nonradical', 'p < 2^31', 'grevlex', 1, None, ['x', 'y'], 32003, ['x^2', 'x*y', 'y^3']),
    ('unit-ideal', 'p < 2^31', 'grevlex', 1, None, ['x', 'y'], 32003, ['x', 'x-1']),
    # Cells the driver is expected to refuse with a typed error.
    ('deglex', 'p < 2^31', 'deglex', 1, None, ['x', 'y', 'z'], 32003, KATSURA3),
    ('block', 'p < 2^31', 'block:1', 1, None, ['x', 'y', 'z'], 32003, KATSURA3),
    ('workers-16', 'p < 2^31', 'grevlex', 16, None, ['x', 'y', 'z'], 32003, KATSURA3),
    ('cheap', 'p < 2^31', 'grevlex', 1, 'cheap', ['x', 'y', 'z'], 32003, KATSURA3),
    ('gf4-as-modulus', 'GF(2^2) (no extension fields)', 'grevlex', 1, None, ['x', 'y'], 4,
     ['x^2+x+1', 'y^2+y']),
    ('rationals', 'Q (modulus 0)', 'grevlex', 1, None, ['x', 'y'], 0, ['x^2-2', 'y-x']),
]


def report_route(report):
    """The field kernel, every run's engine and order, and each handover, from the call report."""
    if not report:
        return None
    route = {'runs': [], 'handovers': 0}
    for line in report.splitlines():
        parts = line.split(' ')
        if len(parts) < 2:
            continue
        kind, fields = parts[1], dict(p.split('=', 1) for p in parts[2:] if '=' in p)
        if kind == 'read':
            route['field'] = fields.get('field')
        elif kind == 'run':
            route['runs'].append({k: fields.get(k) for k in
                                  ('engine', 'order', 'reduce', 'cofactors', 'why')})
        elif kind == 'handover' and fields.get('verdict') not in (None, 'stay'):
            route['handovers'] += 1
        elif kind in ('fglm', 'change', 'lex'):
            route.setdefault('lex', []).append(kind)
    return route


def run(driver, cell, mode):
    name, field, order, workers, forced, variables, modulus, generators = cell
    request = {'variables': variables, 'modulus': modulus, 'order': order, 'workers': workers,
               'mode': forced or mode, 'wall_ns': 10_000_000_000, 'rss_bytes': 1 << 30,
               'generators': generators}
    with tempfile.NamedTemporaryFile('w', suffix='.json') as f:
        json.dump(request, f)
        f.flush()
        done = subprocess.run([driver, f.name], capture_output=True, text=True, timeout=60)
    row = {'cell': name, 'field': field, 'order': order, 'workers': workers,
           'mode': request['mode'], 'modulus': modulus}
    if done.returncode != 0:
        row.update(status='refused', error=done.stderr.strip().splitlines()[-1][:200])
        return row
    out = json.loads(done.stdout)
    basis = out.get('basis')
    row.update(
        status='stopped' if out.get('stopped') else 'ok',
        stopped=out.get('stopped'),
        certified=out.get('certified'),
        flaw=out.get('flaw'),
        basis_sha256=hashlib.sha256(basis.encode()).hexdigest()[:16] if basis else None,
        basis_elements=basis.count(',') + 1 if basis and basis.strip() != '[]:' else 0,
        route=report_route(out.get('report')),
        revision=out['revision'][:8],
        version=out['version'],
    )
    return row


def main():
    driver = sys.argv[1]
    identity = json.loads(subprocess.run([driver, '--version'], capture_output=True, text=True,
                                         check=True).stdout)
    print(json.dumps({'identity': identity}))
    for cell in CELLS:
        modes = [cell[4]] if cell[4] else ['raw', 'certified']
        for mode in modes:
            print(json.dumps(run(driver, cell, mode)), flush=True)


if __name__ == '__main__':
    main()
