#!/usr/bin/env python3
"""#1006 public application panel: import, catalog and reference tool.

`import` is the only step that reads the pinned upstream checkout; it freezes the exact integer
equations into inputs.json. `catalog` and `check` derive corpus-instance-v1 records from that file
alone, so CI reproduces the catalog without network access. `references` shells out to Singular as
an oracle subprocess and records digests, never basis text.
"""
import argparse
import concurrent.futures
import hashlib
import json
import re
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import corpus_lineage  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
PANEL_DIR = ROOT / 'research' / 'm34-public-corpus'
PANEL = PANEL_DIR / 'panel.json'
INPUTS = PANEL_DIR / 'inputs.json'
CATALOG = PANEL_DIR / 'catalog.json'
REFERENCES = PANEL_DIR / 'references.json'

TERM = re.compile(r'([+-]?)([^+-]+)')
FACTOR = re.compile(r'^([A-Za-z_][A-Za-z_0-9]*)(?:\^(\d+))?$')


def parse_integer_polynomial(text, variables):
    """Exact integer polynomial in SymbolicData's `c*x^e*y` syntax -> {exponents: int}."""
    index = {v: i for i, v in enumerate(variables)}
    compact = re.sub(r'\s+', '', text)
    if not compact or re.search(r'[^0-9A-Za-z_*^+-]', compact):
        raise ValueError(f'unsupported polynomial syntax: {text[:60]!r}')
    terms = {}
    position = 0
    for match in TERM.finditer(compact):
        if match.start() != position:
            raise ValueError(f'malformed term near {compact[position:position + 20]!r}')
        position = match.end()
        coefficient = -1 if match.group(1) == '-' else 1
        exponents = [0] * len(variables)
        for factor in match.group(2).split('*'):
            if factor.isdigit():
                coefficient *= int(factor)
                continue
            parsed = FACTOR.match(factor)
            if not parsed or parsed.group(1) not in index:
                raise ValueError(f'unknown factor {factor!r}')
            exponents[index[parsed.group(1)]] += int(parsed.group(2) or 1)
        key = tuple(exponents)
        terms[key] = terms.get(key, 0) + coefficient
    if position != len(compact):
        raise ValueError(f'trailing text {compact[position:]!r}')
    return {k: c for k, c in terms.items() if c}


def reduce_record(problem, entry, field_name, p):
    variables = entry['variables']
    equations, vanished = [], 0
    for text in entry['equations']:
        polynomial = parse_integer_polynomial(text, variables)
        reduced = {k: c % p for k, c in polynomial.items()}
        vanished += sum(1 for c in reduced.values() if c == 0)
        equations.append([{'exponents': list(k), 'coefficient': [str(c)]}
                          for k, c in sorted(reduced.items()) if c])
    transformations = [{'kind': 'prime-reduction',
                        'description': f'integer coefficients reduced modulo {p}'}]
    if vanished:
        transformations.append({'kind': 'exceptional-reduction',
                                'description': f'{vanished} coefficients vanish modulo {p}'})
    record = {
        'schema': 'corpus-instance-v1',
        'id': f'{problem["id"]}@{field_name}',
        'field': {'characteristic': str(p), 'extension_degree': 1, 'defining_polynomial': []},
        'variables': variables,
        'order': 'grevlex',
        'task': 'T-GB',
        'equations': equations,
        'generator': None,
        'source': {'url': entry['url'], 'revision': entry['revision'], 'license': entry['license']},
        'transformations': transformations,
        'lineage': {
            'support_id': None,
            'formulation_id': problem['formulation_id'],
            'family_id': problem['family_id'],
            'source_id': problem['source_id'],
            'presentation_parent': (f'{problem["presentation_parent"]}@{field_name}'
                                    if problem.get('presentation_parent') else None),
            'family_parameters': problem['family_parameters'],
        },
    }
    # Field twins share a support id only when reduction removed no term; otherwise the computed
    # support is the honest identity (corpus-lineage.md, support_id rule).
    record['lineage']['support_id'] = corpus_lineage.support_digest(record)
    record['normalized_input_digest'] = corpus_lineage.input_digest(record)
    return record


def build_catalog(panel, inputs):
    records = []
    for problem in panel['problems']:
        entry = inputs[problem['source_entry']]
        for field_name, p in panel['fields'].items():
            records.append(reduce_record(problem, entry, field_name, int(p)))
    return records


def dump_catalog(records):
    return '[\n' + ',\n'.join(json.dumps(r, sort_keys=True, separators=(',', ':')) for r in records) + '\n]\n'


def import_inputs(panel, checkout):
    source = panel['sources']['symbolicdata']
    inputs = {}
    for problem in panel['problems']:
        name = problem['source_entry']
        if name in inputs:
            continue
        path = Path(checkout) / source['path'] / f'{name}.xml'
        raw = path.read_bytes()
        tree = ET.fromstring(raw)
        variables = [v.strip() for v in tree.findtext('vars').split(',')]
        equations = [p.text.strip() for p in tree.find('basis')]
        for text in equations:
            parse_integer_polynomial(text, variables)
        inputs[name] = {
            'url': f'{source["url"]}/blob/{source["revision"]}/{source["path"]}/{name}.xml',
            'revision': source['revision'],
            'license': source['license'],
            'file_sha256': hashlib.sha256(raw).hexdigest(),
            'variables': variables,
            'equations': equations,
        }
    return dict(sorted(inputs.items()))


def grevlex_key(exponents):
    return sum(exponents), tuple(-e for e in reversed(exponents))


def basis_digest(record, basis):
    """reduced-basis-v1 over the record's field: each generator monic at its grevlex leading term,
    so two oracles that print the same reduced basis with different scalars or order agree."""
    p = int(record['field']['characteristic'])
    normalized = []
    for polynomial in basis:
        terms = {k: c % p for k, c in polynomial.items() if c % p}
        scale = pow(terms[max(terms, key=grevlex_key)], -1, p)
        normalized.append([[list(k), [str(c * scale % p)]] for k, c in sorted(terms.items())])
    return corpus_lineage.sha({'format': 'reduced-basis-v1', 'field': record['field'],
                               'variables': record['variables'], 'order': record['order'],
                               'basis': sorted(normalized, key=corpus_lineage.encoded)})


def leading_exponents(basis):
    return [max((k for k, c in b.items() if c), key=grevlex_key) for b in basis]


def staircase_size(leading):
    """Number of standard monomials of the leading-term ideal, or None when it is infinite."""
    n = len(leading[0]) if leading else 0
    if any(not any(m) for m in leading):
        return 0
    pure = {next(i for i, e in enumerate(m) if e) for m in leading if sum(1 for e in m if e) == 1}
    if len(pure) < n:
        return None
    count, stack = 0, [((0,) * n, 0)]
    while stack:
        monomial, start = stack.pop()
        if any(all(a >= b for a, b in zip(monomial, m)) for m in leading):
            continue
        count += 1
        for i in range(start, n):
            stack.append((monomial[:i] + (monomial[i] + 1,) + monomial[i + 1:], i))
    return count


def generator_texts(record):
    def monomial(exponents, coefficient):
        factors = [] if coefficient == '1' and any(exponents) else [coefficient]
        factors += [v if e == 1 else f'{v}^{e}' for v, e in zip(record['variables'], exponents) if e]
        return '*'.join(factors)
    return ['+'.join(monomial(t['exponents'], t['coefficient'][0]) for t in equation) or '0'
            for equation in record['equations']]


def parse_grobx_basis(text, variables):
    body = text.strip().rstrip(':').strip().removeprefix('[').removesuffix(']')
    return [parse_integer_polynomial(t, variables) for t in body.split(',') if t.strip()]


def grobx_reference(record, binary, timeout):
    request = dict(variables=record['variables'], modulus=int(record['field']['characteristic']),
                   order='grevlex', workers=1, generators=generator_texts(record), mode='certified',
                   wall_ns=int(timeout * 1e9), rss_bytes=32 * 2 ** 30)
    with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False) as handle:
        json.dump(request, handle)
    try:
        run = subprocess.run([binary, handle.name], capture_output=True, text=True, timeout=timeout + 60)
    except subprocess.TimeoutExpired:
        return {'status': 'frontier', 'oracle': 'grobx-certified', 'reason': f'grobx exceeded {timeout} s'}
    finally:
        Path(handle.name).unlink()
    reply = json.loads(run.stdout) if run.returncode == 0 and run.stdout.strip() else {}
    if reply.get('stopped'):
        return {'status': 'frontier', 'oracle': 'grobx-certified', 'reason': f'grobx stopped: {reply["stopped"]}'}
    if not reply.get('certified') or reply.get('flaw'):
        return {'status': 'error', 'oracle': 'grobx-certified',
                'reason': str(reply.get('flaw') or run.stderr.strip()[-200:])}
    basis = parse_grobx_basis(reply['basis'], record['variables'])
    vdim = staircase_size(leading_exponents(basis))
    return {'status': 'reference', 'oracle': 'grobx-certified', 'zero_dimensional': bool(vdim),
            'vdim': vdim, 'basis_size': len(basis), 'reduced_basis_digest': basis_digest(record, basis)}


SINGULAR = '''option(redSB); option(redTail);
ring r = {p},({vars}),dp; short = 0;
ideal i = {eqs};
ideal g = simplify(std(i), 1);
int k; int n = size(g);
print("BEGIN"); print(dim(g)); print(vdim(g)); print(n);
for (k = 1; k <= n; k++) {{ print(string(g[k])); }}
print("END"); quit;
'''


def singular_reference(record, entry, singular, timeout):
    p = int(record['field']['characteristic'])
    script = SINGULAR.format(p=p, vars=','.join(entry['variables']), eqs=',\n'.join(entry['equations']))
    with tempfile.NamedTemporaryFile('w', suffix='.sing', delete=False) as handle:
        handle.write(script)
    try:
        out = subprocess.run([singular, '-q', '--no-rc', '--no-warn', handle.name], capture_output=True,
                             text=True, timeout=timeout).stdout
    except subprocess.TimeoutExpired:
        return {'status': 'frontier', 'oracle': 'singular', 'reason': f'Singular std exceeded {timeout} s'}
    finally:
        Path(handle.name).unlink()
    lines = out.split('BEGIN\n', 1)[-1].split('\nEND', 1)[0].split('\n')
    if len(lines) < 3 or 'END' not in out:
        return {'status': 'error', 'oracle': 'singular', 'reason': out.strip()[-200:]}
    dim, vdim, size = (int(x) for x in lines[:3])
    try:
        basis = [parse_integer_polynomial(t, entry['variables']) for t in lines[3:3 + size]]
    except ValueError as error:
        return {'status': 'error', 'oracle': 'singular', 'reason': str(error)}
    return {'status': 'reference', 'oracle': 'singular', 'dimension': dim, 'vdim': vdim if dim <= 0 else None,
            'basis_size': size, 'reduced_basis_digest': basis_digest(record, basis)}


def singular_version(singular):
    out = subprocess.run([singular, '-q', '--no-rc', '-c', 'print(system("version")); quit;'],
                         capture_output=True, text=True).stdout.strip()
    return f'Singular build {out}'


def grobx_version(binary):
    out = subprocess.run([binary, '--version'], capture_output=True, text=True).stdout
    try:
        meta = json.loads(out)
    except json.JSONDecodeError:
        return out.strip()[:200]
    return {k: meta[k] for k in ('version', 'revision') if k in meta} or out.strip()[:200]


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    sub = parser.add_subparsers(dest='command', required=True)
    imp = sub.add_parser('import', help='freeze exact upstream equations into inputs.json')
    imp.add_argument('checkout', help='SymbolicData data checkout at the pinned revision')
    sub.add_parser('catalog', help='regenerate catalog.json from inputs.json')
    sub.add_parser('check', help='verify catalog.json is current and every record validates')
    ref = sub.add_parser('references', help='compute reference digests: Singular below 2^31, '
                                            'certified grobx above')
    ref.add_argument('--singular', default='Singular')
    ref.add_argument('--grobx', default='/buildcache/cargo-target/zeebra-bench-m34/grobx-8005a2a1/release/grobx-driver',
                     help='pinned grobx-driver (tools/external/grobx-driver)')
    ref.add_argument('--timeout', type=float, default=120.0, help='Singular wall limit per record')
    ref.add_argument('--grobx-timeout', type=float, default=300.0, help='grobx wall limit per record')
    ref.add_argument('--jobs', type=int, default=8)
    args = parser.parse_args()

    panel = json.loads(PANEL.read_text())
    if args.command == 'import':
        INPUTS.write_text(json.dumps(import_inputs(panel, args.checkout), indent=1) + '\n')
        return 0
    inputs = json.loads(INPUTS.read_text())
    records = build_catalog(panel, inputs)
    if args.command == 'catalog':
        CATALOG.write_text(dump_catalog(records))
        return 0
    if args.command == 'check':
        for record in records:
            corpus_lineage.validate_record(record)
        if CATALOG.read_text() != dump_catalog(records):
            print('catalog.json is stale: run tools/m34_public_corpus.py catalog', file=sys.stderr)
            return 1
        known = {r['id'] for r in records}
        stale = sorted(set(json.loads(REFERENCES.read_text())['references']) - known) \
            if REFERENCES.exists() else []
        if stale:
            print(f'references.json names unknown records: {stale}', file=sys.stderr)
            return 1
        print(f'ok: {len(panel["problems"])} base problems, {len(records)} records')
        return 0
    entries = {p['id']: inputs[p['source_entry']] for p in panel['problems']}

    def reference(record):
        if int(record['field']['characteristic']) < 2 ** 31:
            return singular_reference(record, entries[record['id'].split('@')[0]], args.singular, args.timeout)
        return grobx_reference(record, args.grobx, args.grobx_timeout)

    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        references = {r['id']: dict(res, normalized_input_digest=r['normalized_input_digest'])
                      for r, res in zip(records, pool.map(reference, records))}
    REFERENCES.write_text(json.dumps({
        'schema': 'm34-public-reference-v2',
        'oracles': {'singular': {'version': singular_version(args.singular), 'timeout_seconds': args.timeout},
                    'grobx-certified': {'version': grobx_version(args.grobx),
                                        'timeout_seconds': args.grobx_timeout}},
        'references': references}, indent=1, sort_keys=True) + '\n')
    return 0


if __name__ == '__main__':
    sys.exit(main())
