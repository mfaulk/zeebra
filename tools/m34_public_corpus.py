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
from fractions import Fraction
from math import lcm
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import corpus_lineage  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
PANEL_DIR = ROOT / 'research' / 'm34-public-corpus'
PANEL = PANEL_DIR / 'panel.json'
INPUTS = PANEL_DIR / 'inputs.json'
CATALOG = PANEL_DIR / 'catalog.json'
REFERENCES = PANEL_DIR / 'references.json'
COMPOSITION = PANEL_DIR / 'composition.json'

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


def format_polynomial(terms, variables):
    """{exponents: int} -> text that parse_integer_polynomial reads back exactly."""
    parts = []
    for exponents, c in sorted(terms.items(), key=lambda kv: grevlex_key(kv[0]), reverse=True):
        if not c:
            continue
        factors = [v if e == 1 else f'{v}^{e}' for v, e in zip(variables, exponents) if e]
        body = '*'.join(([str(abs(c))] if abs(c) != 1 or not factors else []) + factors)
        parts.append(('-' if c < 0 else '+') + body)
    return ''.join(parts).lstrip('+') or '0'


def prime_factors(d):
    factors, q = set(), 2
    while q * q <= d:
        while d % q == 0:
            factors.add(q)
            d //= q
        q += 1
    return factors | ({d} if d > 1 else set())


def chandrasekhar_h(n, c):
    """Chandrasekhar's H-equation H(mu) = 1 + (c/2) mu H(mu) int_0^1 H(nu)/(mu+nu) dnu, collocated
    at mu_i = i/n with the n-point right-endpoint rule: 2n H_i - c H_i sum_j i/(i+j) H_j - 2n = 0,
    c = c[0]/c[1]. Each row is scaled by the lcm of its denominators, which is exact over Q."""
    albedo = Fraction(*c)
    variables = [f'H{i}' for i in range(1, n + 1)]

    def mono(*indices):
        return tuple(sum(1 for k in indices if k == v) for v in range(n))

    equations, denominators = [], set()
    for i in range(1, n + 1):
        row = {mono(i - 1): Fraction(2 * n), mono(): Fraction(-2 * n)}
        for j in range(1, n + 1):
            key = mono(i - 1, j - 1)
            row[key] = row.get(key, 0) - albedo * Fraction(i, i + j)
        scale = lcm(*(v.denominator for v in row.values()))
        denominators.add(scale)
        equations.append(format_polynomial({k: int(v * scale) for k, v in row.items()}, variables))
    excluded = sorted(set().union(*map(prime_factors, denominators)))
    return dict(variables=variables, equations=equations, excluded_primes=excluded, transformations=[
        dict(kind='parameter-specialization', description=f'albedo c = {albedo}; nodes mu_i = i/n, n = {n}'),
        dict(kind='clear-denominators',
             description=f'each equation scaled by the lcm of its denominators; primes {excluded} excluded')])


def multisite_phosphorylation(n, nonzero=False):
    """Steady states of the n-site sequential distributive phosphorylation network (Wang & Sontag,
    J. Math. Biol. 57 (2008) 29-52) under mass action: S_i + E <-> ES_i -> S_{i+1} + E and
    S_{i+1} + F <-> FS_{i+1} -> S_i + F. Equations are the ODE right-hand sides of every complex and
    of S_0..S_{n-1}; the dependent S_n, E and F rows are replaced by the three conservation laws."""
    S = [f'S{i}' for i in range(n + 1)]
    C = [f'ES{i}' for i in range(n)]
    D = [f'FS{i}' for i in range(1, n + 1)]
    variables = S + ['E', 'F'] + C + D
    at = {v: k for k, v in enumerate(variables)}

    def mono(*names):
        e = [0] * len(variables)
        for name in names:
            e[at[name]] += 1
        return tuple(e)

    rhs = {v: {} for v in variables}

    def react(rate, reactants, products):
        for v, sign in [(v, -1) for v in reactants] + [(v, 1) for v in products]:
            rhs[v][mono(*reactants)] = rhs[v].get(mono(*reactants), 0) + sign * rate

    for i in range(n):
        react(i + 2, (S[i], 'E'), (C[i],))
        react(1, (C[i],), (S[i], 'E'))
        react(i + 1, (C[i],), (S[i + 1], 'E'))
        react(i + 1, (S[i + 1], 'F'), (D[i],))
        react(2, (D[i],), (S[i + 1], 'F'))
        react(i + 3, (D[i],), (S[i], 'F'))
    totals = dict(E=7, F=11, S=10 * n + 3)
    conservation = []
    for group, total in ((['E'] + C, totals['E']), (['F'] + D, totals['F']), (S + C + D, totals['S'])):
        law = {mono(v): 1 for v in group}
        law[mono()] = -total
        conservation.append(law)
    equations = [format_polynomial(rhs[v], variables) for v in C + D + S[:-1]]
    equations += [format_polynomial(law, variables) for law in conservation]
    transformations = [dict(kind='parameter-specialization', description=(
        f'n = {n}; site i rates (a, b, c, alpha, beta, gamma) = (i+2, 1, i+1, i+1, 2, i+3); '
        f'totals E = {totals["E"]}, F = {totals["F"]}, S = {totals["S"]}'))]
    if nonzero:
        variables = variables + ['t']
        equations = equations + ['t*' + '*'.join(['E', 'F'] + S) + '-1']
        transformations.append(dict(kind='rabinowitsch-augmentation', description=(
            'adds t*E*F*S0*...*Sn - 1 (free species nonzero). T-GB is the basis of the augmented ideal '
            'in k[species, t], not the saturation I : (E*F*S0*...*Sn)^infinity')))
    return dict(variables=variables, equations=equations, excluded_primes=[], transformations=transformations)


GENERATORS = {'chandrasekhar-h': chandrasekhar_h, 'multisite-phosphorylation': multisite_phosphorylation}


def problem_entry(problem, panel, inputs):
    """The frozen upstream entry, or the generated one carrying its source's citation and licence."""
    if 'generator' not in problem:
        return inputs[problem['source_entry']]
    source = panel['sources'][problem['source']]
    entry = GENERATORS[problem['generator']](**problem['generator_parameters'])
    return dict(entry, url=source['url'], revision=source['revision'], license=source['license'])


def composition(panel, references):
    """Per-family base problems, scales (distinct n) and frontier rows: #1006's side of the §8.2 read."""
    families = {}
    for problem in panel['problems']:
        family = families.setdefault(problem['family_id'], dict(
            base_problems=0, scales=set(), sources=set(), frontier={'p31': 0, 'p64': 0}))
        family['base_problems'] += 1
        family['scales'].add(problem['family_parameters']['n'])
        family['sources'].add(problem['source_id'])
        for field in family['frontier']:
            if references.get(f'{problem["id"]}@{field}', {}).get('status') == 'frontier':
                family['frontier'][field] += 1
    for family in families.values():
        family.update(scales=sorted(family['scales']), sources=sorted(family['sources']),
                      multi_scale=len(family['scales']) > 1)
    return dict(schema='m34-public-composition-v1', base_problems=len(panel['problems']),
                families=dict(sorted(families.items())))


def dump_composition(panel):
    references = json.loads(REFERENCES.read_text())['references'] if REFERENCES.exists() else {}
    summary = composition(panel, references)
    rows = ',\n'.join(f'  {json.dumps(k)}: {json.dumps(v)}' for k, v in summary['families'].items())
    return (f'{{"schema": {json.dumps(summary["schema"])}, "base_problems": {summary["base_problems"]},\n'
            f' "families": {{\n{rows}\n }}}}\n')


def reduce_record(problem, entry, field_name, p):
    variables = entry['variables']
    if any(p % q == 0 for q in entry.get('excluded_primes', [])):
        raise ValueError(f'{problem["id"]}: {p} divides a cleared denominator')
    equations, vanished = [], 0
    for text in entry['equations']:
        polynomial = parse_integer_polynomial(text, variables)
        reduced = {k: c % p for k, c in polynomial.items()}
        vanished += sum(1 for c in reduced.values() if c == 0)
        equations.append([{'exponents': list(k), 'coefficient': [str(c)]}
                          for k, c in sorted(reduced.items()) if c])
    transformations = list(entry.get('transformations', [])) + [{'kind': 'prime-reduction',
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
        entry = problem_entry(problem, panel, inputs)
        for field_name, p in panel['fields'].items():
            records.append(reduce_record(problem, entry, field_name, int(p)))
    return records


def dump_catalog(records):
    return '[\n' + ',\n'.join(json.dumps(r, sort_keys=True, separators=(',', ':')) for r in records) + '\n]\n'


def import_inputs(panel, checkout):
    source = panel['sources']['symbolicdata']
    inputs = {}
    for problem in panel['problems']:
        name = problem.get('source_entry')
        if name is None or name in inputs:
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
    ref.add_argument('--missing', action='store_true',
                     help='keep committed rows whose input digest is unchanged; run only the others')
    args = parser.parse_args()

    panel = json.loads(PANEL.read_text())
    if args.command == 'import':
        INPUTS.write_text(json.dumps(import_inputs(panel, args.checkout), indent=1) + '\n')
        return 0
    inputs = json.loads(INPUTS.read_text())
    records = build_catalog(panel, inputs)
    summary = dump_composition(panel)
    if args.command == 'catalog':
        CATALOG.write_text(dump_catalog(records))
        COMPOSITION.write_text(summary)
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
        if not COMPOSITION.exists() or COMPOSITION.read_text() != summary:
            print('composition.json is stale: run tools/m34_public_corpus.py catalog', file=sys.stderr)
            return 1
        print(f'ok: {len(panel["problems"])} base problems, {len(records)} records')
        return 0
    entries = {p['id']: problem_entry(p, panel, inputs) for p in panel['problems']}

    def reference(record):
        if int(record['field']['characteristic']) < 2 ** 31:
            return singular_reference(record, entries[record['id'].split('@')[0]], args.singular, args.timeout)
        return grobx_reference(record, args.grobx, args.grobx_timeout)

    # --missing keeps every committed row whose input digest is unchanged and runs only the rest.
    kept = json.loads(REFERENCES.read_text())['references'] if args.missing and REFERENCES.exists() else {}
    kept = {r['id']: kept[r['id']] for r in records
            if kept.get(r['id'], {}).get('normalized_input_digest') == r['normalized_input_digest']}
    todo = [r for r in records if r['id'] not in kept]
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        references = dict(kept, **{r['id']: dict(res, normalized_input_digest=r['normalized_input_digest'])
                                   for r, res in zip(todo, pool.map(reference, todo))})
    REFERENCES.write_text(json.dumps({
        'schema': 'm34-public-reference-v2',
        'oracles': {'singular': {'version': singular_version(args.singular), 'timeout_seconds': args.timeout},
                    'grobx-certified': {'version': grobx_version(args.grobx),
                                        'timeout_seconds': args.grobx_timeout}},
        'references': references}, indent=1, sort_keys=True) + '\n')
    COMPOSITION.write_text(dump_composition(panel))
    return 0


if __name__ == '__main__':
    sys.exit(main())
