#!/usr/bin/env python3
"""#1007 controlled structural families: generators, catalog and references.

Every generator builds an exact integer system from a SHA-256 counter stream keyed by the problem's
family, parameters and seed, so the equations depend on nothing but this file. The integer system is
then reduced at each panel prime; field twins are one formulation (plan §8.2). The written
specification, including what is and is not known about each ideal, is
research/m34-structural-corpus/README.md.
"""
import argparse
import concurrent.futures
import hashlib
import itertools
import json
import math
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import corpus_lineage  # noqa: E402
import m34_public_corpus as oracle  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
PANEL_DIR = ROOT / 'research' / 'm34-structural-corpus'
CATALOG = PANEL_DIR / 'catalog.json'
REFERENCES = PANEL_DIR / 'references.json'
FIELDS = {'p31': 2 ** 31 - 1, 'p64': 2 ** 64 - 59}
REPOSITORY = 'https://github.com/mfaulk/zeebra'
# The main commit that introduced these generators. Records cite it as their recipe revision; the
# CI check regenerates the catalog from the current file, so a generator change shows up as a diff.
GENERATOR_REVISION = 'd35b7639f8d4287878b7129c94ff5d32b7cc65a1'
PATH = 'tools/m34_structural_corpus.py'
COEFFICIENT_BOUND = 2 ** 15


class Rng:
    """Deterministic draws: SHA-256 of (label, counter), rejection-sampled, so no library version
    or platform can change an instance."""

    def __init__(self, *label):
        self.label, self.counter = json.dumps(label, sort_keys=True, separators=(',', ':')), 0

    def below(self, n):
        bound = 2 ** 64 - 2 ** 64 % n
        while True:
            digest = hashlib.sha256(f'{self.label}#{self.counter}'.encode()).digest()
            self.counter += 1
            value = int.from_bytes(digest[:8], 'big')
            if value < bound:
                return value % n

    def integer(self, low, high):
        return low + self.below(high - low + 1)

    def coefficient(self):
        """Uniform over the nonzero integers in [-COEFFICIENT_BOUND, COEFFICIENT_BOUND]."""
        value = self.below(2 * COEFFICIENT_BOUND) - COEFFICIENT_BOUND
        return value if value < 0 else value + 1

    def sample(self, items, k):
        items = list(items)
        for i in range(k):
            j = i + self.below(len(items) - i)
            items[i], items[j] = items[j], items[i]
        return items[:k]


# Polynomials are {exponent tuple: nonzero int}.

def unit(n, *indices):
    exponents = [0] * n
    for i in indices:
        exponents[i] += 1
    return tuple(exponents)


def add(a, b, scale=1):
    out = dict(a)
    for k, c in b.items():
        out[k] = out.get(k, 0) + scale * c
    return {k: c for k, c in out.items() if c}


def mul(a, b):
    out = {}
    for (ka, ca), (kb, cb) in itertools.product(a.items(), b.items()):
        k = tuple(x + y for x, y in zip(ka, kb))
        out[k] = out.get(k, 0) + ca * cb
    return {k: c for k, c in out.items() if c}


def power(a, e, n):
    out = {(0,) * n: 1}
    for _ in range(e):
        out = mul(out, a)
    return out


def evaluate(f, point):
    return sum(c * math.prod(v ** e for v, e in zip(point, k)) for k, c in f.items())


def substitute(f, forms, n):
    """f(forms[0], …, forms[n-1]) with each form a polynomial."""
    out, cache = {}, {}
    for k, c in f.items():
        term = {(0,) * n: c}
        for i, e in enumerate(k):
            if e:
                if (i, e) not in cache:
                    cache[i, e] = power(forms[i], e, n)
                term = mul(term, cache[i, e])
        out = add(out, term)
    return out


def monomials(n, among, low, high):
    """Exponent tuples over the variables `among` with total degree in [low, high]."""
    out = []
    for degree in range(low, high + 1):
        for combo in itertools.combinations_with_replacement(among, degree):
            out.append(unit(n, *combo))
    return out


def random_poly(rng, support):
    return {k: rng.coefficient() for k in support}


def unit_triangular_product(rng, n):
    """L·U with unit diagonals and entries in [-3, 3]: determinant 1, so invertible at every prime."""
    lower = [[1 if i == j else (rng.integer(-3, 3) if j < i else 0) for j in range(n)] for i in range(n)]
    upper = [[1 if i == j else (rng.integer(-3, 3) if j > i else 0) for j in range(n)] for i in range(n)]
    return [[sum(lower[i][k] * upper[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def hide(rng, equations, n):
    """Coordinate change x = A·y, then generator mixing F' = M·F; both determinant 1."""
    a = unit_triangular_product(rng, n)
    forms = [{unit(n, j): a[i][j] for j in range(n) if a[i][j]} for i in range(n)]
    moved = [substitute(f, forms, n) for f in equations]
    mix = unit_triangular_product(rng, len(moved))
    mixed = [{} for _ in moved]
    for i, row in enumerate(mix):
        for j, c in enumerate(row):
            if c:
                mixed[i] = add(mixed[i], moved[j], c)
    return mixed, [{'kind': 'coordinate-change', 'description': 'x = A*y, A = L*U unit triangular, entries in [-3,3]'},
                   {'kind': 'generator-mixing', 'description': 'F\' = M*F, M = L*U unit triangular, entries in [-3,3]'}]


def variables(n):
    return [f'x{i + 1}' for i in range(n)]


# Graphs: vertex count and sorted edge list.

def graph(kind, rng, n=0, m=0, rows=0, cols=0, rim=0):
    if kind == 'path':
        edges = [(i, i + 1) for i in range(n - 1)]
    elif kind == 'cycle':
        edges = [(i, i + 1) for i in range(n - 1)] + [(0, n - 1)]
    elif kind == 'tree':  # random recursive tree: vertex i attaches to a uniform earlier vertex
        edges = [(rng.below(i), i) for i in range(1, n)]
    elif kind == 'grid':
        n = rows * cols
        edges = [(r * cols + c, r * cols + c + 1) for r in range(rows) for c in range(cols - 1)]
        edges += [(r * cols + c, (r + 1) * cols + c) for r in range(rows - 1) for c in range(cols)]
    elif kind == 'gnm':  # uniform m-subset of all vertex pairs
        edges = rng.sample(itertools.combinations(range(n), 2), m)
    elif kind == 'ktree2':  # chordal 2-tree: each new vertex joins both ends of a uniform edge
        edges = [(0, 1), (0, 2), (1, 2)]
        for v in range(3, n):
            a, b = edges[rng.below(len(edges))]
            edges += [(a, v), (b, v)]
    elif kind == 'wheel':
        n = rim + 1
        edges = [(0, i) for i in range(1, n)] + [(i, i + 1) for i in range(1, n - 1)] + [(1, n - 1)]
    else:
        raise ValueError(f'unknown graph {kind}')
    return n, sorted({tuple(sorted(e)) for e in edges})


def proper_colourings(n, edges, colours=3):
    """P(G, colours) by backtracking; exact."""
    neighbours = [[] for _ in range(n)]
    for a, b in edges:
        neighbours[max(a, b)].append(min(a, b))
    colour = [0] * n

    def count(v):
        if v == n:
            return 1
        total = 0
        for c in range(colours):
            if all(colour[u] != c for u in neighbours[v]):
                colour[v] = c
                total += count(v + 1)
        return total
    return count(0)


def colouring(rng, graph_kind, count_colourings=True, **shape):
    n, edges = graph(graph_kind, rng, **shape)
    equations = [{unit(n, v, v, v): 1, (0,) * n: -1} for v in range(n)]
    equations += [{unit(n, a, a): 1, unit(n, a, b): 1, unit(n, b, b): 1} for a, b in edges]
    expected = {'edges': len(edges)}
    if count_colourings:
        expected['vdim'] = proper_colourings(n, edges)
    return n, equations, expected, []


def triangular_chain(rng, n, degrees, roots=None):
    """f_i = x_i^d_i + r_i(x_1..x_i): r_i dense, total degree <= d_i, degree in x_i < d_i.
    With `roots`, f_i = (x_i - a_i)^e (x_i - b_i) for affine a_i, b_i in x_1..x_{i-1}."""
    equations = []
    for i in range(n):
        if roots is None:
            support = [k for k in monomials(n, range(i + 1), 0, degrees[i]) if k[i] < degrees[i]]
            equations.append(add({unit(n, i, *[i] * (degrees[i] - 1)): 1}, random_poly(rng, support)))
            continue
        e, collide = roots
        x = {unit(n, i): 1}
        a = random_poly(rng, monomials(n, range(i), 0, 1))
        b = random_poly(rng, monomials(n, range(i), 0, 1))
        b = a if collide else b
        equations.append(mul(power(add(x, a, -1), e, n), add(x, b, -1)))
    return equations


def triangular(rng, n, degree, hidden):
    equations = triangular_chain(rng, n, [degree] * n)
    transformations = []
    if hidden:
        equations, transformations = hide(rng, equations, n)
    return n, equations, {'vdim': degree ** n}, transformations


def nonradical(rng, n, e, collide):
    equations = triangular_chain(rng, n, None, roots=(e, collide))
    equations, transformations = hide(rng, equations, n)
    expected = {'vdim': (e + 1) ** n}
    if collide:
        expected['radical_vdim'] = 1
    return n, equations, expected, transformations


def planted(rng, n, degrees, terms=None, witness=None):
    """f_i = g_i - g_i(w): g_i dense of degree d_i, or `terms` sampled monomials, one of degree d_i."""
    w = witness or [rng.integer(-5, 5) for _ in range(n)]
    equations = []
    for d in degrees:
        support = monomials(n, range(n), 1, d)
        if terms is not None:
            top = [k for k in support if sum(k) == d]
            first = top[rng.below(len(top))]
            support = [first] + rng.sample([k for k in support if k != first], terms - 1)
        g = random_poly(rng, support)
        equations.append(add(g, {(0,) * n: evaluate(g, w)}, -1))
    return equations, w


def planted_family(rng, n, degrees, terms=None):
    equations, w = planted(rng, n, degrees, terms)
    return n, equations, {'witness': w}, []


def blocks(rng, k, b, coupling):
    """k planted dense quadratic blocks of b variables; in `coupling` equations the term
    x_{β,1}·x_{β,2} is moved to x_{β,1}·x_{β+1,1} with the same coefficient, keeping n, m, the degree
    profile and every term count."""
    n = k * b
    w = [rng.integer(-5, 5) for _ in range(n)]
    equations = []
    for beta in range(k):
        local, _ = planted(Rng(rng.label, beta), b, [2] * b)
        lift = [{unit(n, beta * b + j): 1} for j in range(b)]
        for f in local:  # g(w_block) recomputed below, so the block's own witness is irrelevant
            equations.append(substitute({key: c for key, c in f.items() if any(key)}, lift, n))
    for j in range(coupling):
        beta = j % k
        f = equations[beta * b + j // k]
        old, new = unit(n, beta * b, beta * b + 1), unit(n, beta * b, ((beta + 1) % k) * b)
        f[new] = f.pop(old)
    for f in equations:
        f.pop((0,) * n, None)
        f[(0,) * n] = -evaluate(f, w)
    return n, [{key: c for key, c in f.items() if c} for f in equations], {'witness': w}, []


def minors(matrix, size, n):
    rows, cols = len(matrix), len(matrix[0])
    out = []
    for rs in itertools.combinations(range(rows), size):
        for cs in itertools.combinations(range(cols), size):
            det = {}
            for perm in itertools.permutations(range(size)):
                sign = (-1) ** sum(1 for i, j in itertools.combinations(range(size), 2) if perm[i] > perm[j])
                term = {(0,) * n: sign}
                for i in range(size):
                    term = mul(term, matrix[rs[i]][cs[perm[i]]])
                det = add(det, term)
            out.append(det)
    return out


def slices(rng, n, count):
    return [random_poly(rng, monomials(n, range(n), 0, 1)) for _ in range(count)]


def toric(rng, kind, d=0, rows=0, cols=0, sliced=False):
    """Rational normal curve of degree d, or the Segre embedding of P^(rows-1) x P^(cols-1): the 2x2
    minors of the stated matrix of variables, which generate the toric ideal exactly."""
    if kind == 'rnc':
        n = d + 1
        x = [{unit(n, i): 1} for i in range(n)]
        matrix, cone, degree = [x[:-1], x[1:]], 2, d
    else:
        n = rows * cols
        matrix = [[{unit(n, r * cols + c): 1} for c in range(cols)] for r in range(rows)]
        cone, degree = rows + cols - 1, math.comb(rows + cols - 2, rows - 1)
    equations = minors(matrix, 2, n)
    if not sliced:
        return n, equations, {'dimension': cone}, []
    return n, equations + slices(rng, n, cone), {'generic_vdim': degree}, [
        {'kind': 'slicing', 'description': f'{cone} seeded affine-linear forms appended'}]


def determinantal(rng, rows, cols, n, entry_degree):
    """Maximal minors of a rows x cols matrix of dense seeded integer forms of degree <= entry_degree
    in n variables. Expected codimension cols - rows + 1 (Eagon–Northcott)."""
    matrix = [[random_poly(rng, monomials(n, range(n), 0, entry_degree)) for _ in range(cols)]
              for _ in range(rows)]
    codim = cols - rows + 1
    expected = ({'generic_vdim': math.comb(cols, rows - 1) * entry_degree ** codim} if n == codim
                else {'generic_dimension': n - codim})
    return n, minors(matrix, rows, n), expected, []


def katsura(n):
    """benchmark_systems::katsura in n variables (Katsura-(n-1))."""
    m, equations = n - 1, []
    for level in range(m):
        f = {}
        for i in range(-m, m + 1):
            if abs(i) <= m and abs(level - i) <= m:
                key = unit(n, abs(i), abs(level - i))
                f[key] = f.get(key, 0) + 1
        equations.append(add(f, {unit(n, level): -1}))
    f = {unit(n, 0): 1, (0,) * n: -1}
    equations.append(add(f, {unit(n, i): 2 for i in range(1, n)}))
    return equations


def cyclic(n):
    equations = [{unit(n, *[(s + o) % n for o in range(w)]): 1 for s in range(n)} for w in range(1, n)]
    return equations + [{(1,) * n: 1, (0,) * n: -1}]


def eco(n):
    equations = []
    for lag in range(1, n):
        f = {unit(n, lag - 1, n - 1): 1, (0,) * n: -lag}
        f.update({unit(n, j, j + lag, n - 1): 1 for j in range(n - lag - 1)})
        equations.append(f)
    return equations + [{(0,) * n: 1, **{unit(n, j): 1 for j in range(n - 1)}}]


def noon(n):
    return [{(0,) * n: 10, unit(n, i): -11, **{unit(n, i, j, j): 10 for j in range(n) if j != i}}
            for i in range(n)]


def reimer(n):
    return [{(0,) * n: -1, **{unit(n, *[j] * d): 2 if j % 2 == 0 else -2 for j in range(n)}}
            for d in range(2, n + 2)]


LADDERS = {'katsura': katsura, 'cyclic': cyclic, 'eco': eco, 'noon': noon, 'reimer': reimer}


def ladder(rng, name, n):
    return n, LADDERS[name](n), {}, []


FAMILIES = {
    'zb/graph-3colouring': colouring,
    'zb/hidden-triangular': triangular,
    'zb/nonradical-triangular': nonradical,
    'zb/coupled-blocks': blocks,
    'zb/toric': toric,
    'zb/determinantal': determinantal,
    'zb/planted-dense': planted_family,
    'zb/planted-sparse': planted_family,
}


def P(id, family, seed=None, group=None, parent=None, **parameters):
    return dict(id=id, family=family, seed=seed, group=group, parent=parent, parameters=parameters)


COL, TRI, NR, BLK = 'zb/graph-3colouring', 'zb/hidden-triangular', 'zb/nonradical-triangular', 'zb/coupled-blocks'
TOR, DET, PD, PS = 'zb/toric', 'zb/determinantal', 'zb/planted-dense', 'zb/planted-sparse'
PANEL = [
    # Incidence at fixed (n, m, degree, terms): path vs random tree; grid vs G(n, m); 2-tree vs G(n, m).
    P('zb-col-path-8', COL, graph_kind='path', n=8),
    P('zb-col-tree-8-s1', COL, 1, graph_kind='tree', n=8),
    P('zb-col-path-12', COL, graph_kind='path', n=12),
    P('zb-col-tree-12-s1', COL, 1, graph_kind='tree', n=12),
    P('zb-col-grid-3x4', COL, graph_kind='grid', rows=3, cols=4),
    P('zb-col-gnm-12-17-s1', COL, 1, graph_kind='gnm', n=12, m=17),
    P('zb-col-gnm-12-17-s2', COL, 2, graph_kind='gnm', n=12, m=17),
    P('zb-col-ktree2-12-s1', COL, 1, graph_kind='ktree2', n=12),
    P('zb-col-gnm-12-21-s1', COL, 1, graph_kind='gnm', n=12, m=21),
    P('zb-col-wheel-5', COL, graph_kind='wheel', rim=5),
    P('zb-col-grid-4x5', COL, graph_kind='grid', rows=4, cols=5, count_colourings=False),
    P('zb-col-grid-5x5', COL, graph_kind='grid', rows=5, cols=5, count_colourings=False),
    # Presence of hidden triangular structure: each hidden system is a presentation of its chain.
    P('zb-tri-6-d2-s1', TRI, 1, group='tri-6-d2-s1', n=6, degree=2, hidden=False),
    P('zb-tri-hidden-6-d2-s1', TRI, 1, group='tri-6-d2-s1', parent='zb-tri-6-d2-s1', n=6, degree=2, hidden=True),
    P('zb-tri-8-d2-s1', TRI, 1, group='tri-8-d2-s1', n=8, degree=2, hidden=False),
    P('zb-tri-hidden-8-d2-s1', TRI, 1, group='tri-8-d2-s1', parent='zb-tri-8-d2-s1', n=8, degree=2, hidden=True),
    P('zb-tri-5-d3-s1', TRI, 1, group='tri-5-d3-s1', n=5, degree=3, hidden=False),
    P('zb-tri-hidden-5-d3-s1', TRI, 1, group='tri-5-d3-s1', parent='zb-tri-5-d3-s1', n=5, degree=3, hidden=True),
    P('zb-tri-hidden-11-d2-s1', TRI, 1, n=11, degree=2, hidden=True),
    # Radicality at fixed (n, m, degree, vdim): distinct vs colliding roots, same draws.
    P('zb-nr-6-e1-distinct-s1', NR, 1, group='nr-6-e1-s1', n=6, e=1, collide=False),
    P('zb-nr-6-e1-collide-s1', NR, 1, group='nr-6-e1-s1', n=6, e=1, collide=True),
    P('zb-nr-8-e1-distinct-s1', NR, 1, group='nr-8-e1-s1', n=8, e=1, collide=False),
    P('zb-nr-8-e1-collide-s1', NR, 1, group='nr-8-e1-s1', n=8, e=1, collide=True),
    P('zb-nr-5-e2-collide-s1', NR, 1, n=5, e=2, collide=True),
    P('zb-nr-10-e1-collide-s1', NR, 1, n=10, e=1, collide=True),
    P('zb-nr-12-e1-collide-s1', NR, 1, n=12, e=1, collide=True),
    # Block coupling count at fixed (n, m, degree, terms): the same draws with c terms moved.
    P('zb-blk-2x4-c0-s1', BLK, 1, group='blk-2x4-s1', k=2, b=4, coupling=0),
    P('zb-blk-2x4-c1-s1', BLK, 1, group='blk-2x4-s1', k=2, b=4, coupling=1),
    P('zb-blk-2x4-c2-s1', BLK, 1, group='blk-2x4-s1', k=2, b=4, coupling=2),
    P('zb-blk-3x3-c0-s1', BLK, 1, group='blk-3x3-s1', k=3, b=3, coupling=0),
    P('zb-blk-3x3-c3-s1', BLK, 1, group='blk-3x3-s1', k=3, b=3, coupling=3),
    P('zb-blk-2x6-c0-s1', BLK, 1, group='blk-2x6-s1', k=2, b=6, coupling=0),
    P('zb-blk-2x6-c2-s1', BLK, 1, group='blk-2x6-s1', k=2, b=6, coupling=2),
    P('zb-blk-3x4-c3-s1', BLK, 1, k=3, b=4, coupling=3),
    # Binomial: exact toric ideals, unsliced (positive-dimensional) and generically sliced.
    P('zb-toric-rnc-5', TOR, kind='rnc', d=5),
    P('zb-toric-rnc-8-slice-s1', TOR, 1, kind='rnc', d=8, sliced=True),
    P('zb-toric-segre-3x3', TOR, kind='segre', rows=3, cols=3),
    P('zb-toric-segre-3x3-slice-s1', TOR, 1, kind='segre', rows=3, cols=3, sliced=True),
    P('zb-toric-segre-3x5-slice-s1', TOR, 1, kind='segre', rows=3, cols=5, sliced=True),
    P('zb-toric-segre-4x4-slice-s1', TOR, 1, kind='segre', rows=4, cols=4, sliced=True),
    # Rank constraints on seeded forms; the last is unsliced, so positive-dimensional.
    P('zb-det-2x4-lin-s1', DET, 1, rows=2, cols=4, n=3, entry_degree=1),
    P('zb-det-2x6-lin-s1', DET, 1, rows=2, cols=6, n=5, entry_degree=1),
    P('zb-det-3x5-lin-s1', DET, 1, rows=3, cols=5, n=3, entry_degree=1),
    P('zb-det-2x4-quad-s1', DET, 1, rows=2, cols=4, n=3, entry_degree=2),
    P('zb-det-2x6-lin-n8-s1', DET, 1, rows=2, cols=6, n=8, entry_degree=1),
    # Overdetermination and degree profile; dense all-monomial vs sampled support.
    P('zb-pd-8-8-d2-s1', PD, 1, n=8, degrees=[2] * 8),
    P('zb-pd-6-6-d3-s1', PD, 1, n=6, degrees=[3] * 6),
    P('zb-pd-7-10-mixed-s1', PD, 1, n=7, degrees=[2] * 5 + [3] * 5),
    P('zb-pd-12-24-d2-s1', PD, 1, n=12, degrees=[2] * 24),
    P('zb-pd-14-14-d2-s1', PD, 1, n=14, degrees=[2] * 14),
    P('zb-ps-10-15-d2-t12-s1', PS, 1, n=10, degrees=[2] * 15, terms=12),
    P('zb-ps-10-15-d2-t12-s2', PS, 2, n=10, degrees=[2] * 15, terms=12),
    P('zb-ps-14-21-d2-t16-s1', PS, 1, n=14, degrees=[2] * 21, terms=16),
    P('zb-ps-8-8-d3-t10-s1', PS, 1, n=8, degrees=[3] * 8, terms=10),
    P('zb-ps-16-16-d2-t18-s1', PS, 1, n=16, degrees=[2] * 16, terms=18),
    # The retained benchmark_systems ladders, under the #1005 audit's family and formulation ids.
    *[P(f'zb-{name}-{n}', name, name=name, n=n) for name, n in [
        ('katsura', 9), ('katsura', 12), ('cyclic', 6), ('cyclic', 7), ('eco', 8),
        ('eco', 12), ('noon', 5), ('noon', 7), ('reimer', 4), ('reimer', 6)]],
]


def build(problem):
    """The exact integer system: (variables, equations, expected properties, transformations)."""
    family, parameters = problem['family'], problem['parameters']
    # Rungs of a matched ladder share one draw stream, so they differ only where the spec says.
    rng = Rng(family, problem['group']) if problem['group'] else Rng(family, parameters, problem['seed'])
    builder = ladder if family in LADDERS else FAMILIES[family]
    n, equations, expected, transformations = builder(rng, **parameters)
    return variables(n), equations, expected, transformations


def record(problem, system, field_name):
    p = FIELDS[field_name]
    names, equations, _, transformations = system
    reduced = [{k: c % p for k, c in f.items() if c % p} for f in equations]
    vanished = sum(len(f) for f in equations) - sum(len(f) for f in reduced)
    transformations = list(transformations) + [
        {'kind': 'prime-reduction', 'description': f'integer coefficients reduced modulo {p}'}]
    if vanished:
        transformations.append({'kind': 'exceptional-reduction',
                                'description': f'{vanished} coefficients vanish modulo {p}'})
    family, ladder_name = problem['family'], problem['parameters'].get('name')
    rec = {
        'schema': 'corpus-instance-v1',
        'id': f'{problem["id"]}@{field_name}',
        'field': {'characteristic': str(p), 'extension_degree': 1, 'defining_polynomial': []},
        'variables': names,
        'order': 'grevlex',
        'task': 'T-GB',
        'equations': [[{'exponents': list(k), 'coefficient': [str(c)]} for k, c in sorted(f.items())]
                      for f in reduced],
        'generator': {'repository': REPOSITORY, 'revision': GENERATOR_REVISION, 'path': PATH,
                      'call': ['python3', PATH, 'emit', problem['id']], 'seed': problem['seed'],
                      'parameters': problem['parameters']},
        'source': {'url': f'{REPOSITORY}/blob/{GENERATOR_REVISION}/{PATH}', 'revision': GENERATOR_REVISION,
                   'license': 'MIT (Zeebra repository; generated data)'},
        'transformations': transformations,
        'lineage': {
            'support_id': None,
            'formulation_id': (f'{family}/{problem["parameters"]["n"]}' if ladder_name
                               else f'{family}/{problem["id"]}'),
            'family_id': family,
            'source_id': f'zeebra/{family}' if ladder_name else f'zeebra/m34-structural/{family}',
            'presentation_parent': f'{problem["parent"]}@{field_name}' if problem['parent'] else None,
            'family_parameters': dict(problem['parameters'], seed=problem['seed']),
        },
    }
    # A matched ladder shares one draw, so its rungs share a conservative support group.
    rec['lineage']['support_id'] = (f'{family}/{problem["group"]}' if problem['group']
                                    else corpus_lineage.support_digest(rec))
    rec['normalized_input_digest'] = corpus_lineage.input_digest(rec)
    return rec


def build_catalog():
    if GENERATOR_REVISION is None:
        raise SystemExit('GENERATOR_REVISION is unset: records need the main commit of these generators')
    records = []
    for problem in PANEL:
        system = build(problem)
        records += [record(problem, system, name) for name in FIELDS]
    return records


def singular_reference(record, singular, timeout):
    entry = {'variables': record['variables'], 'equations': oracle.generator_texts(record)}
    return oracle.singular_reference(record, entry, singular, timeout)


def composition(panels):
    """§8.2's composition read over (issue, catalog, references) panels, one row per family.
    A base problem is a record at p31; it is frontier when the p31 oracle did not finish."""
    rows = {}
    for issue, catalog, references in panels:
        refs = json.loads(Path(references).read_text())['references']
        for rec in json.loads(Path(catalog).read_text()):
            if not rec['id'].endswith('@p31'):
                continue
            lineage = rec['lineage']
            row = rows.setdefault(lineage['family_id'], dict(issue=issue, bases=0, n=set(), m=set(),
                                                             supports=set(), frontier=0, seeded=False))
            row['bases'] += 1
            row['n'].add(len(rec['variables']))
            row['m'].add(len(rec['equations']))
            row['supports'].add(lineage['support_id'])
            row['seeded'] |= bool(rec['generator'] and rec['generator']['seed'] is not None)
            row['frontier'] += refs[rec['id']]['status'] == 'frontier'
    total = sum(r['bases'] for r in rows.values())
    span = lambda s: f'{min(s)}–{max(s)}' if len(s) > 1 else f'{min(s)}'  # noqa: E731
    lines = ['| Family | Issue | Base problems | Share | n | m | Scales (distinct n) | Supports | Frontier |',
             '|---|---|---:|---:|---|---|---:|---:|---:|']
    for family, r in sorted(rows.items(), key=lambda kv: (kv[1]['issue'], kv[0])):
        lines.append(f'| `{family}` | {r["issue"]} | {r["bases"]} | {100 * r["bases"] / total:.1f}% | {span(r["n"])} | '
                     f'{span(r["m"])} | {len(r["n"])} | {len(r["supports"])} | {r["frontier"]} |')
    frontier = sum(r['frontier'] for r in rows.values())
    by_issue = {i: sum(1 for r in rows.values() if r['issue'] == i) for i, _, _ in panels}
    checks = [
        (f'{len(rows)} families (≥ 10)', len(rows) >= 10),
        (f'{total} base problems (≥ 60)', total >= 60),
        (', '.join(f'{k} families from {i}' for i, k in by_issue.items()) + ' (≥ 4 each)',
         all(k >= 4 for k in by_issue.values())),
        (f'largest family {max(r["bases"] for r in rows.values())} of {total} (≤ 15%)',
         all(r['bases'] <= 0.15 * total for r in rows.values())),
        ('seeded families with < 2 supports: ' + (', '.join(f for f, r in sorted(rows.items())
         if r['seeded'] and len(r['supports']) < 2) or 'none'),
         all(len(r['supports']) >= 2 for r in rows.values() if r['seeded'])),
        (f'families with one scale: {sum(1 for r in rows.values() if len(r["n"]) < 2)}',
         all(len(r['n']) >= 2 for r in rows.values())),
        (f'{frontier} frontier base problems, {100 * frontier / total:.1f}% (≥ 10%)', frontier >= 0.1 * total),
    ]
    return '\n'.join(lines), checks


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    sub = parser.add_subparsers(dest='command', required=True)
    emit = sub.add_parser('emit', help='print one problem\'s records')
    emit.add_argument('problem')
    sub.add_parser('catalog', help='write catalog.json')
    sub.add_parser('check', help='verify catalog.json is current and every record validates')
    ref = sub.add_parser('references', help='Singular digests at p31, certified grobx at p64')
    ref.add_argument('--singular', default='Singular')
    ref.add_argument('--grobx', default='/buildcache/cargo-target/zeebra-bench-m34/grobx-8005a2a1/release/grobx-driver')
    ref.add_argument('--timeout', type=float, default=120.0)
    ref.add_argument('--grobx-timeout', type=float, default=300.0)
    ref.add_argument('--jobs', type=int, default=8)
    sub.add_parser('compose', help='composition table over the #1006 and #1007 panels (plan §8.2)')
    args = parser.parse_args()

    if args.command == 'compose':
        public = ROOT / 'research' / 'm34-public-corpus'
        table, checks = composition([('#1006', public / 'catalog.json', public / 'references.json'),
                                     ('#1007', CATALOG, REFERENCES)])
        print(table + '\n')
        print('\n'.join(f'- {"met" if ok else "**not met**"}: {text}' for text, ok in checks))
        return 0

    if args.command == 'emit':
        problem = next(p for p in PANEL if p['id'] == args.problem)
        system = build(problem)
        for name in FIELDS:
            print(json.dumps(record(problem, system, name), sort_keys=True, separators=(',', ':')))
        return 0
    records = build_catalog()
    if args.command == 'catalog':
        CATALOG.write_text(oracle.dump_catalog(records))
        return 0
    if args.command == 'check':
        for rec in records:
            corpus_lineage.validate_record(rec)
        if CATALOG.read_text() != oracle.dump_catalog(records):
            print('catalog.json is stale: run tools/m34_structural_corpus.py catalog', file=sys.stderr)
            return 1
        stale = sorted(set(json.loads(REFERENCES.read_text())['references']) - {r['id'] for r in records})
        if stale:
            print(f'references.json names unknown records: {stale}', file=sys.stderr)
            return 1
        print(f'ok: {len(PANEL)} base problems, {len(records)} records')
        return 0

    def reference(rec):
        if int(rec['field']['characteristic']) < 2 ** 31:
            return singular_reference(rec, args.singular, args.timeout)
        return oracle.grobx_reference(rec, args.grobx, args.grobx_timeout)

    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        references = {r['id']: dict(res, normalized_input_digest=r['normalized_input_digest'])
                      for r, res in zip(records, pool.map(reference, records))}
    REFERENCES.write_text(json.dumps({
        'schema': 'm34-public-reference-v2',
        'oracles': {'singular': {'version': oracle.singular_version(args.singular), 'timeout_seconds': args.timeout},
                    'grobx-certified': {'version': oracle.grobx_version(args.grobx),
                                        'timeout_seconds': args.grobx_timeout}},
        'references': references}, indent=1, sort_keys=True) + '\n')
    return 0


if __name__ == '__main__':
    sys.exit(main())
