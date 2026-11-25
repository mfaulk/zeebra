# #1007: controlled structural families

M34's controlled corpus ([plan §8.2](../../docs/MILESTONE-GENERALIZABLE-SELECTION.md)). Each family
varies **one** structural property while holding the variable count, equation count, degree
profile and term count fixed or nearly fixed. Families: incidence, hidden triangular structure,
radicality, block coupling, binomial structure, rank constraints, overdetermination and support
density. The retained `benchmark_systems` ladders are admitted beside them, under the
[#1005 audit](../corpus-lineage/README.md)'s family and formulation ids.

[`tools/m34_structural_corpus.py`](../../tools/m34_structural_corpus.py) holds every generator and
the panel. Each problem is an **exact integer system**, reduced at 2³¹−1 (`p31`) and 2⁶⁴−59 (`p64`),
with grevlex and task `T-GB`. A field twin is the same formulation (§8.2).

## Reproduce

```sh
python3 tools/test/m34-structural-corpus-test.py
python3 tools/m34_structural_corpus.py emit zb-col-grid-3x4     # one problem's two records
```

Run from the repository root with Python 3.9 or newer, standard library only.

## Seeds and draws

A problem's draws come from SHA-256 of `(label, counter)`, rejection-sampled to the range. The label
is the family id plus the problem's parameters and seed. **Rungs of a matched ladder** (a `group` in
the panel) share one label, so they share every draw and differ only where the specification says.
No library RNG is involved, so neither a Python version nor a platform can change an instance. The
test pins the first draws and a digest over every record's normalized input.

A random coefficient is a uniform nonzero integer in [−2¹⁵, 2¹⁵], and a witness coordinate is a
uniform integer in [−5, 5]. No coefficient of the panel vanishes at either prime, and a test
asserts that. Field twins therefore share their computed `support-v1` id.

## Lineage

- `family_id` is the generator: for example `zb/graph-3colouring`. A ladder keeps the audit's id,
  such as `katsura`.
- `formulation_id` is `family/problem`, or `family/n` for a ladder (the audit's `katsura/9`).
- `source_id` is `zeebra/m34-structural/<family>`, or `zeebra/<ladder>` as in the audit.
- `support_id` is the computed `support-v1` digest. The exception is a matched ladder's rungs,
  which share one conservative group id (`family/group`): they share draws, so S1 must keep them
  together.
- `presentation_parent` links a hidden triangular system to its visible chain.
- `generator` records `call = python3 tools/m34_structural_corpus.py emit <id>`, the seed and
  the parameters. `transformations` records the coordinate change, generator mixing and slicing.

The ladders were inspected in M29–M33 and are **exposed**. #1005's freeze must place them in
development.

## Family specifications

Variables are `x1 … xn`. "Exact" is proved by construction or by a cited theorem; "generic" is an
expectation for a generic draw, which the references check rather than assume.

### `zb/graph-3colouring`: incidence

For a graph G on n vertices the ideal is `x_v³ − 1` for each vertex, plus
`x_u² + x_u x_v + x_v²` for each edge `uv`. The edge polynomial is `(x_u³ − x_v³)/(x_u − x_v)`.

- **Graphs.** `path`, `cycle`, `grid r×c`, and `tree`, a random recursive tree in which vertex i
  joins a uniform earlier vertex. `gnm(n, m)` is a uniform m-subset of vertex pairs. `ktree2` is a
  chordal 2-tree: each new vertex joins both ends of a uniform existing edge. `wheel` is a hub
  joined to a cycle rim.
- **Exact.** V(I) is the set of proper 3-colourings, with the cube roots of unity as colours
  (Bayer 1982; Hillar & Windfeldt 2008). When char ≠ 3, `x³ − 1` is squarefree, so I is radical
  by Seidenberg's lemma. Hence `vdim = P(G, 3)`, the number of proper colourings, which the tool
  counts exactly. A graph that is not 3-colourable gives the unit ideal: the odd wheel, and
  `gnm-12-17-s2`, which has no proper colouring.
- **Field constraint.** char ∤ 3. Base-field colourings need 3 | p − 1. That holds at `p31` but
  not at `p64`, where the points lie in F_{p²}. vdim is unchanged.
- **Not known.** Gröbner degree, or any complexity claim from chordality: Cifuentes & Parrilo's
  results need their stated assumptions.

### `zb/hidden-triangular`: presentation

The visible chain is `f_i = x_i^d + r_i(x_1 … x_i)`. Here r_i is dense, of total degree ≤ d and of
degree < d in x_i.

- **Exact.** Under lex with `x_n > … > x_1` the leading terms are the pairwise coprime `x_i^d`, so
  the chain is a lex Gröbner basis and `vdim = dⁿ`.
- **The hidden child** substitutes `x = A·y` and then mixes generators, `F' = M·F`. A and M are
  L·U products with unit diagonals and entries in [−3, 3], so det = 1 and both are invertible at
  every prime. Generator mixing preserves the ideal. A coordinate change preserves vdim and the
  quotient structure, so the child's `vdim = dⁿ` is also exact. Its `presentation_parent` is the
  chain.
- **Not known.** Radicality: it holds for a generic draw but is not certified.

### `zb/nonradical-triangular`: multiplicity

`f_i = (x_i − a_i)^e · (x_i − b_i)`, where `a_i` and `b_i` are seeded affine-linear forms in
`x_1 … x_{i−1}`. The system is then hidden as above. In the `collide` rung `b_i = a_i`, and both
rungs share every draw.

- **Exact.** The chain is monic in x_i of degree e + 1, so `vdim = (e + 1)ⁿ` in both rungs. When the
  roots collide, V(I) is the single point fixed by `x_i = a_i(x_<i)`. The radical is maximal, the
  radical's vdim is 1, and the whole of `(e+1)ⁿ` is multiplicity.
- **The matched pair.** Equal n, m, degrees, vdim and support. Only radicality changes.
- **Not known.** Whether the `distinct` rung is radical. It needs a_i ≠ b_i at every point, which
  is generic but not certified.

### `zb/coupled-blocks`: decomposition

The system has k blocks of b variables. Each block has b dense, planted quadratics in its own
variables, with one witness w drawn for all n = kb variables. In the coupled rung with c couplings,
equation ⌊j/k⌋ of block j mod k, for j < c, has its term `x_{β,1}x_{β,2}` replaced by
`x_{β,1}x_{β+1,1}` with the same coefficient. Then every constant is recomputed so that w is
still a zero.

- **Exact.** n, m, the degree profile and every equation's term count are equal across rungs; a
  test asserts this. w lies on every rung. At c = 0 the ideal is the sum of the block ideals in
  disjoint variables.
- **Not known.** vdim, for any rung. For a dense square block it is generically 2ᵇ per block.

### `zb/toric`: binomial (the actual ideals)

- **Rational normal curve of degree d.** The 2×2 minors of `[[x_1 … x_d], [x_2 … x_{d+1}]]`.
- **Segre `P^{r−1} × P^{c−1}`.** The 2×2 minors of the generic r×c matrix of variables.
- **Exact.** These minors *generate* the toric ideal, which is prime (classical; e.g. Sturmfels,
  *Gröbner Bases and Convex Polytopes*, ch. 4 and 14). Neither ideal is a lattice-basis ideal: a
  lattice basis does not in general generate a toric ideal, and none is used here. The unsliced
  systems are homogeneous and positive-dimensional. The affine cone has dimension 2 for the
  curve and r + c − 1 for Segre.
- **Sliced.** A rung appends as many seeded affine-linear forms as the cone's dimension. For a
  generic slice, vdim is the degree of the variety: d for the curve, `C(r+c−2, r−1)` for Segre.
  This is generic, not certified.

### `zb/determinantal`: rank constraints

The ideal is the maximal (r×r) minors of an r×c matrix whose entries are dense seeded integer
forms of degree ≤ e in n variables.

- **Exact.** The generators and their degree, re.
- **Generic.** The expected codimension is c − r + 1 (Eagon–Northcott). When n equals that
  codimension the system is expected to be zero-dimensional, with vdim `C(c, r−1)·e^{c−r+1}` by
  Porteous. When n is larger (the `n8` rung) the rank variety has expected dimension n − c + r − 1.
  Neither is certified.

### `zb/planted-dense` and `zb/planted-sparse`: overdetermination and density

`f_i = g_i − g_i(w)`, where w is a seeded integer point. A dense `g_i` has every nonconstant
monomial of degree ≤ d_i. A sparse `g_i` has `terms` monomials sampled without replacement,
including at least one of degree d_i. The degree profiles are quadratic, cubic and mixed 2/3, with
m/n from 1 to 2. These are separate families, because dense and sampled supports are different
mechanisms (#1005).

- **Exact.** w is a zero of every equation.
- **Not known.** Uniqueness of w, dimension and radicality.

### Retained ladders

`katsura`, `cyclic`, `eco`, `noon` and `reimer`. These are the `benchmark_systems.rs` definitions,
in n variables, with integer coefficients. Noon is multiplied by 10, so it needs char ∤ 10. A test
checks that the Katsura, Cyclic, Eco and Noon systems match all 28 Rust-generated ladders committed
in `research/wide-corpus/cases.json`, by normalized digest. Reimer is checked against its written
definition. The wide catalog's dense MQ is not reproduced: its draws are Rust `StdRng` over F_p.

### Not admitted in this slice

- **Bilinear / multihomogeneous.** #1034 implemented it in Rust
  (`benchmark_systems::bilinear`). That generator draws over F_p with `StdRng`, so a p31/p64 pair
  would be two formulations, not one, and admitting it needs a Rust emitter. Left to a follow-up.
- **Lattice-basis binomial ideals** and other ideals whose saturation is the toric ideal. Dropped
  under #1007's stop condition until each one's ideal is stated exactly.

## Matched comparisons

| Property varied | Pairs or ladders (equal n, m, degree profile and term counts) |
|---|---|
| Incidence | `col-path-8` / `col-tree-8-s1`; `col-path-12` / `col-tree-12-s1`; `col-grid-3x4` / `col-gnm-12-17-s1`; chordal `col-ktree2-12-s1` / `col-gnm-12-21-s1` |
| Hidden triangular structure | each `tri-…` chain / its `tri-hidden-…` child (same ideal up to coordinates) |
| Radicality | `nr-6-e1-distinct-s1` / `nr-6-e1-collide-s1`; the same at n = 8 (equal support and vdim) |
| Block coupling count | `blk-2x4` c = 0, 1, 2; `blk-3x3` c = 0, 3; `blk-2x6` c = 0, 2 |

Pairs across families are also available, with equal n and m. Examples are `tri-hidden-8-d2` beside
`pd-8-8-d2` and `nr-8-e1-*`, all dense quadratic with n = m = 8, and `det-2x6-lin-n8` beside the
unsliced toric systems.

## Panel

65 base problems in 13 families, 130 records in [`catalog.json`](catalog.json). Each record cites
generator revision `d35b7639` (#1129). [`references.json`](references.json) holds a
`reduced-basis-v1` digest per record. At `p31` the oracle is Singular build 44105 (`std`, 120 s); at
`p64` it is certified grobx 0.155.1 (`8005a2a1`, 300 s). These are the same oracles and digest
function as [#1006](../m34-public-corpus/README.md#verification-procedure). The reference runs are
untimed, and *frontier* means neither oracle finished. Every exact claim agrees with both oracles,
and so does every generic expectation; `m34-structural-corpus-test.py` asserts the exact ones.

| Problem | `family_id` | n | m | Expected | p31 (Singular) | p64 (grobx) |
|---|---|---:|---:|---|---|---|
| `zb-col-path-8` | `zb/graph-3colouring` | 8 | 15 | vdim 384 (exact) | 0, vdim 384 | 0, vdim 384 |
| `zb-col-tree-8-s1` | `zb/graph-3colouring` | 8 | 15 | vdim 384 (exact) | 0, vdim 384 | 0, vdim 384 |
| `zb-col-path-12` | `zb/graph-3colouring` | 12 | 23 | vdim 6144 (exact) | 0, vdim 6144 | 0, vdim 6144 |
| `zb-col-tree-12-s1` | `zb/graph-3colouring` | 12 | 23 | vdim 6144 (exact) | 0, vdim 6144 | 0, vdim 6144 |
| `zb-col-grid-3x4` | `zb/graph-3colouring` | 12 | 29 | vdim 1122 (exact) | 0, vdim 1122 | 0, vdim 1122 |
| `zb-col-gnm-12-17-s1` | `zb/graph-3colouring` | 12 | 29 | vdim 300 (exact) | 0, vdim 300 | 0, vdim 300 |
| `zb-col-gnm-12-17-s2` | `zb/graph-3colouring` | 12 | 29 | vdim 0 (exact) | unit ideal | unit ideal |
| `zb-col-ktree2-12-s1` | `zb/graph-3colouring` | 12 | 33 | vdim 6 (exact) | 0, vdim 6 | 0, vdim 6 |
| `zb-col-gnm-12-21-s1` | `zb/graph-3colouring` | 12 | 33 | vdim 72 (exact) | 0, vdim 72 | 0, vdim 72 |
| `zb-col-wheel-5` | `zb/graph-3colouring` | 6 | 16 | vdim 0 (exact) | unit ideal | unit ideal |
| `zb-col-grid-4x5` | `zb/graph-3colouring` | 20 | 51 | — | 0, vdim 54450 | 0, vdim 54450 |
| `zb-col-grid-5x5` | `zb/graph-3colouring` | 25 | 65 | — | 0, vdim 580986 | 0, vdim 580986 |
| `zb-tri-6-d2-s1` | `zb/hidden-triangular` | 6 | 6 | vdim 64 (exact) | 0, vdim 64 | 0, vdim 64 |
| `zb-tri-hidden-6-d2-s1` | `zb/hidden-triangular` | 6 | 6 | vdim 64 (exact) | 0, vdim 64 | 0, vdim 64 |
| `zb-tri-8-d2-s1` | `zb/hidden-triangular` | 8 | 8 | vdim 256 (exact) | 0, vdim 256 | 0, vdim 256 |
| `zb-tri-hidden-8-d2-s1` | `zb/hidden-triangular` | 8 | 8 | vdim 256 (exact) | 0, vdim 256 | 0, vdim 256 |
| `zb-tri-5-d3-s1` | `zb/hidden-triangular` | 5 | 5 | vdim 243 (exact) | 0, vdim 243 | 0, vdim 243 |
| `zb-tri-hidden-5-d3-s1` | `zb/hidden-triangular` | 5 | 5 | vdim 243 (exact) | 0, vdim 243 | 0, vdim 243 |
| `zb-tri-hidden-11-d2-s1` | `zb/hidden-triangular` | 11 | 11 | vdim 2048 (exact) | frontier | frontier |
| `zb-nr-6-e1-distinct-s1` | `zb/nonradical-triangular` | 6 | 6 | vdim 64 (exact) | 0, vdim 64 | 0, vdim 64 |
| `zb-nr-6-e1-collide-s1` | `zb/nonradical-triangular` | 6 | 6 | vdim 64 (exact); radical vdim 1 | 0, vdim 64 | 0, vdim 64 |
| `zb-nr-8-e1-distinct-s1` | `zb/nonradical-triangular` | 8 | 8 | vdim 256 (exact) | 0, vdim 256 | 0, vdim 256 |
| `zb-nr-8-e1-collide-s1` | `zb/nonradical-triangular` | 8 | 8 | vdim 256 (exact); radical vdim 1 | 0, vdim 256 | 0, vdim 256 |
| `zb-nr-5-e2-collide-s1` | `zb/nonradical-triangular` | 5 | 5 | vdim 243 (exact); radical vdim 1 | 0, vdim 243 | 0, vdim 243 |
| `zb-nr-10-e1-collide-s1` | `zb/nonradical-triangular` | 10 | 10 | vdim 1024 (exact); radical vdim 1 | 0, vdim 1024 | 0, vdim 1024 |
| `zb-nr-12-e1-collide-s1` | `zb/nonradical-triangular` | 12 | 12 | vdim 4096 (exact); radical vdim 1 | frontier | frontier |
| `zb-blk-2x4-c0-s1` | `zb/coupled-blocks` | 8 | 8 | planted witness | 0, vdim 256 | 0, vdim 256 |
| `zb-blk-2x4-c1-s1` | `zb/coupled-blocks` | 8 | 8 | planted witness | 0, vdim 256 | 0, vdim 256 |
| `zb-blk-2x4-c2-s1` | `zb/coupled-blocks` | 8 | 8 | planted witness | 0, vdim 256 | 0, vdim 256 |
| `zb-blk-3x3-c0-s1` | `zb/coupled-blocks` | 9 | 9 | planted witness | 0, vdim 512 | 0, vdim 512 |
| `zb-blk-3x3-c3-s1` | `zb/coupled-blocks` | 9 | 9 | planted witness | 0, vdim 512 | 0, vdim 512 |
| `zb-blk-2x6-c0-s1` | `zb/coupled-blocks` | 12 | 12 | planted witness | 0, vdim 4096 | 0, vdim 4096 |
| `zb-blk-2x6-c2-s1` | `zb/coupled-blocks` | 12 | 12 | planted witness | frontier | frontier |
| `zb-blk-3x4-c3-s1` | `zb/coupled-blocks` | 12 | 12 | planted witness | frontier | frontier |
| `zb-toric-rnc-5` | `zb/toric` | 6 | 10 | dim 2 (exact) | dim 2 | positive-dim |
| `zb-toric-rnc-8-slice-s1` | `zb/toric` | 9 | 30 | vdim 8 (generic) | 0, vdim 8 | 0, vdim 8 |
| `zb-toric-segre-3x3` | `zb/toric` | 9 | 9 | dim 5 (exact) | dim 5 | positive-dim |
| `zb-toric-segre-3x3-slice-s1` | `zb/toric` | 9 | 14 | vdim 6 (generic) | 0, vdim 6 | 0, vdim 6 |
| `zb-toric-segre-3x5-slice-s1` | `zb/toric` | 15 | 37 | vdim 15 (generic) | 0, vdim 15 | 0, vdim 15 |
| `zb-toric-segre-4x4-slice-s1` | `zb/toric` | 16 | 43 | vdim 20 (generic) | 0, vdim 20 | 0, vdim 20 |
| `zb-det-2x4-lin-s1` | `zb/determinantal` | 3 | 6 | vdim 4 (generic) | 0, vdim 4 | 0, vdim 4 |
| `zb-det-2x6-lin-s1` | `zb/determinantal` | 5 | 15 | vdim 6 (generic) | 0, vdim 6 | 0, vdim 6 |
| `zb-det-3x5-lin-s1` | `zb/determinantal` | 3 | 10 | vdim 10 (generic) | 0, vdim 10 | 0, vdim 10 |
| `zb-det-2x4-quad-s1` | `zb/determinantal` | 3 | 6 | vdim 32 (generic) | 0, vdim 32 | 0, vdim 32 |
| `zb-det-2x6-lin-n8-s1` | `zb/determinantal` | 8 | 15 | dim 3 (generic) | dim 3 | positive-dim |
| `zb-pd-8-8-d2-s1` | `zb/planted-dense` | 8 | 8 | planted witness | 0, vdim 256 | 0, vdim 256 |
| `zb-pd-6-6-d3-s1` | `zb/planted-dense` | 6 | 6 | planted witness | 0, vdim 729 | 0, vdim 729 |
| `zb-pd-7-10-mixed-s1` | `zb/planted-dense` | 7 | 10 | planted witness | 0, vdim 1 | 0, vdim 1 |
| `zb-pd-12-24-d2-s1` | `zb/planted-dense` | 12 | 24 | planted witness | 0, vdim 1 | 0, vdim 1 |
| `zb-pd-14-14-d2-s1` | `zb/planted-dense` | 14 | 14 | planted witness | frontier | frontier |
| `zb-ps-10-15-d2-t12-s1` | `zb/planted-sparse` | 10 | 15 | planted witness | 0, vdim 1 | 0, vdim 1 |
| `zb-ps-10-15-d2-t12-s2` | `zb/planted-sparse` | 10 | 15 | planted witness | 0, vdim 1 | 0, vdim 1 |
| `zb-ps-14-21-d2-t16-s1` | `zb/planted-sparse` | 14 | 21 | planted witness | 0, vdim 1 | 0, vdim 1 |
| `zb-ps-8-8-d3-t10-s1` | `zb/planted-sparse` | 8 | 8 | planted witness | frontier | frontier |
| `zb-ps-16-16-d2-t18-s1` | `zb/planted-sparse` | 16 | 16 | planted witness | frontier | frontier |
| `zb-katsura-9` | `katsura` | 9 | 9 | — | 0, vdim 256 | 0, vdim 256 |
| `zb-katsura-12` | `katsura` | 12 | 12 | — | frontier | frontier |
| `zb-cyclic-6` | `cyclic` | 6 | 6 | — | 0, vdim 156 | 0, vdim 156 |
| `zb-cyclic-7` | `cyclic` | 7 | 7 | — | 0, vdim 924 | 0, vdim 924 |
| `zb-eco-8` | `eco` | 8 | 8 | — | 0, vdim 64 | 0, vdim 64 |
| `zb-eco-12` | `eco` | 12 | 12 | — | frontier | frontier |
| `zb-noon-5` | `noon` | 5 | 5 | — | 0, vdim 233 | 0, vdim 233 |
| `zb-noon-7` | `noon` | 7 | 7 | — | 0, vdim 2173 | 0, vdim 2173 |
| `zb-reimer-4` | `reimer` | 4 | 4 | — | 0, vdim 36 | 0, vdim 36 |
| `zb-reimer-6` | `reimer` | 6 | 6 | — | 0, vdim 576 | 0, vdim 576 |

```sh
python3 tools/m34_structural_corpus.py check            # catalog current, records valid
python3 tools/corpus_lineage.py validate research/m34-structural-corpus/catalog.json
python3 tools/m34_structural_corpus.py references --jobs 12   # about 10 minutes, untimed
python3 tools/m34_structural_corpus.py compose          # the table below
```

## Pilot composition (#1006 + #1007)

Read with `compose` at this commit, over `research/m34-public-corpus` (39 problems) and this panel
(65 problems). A base problem is its `p31` record. The table is a snapshot: #1006's remainder
can add rows, so rerun `compose` after it lands. #1005's freeze commit is the binding read.

| Family | Issue | Base problems | Share | n | m | Scales (distinct n) | Supports | Frontier |
|---|---|---:|---:|---|---|---:|---:|---:|
| `sd/chemkin` | #1006 | 1 | 1.0% | 13 | 13 | 1 | 1 | 0 |
| `sd/classical/bjoerk_8` | #1006 | 1 | 1.0% | 8 | 9 | 1 | 1 | 0 |
| `sd/classical/caprasse` | #1006 | 1 | 1.0% | 4 | 4 | 1 | 1 | 0 |
| `sd/classical/cassou` | #1006 | 1 | 1.0% | 4 | 4 | 1 | 1 | 0 |
| `sd/classical/czapor-86a` | #1006 | 1 | 1.0% | 3 | 3 | 1 | 1 | 0 |
| `sd/classical/fee_1` | #1006 | 1 | 1.0% | 4 | 4 | 1 | 1 | 0 |
| `sd/classical/fourcircles` | #1006 | 1 | 1.0% | 2 | 3 | 1 | 1 | 0 |
| `sd/classical/heron` | #1006 | 1 | 1.0% | 7 | 4 | 1 | 1 | 0 |
| `sd/classical/raksanyi` | #1006 | 1 | 1.0% | 8 | 4 | 1 | 1 | 0 |
| `sd/classical/rose` | #1006 | 1 | 1.0% | 3 | 3 | 1 | 1 | 0 |
| `sd/classical/schiele` | #1006 | 1 | 1.0% | 5 | 4 | 1 | 1 | 0 |
| `sd/classical/trinks` | #1006 | 2 | 1.9% | 6 | 6–7 | 1 | 2 | 0 |
| `sd/classical/weispfenning-94` | #1006 | 1 | 1.0% | 3 | 3 | 1 | 1 | 0 |
| `sd/ellipsoid` | #1006 | 3 | 2.9% | 10 | 4 | 1 | 3 | 0 |
| `sd/four-body` | #1006 | 1 | 1.0% | 6 | 6 | 1 | 1 | 0 |
| `sd/gametwo-nash` | #1006 | 3 | 2.9% | 5–7 | 5–7 | 3 | 3 | 1 |
| `sd/robot-kinematics` | #1006 | 4 | 3.8% | 9–34 | 7–34 | 4 | 4 | 0 |
| `sd/runge-kutta-order-conditions` | #1006 | 4 | 3.8% | 8–13 | 6–12 | 2 | 4 | 0 |
| `sd/schwarz` | #1006 | 5 | 4.8% | 7–11 | 7–11 | 5 | 5 | 0 |
| `sd/signal-theory` | #1006 | 4 | 3.8% | 10–16 | 9–24 | 4 | 4 | 1 |
| `sd/virasoro` | #1006 | 1 | 1.0% | 8 | 8 | 1 | 1 | 0 |
| `cyclic` | #1007 | 2 | 1.9% | 6–7 | 6–7 | 2 | 2 | 0 |
| `eco` | #1007 | 2 | 1.9% | 8–12 | 8–12 | 2 | 2 | 1 |
| `katsura` | #1007 | 2 | 1.9% | 9–12 | 9–12 | 2 | 2 | 1 |
| `noon` | #1007 | 2 | 1.9% | 5–7 | 5–7 | 2 | 2 | 0 |
| `reimer` | #1007 | 2 | 1.9% | 4–6 | 4–6 | 2 | 2 | 0 |
| `zb/coupled-blocks` | #1007 | 8 | 7.7% | 8–12 | 8–12 | 3 | 4 | 2 |
| `zb/determinantal` | #1007 | 5 | 4.8% | 3–8 | 6–15 | 3 | 5 | 0 |
| `zb/graph-3colouring` | #1007 | 12 | 11.5% | 6–25 | 15–65 | 5 | 12 | 0 |
| `zb/hidden-triangular` | #1007 | 7 | 6.7% | 5–11 | 5–11 | 4 | 4 | 1 |
| `zb/nonradical-triangular` | #1007 | 7 | 6.7% | 5–12 | 5–12 | 5 | 5 | 1 |
| `zb/planted-dense` | #1007 | 5 | 4.8% | 6–14 | 6–24 | 5 | 5 | 1 |
| `zb/planted-sparse` | #1007 | 5 | 4.8% | 8–16 | 8–21 | 4 | 5 | 2 |
| `zb/toric` | #1007 | 6 | 5.8% | 6–16 | 9–43 | 4 | 6 | 0 |

- met: 34 families (≥ 10)
- met: 104 base problems (≥ 60)
- met: 21 families from #1006, 13 families from #1007 (≥ 4 each)
- met: largest family 12 of 104 (≤ 15%)
- met: seeded families with < 2 supports: none
- **not met**: families with one scale: 16
- met: 11 frontier base problems, 10.6% (≥ 10%)

- **Families with one scale.** All 16 are #1006's: the 12 `sd/classical/*` models, `sd/chemkin`,
  `sd/four-body` and `sd/virasoro`, plus `sd/ellipsoid`, whose three problems share n = 10. Every
  #1007 family covers at least two scales. Closing this gap is #1006's remainder, or an owner
  waiver of the two-scale rule for single-model public families.
- **Small inputs** (best arm under 300 ms) are not read here, because no arm has been timed. Ladders
  such as `reimer-4` and `noon-5`, the colouring paths, `det-2x4-*` and the sliced toric systems are
  the expected small rows; #1012's matrix decides.
- **Exposure.** The 10 ladder problems are M29–M33 relatives (development only, §8.3).
- **Field constraint.** Colouring needs char ≠ 3; Noon needs char ∤ 10. Both primes satisfy both.

## Status against #1007

- **Done.**
  - Generators with written specifications for eight controlled families, plus the five retained
    ladders.
  - Deterministic SHA-256 draws, lineage under #1005, and tests: determinism, a pinned panel
    digest, catalog currency, witnesses, toric parametrizations, determinant-one transforms,
    matched shapes, and oracle agreement with every exact claim.
  - Matched pairs or ladders for incidence, hidden triangular structure, radicality and block
    coupling.
  - Retained tiny, interactive, memory-heavy (`col-grid-5x5`, vdim 580,986) and nine frontier
    inputs.
- **Open.**
  - Admitting #1034's bilinear family; it needs an integer-coefficient emitter.
  - Lattice-basis binomial ideals.
  - The small-input share, which needs #1012's timings.
