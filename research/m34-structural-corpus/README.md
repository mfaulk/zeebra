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
