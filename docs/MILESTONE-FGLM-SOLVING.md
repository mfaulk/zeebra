# Milestone: FGLM and Zero-Dimensional Polynomial-System Solving

**Status:** M17 complete. A system goes in and a verified solution comes out, by either of two
routes, under budgets that fail with a structured error. The conversion agrees with direct lex F4,
with both classical engines, and with 29 bases from Singular. §14 is the report; §12 marks each
acceptance criterion, including the two that are not met. Design approved against the merged M16 code,
baseline measured, and classification, the quotient monomial basis, the quotient algebra, the
incremental dependence test and the FGLM conversion all implemented and measured end to end.
**Prerequisite:** M16 on `main` at `494c16e`, CI green. Satisfied.

This document began as the M17-0 deliverable — the mathematical design, the API contracts, the
resource semantics, the test corpus, and the measured baseline the implementation is judged
against — and is kept current as each sub-milestone lands. It is written against the code as
merged, not against the proposal; §3 records where the two differ, and §11 tracks what is done.

---

## 1. Objective

Convert a cheap grevlex Gröbner basis into the lex basis that solving needs, and use it to find
solutions over the base field.

Zeebra can already compute Gröbner bases under lex, grlex, and grevlex with either classical
Buchberger or the optimized F4 of M16, reduce to normal form, factor and find roots of univariate
polynomials, and solve systems by back-substitution from a lex basis. The missing capability is
**monomial-order conversion**: `grobner::solve` computes its lex basis directly, with classical
Buchberger, which is the most expensive way to get it.

The measured case for the milestone is in §10. Two numbers from it:

- **cyclic-6**: grevlex in 13.5 ms, lex in 299 ms with F4 and 384 ms with Buchberger. The source
  basis costs **22x less** than the target one, and the quotient algebra it has to be converted
  through has dimension 156.
- **katsura-7**: grevlex in 30.5 ms, and **lex does not finish at all** — it crosses
  `max_live_nonzeros` at 20,003,295 live entries at the default limit, and does not finish at a
  hundredfold limit either. Its quotient algebra has dimension **64**, so the entire conversion
  fits in well under a megabyte.

katsura-7 is the milestone's central instance. It is not that FGLM would be faster there; it is
that the direct route does not arrive.

---

## 2. What M16 provides

Audited against the merged tree. Every signature below is copied from the code.

### 2.1 Polynomials and monomials

`src/poly/multivariate/`. The public name of the polynomial type is `MultivariatePolynomial`; it
is a re-export of `SparseMultiPoly`, which is not itself public.

```rust
pub struct Monomial<const N: usize>;                         // [u32; N] exponents, Copy + Hash + Eq
impl<const N: usize> Monomial<N> {
    pub fn new(exponents: &[u32]) -> Self;
    pub fn univariate(index: usize, exponent: u32) -> Self;
    pub fn one() -> Self;
    pub fn is_one(&self) -> bool;
    pub fn exponents(&self) -> &[u32];
    pub fn degree(&self) -> u64;
    pub fn eval<F: FiniteField>(&self, x: &[F]) -> F;
    pub fn lcm(a: &Self, b: &Self) -> Self;
    pub fn checked_div(&self, rhs: &Self) -> Option<Self>;    // divisibility *and* the quotient
}

pub struct SparseMultiPoly<const N: usize, F: FiniteField>;   // HashMap<Monomial<N>, F>
impl<const N: usize, F: FiniteField> SparseMultiPoly<N, F> {
    pub fn terms(&self) -> &HashMap<Monomial<N>, F>;
    pub fn leading_monomial(&self, order: MonomialOrder) -> Monomial<N>;
    pub fn leading_coefficient(&self, order: MonomialOrder) -> F;
    pub fn substitute(&self, index: usize, value: F) -> Self;
    pub fn eval(&self, x: &[F]) -> F;
    pub fn is_constant(&self) -> bool;
    pub fn scale(&self, scale_factor: &F) -> Self;
    pub fn normal_form(&self, divisors: &[Self], order: MonomialOrder) -> Self;
    pub fn multi_div_rem(&self, divisors: &[Self], order: MonomialOrder) -> (Vec<Self>, Self);
}
```

Everything M17 needs from the polynomial layer is here, and **no change to it is proposed**.
Three properties are load-bearing:

- `checked_div` answers divisibility and returns the cofactor in one pass, which is exactly the
  standard-monomial test and exactly the staircase pruning test.
- `Monomial<N>` is `Copy + Hash + Eq`, so a `HashMap<Monomial<N>, usize>` is the monomial-to-index
  map with no wrapper type and no interning.
- `normal_form` against a Gröbner basis is the canonical representative of a residue class. It is
  the only reduction M17-B needs.

`Monomial`'s `Mul` already uses `checked_add` per exponent and panics in **every** build, release
included, with the stated reason that a wrapped exponent is a different monomial rather than a
large one. So the frontier walk cannot silently leave the ring. It can panic — but for a
zero-dimensional ideal each exponent of a standard monomial is bounded by its variable's pure
power, and a child `x_i * m` exceeds that bound by one at most, so `u32` overflow is unreachable
on the paths M17 introduces. **No new checked monomial API is needed**, contrary to the
proposal's §12.

### 2.2 Monomial orders

```rust
pub enum MonomialOrder { Lexicographic, GradedLexicographic, GradedReverseLexicographic }
impl MonomialOrder {
    pub fn cmp<const N: usize>(&self, a: &Monomial<N>, b: &Monomial<N>) -> Ordering;
    pub fn max<const N: usize>(&self, a: &Monomial<N>, b: &Monomial<N>) -> Monomial<N>;
}
```

`Lexicographic` compares the exponent of `x_0` first, so **x_0 > x_1 > ... > x_{N-1}**. The
elimination polynomial of a lex basis is therefore the one in `x_{N-1}` alone, and `solve` assigns
variables from index `N-1` downwards. FGLM's monomial frontier must run in **increasing** lex
order, which starts at `1` and proceeds through the powers of `x_{N-1}`.

`Monomial<N>` has no `Ord` of its own, so the frontier's priority queue needs a wrapper ordering by
`MonomialOrder::cmp`. That wrapper is the only new ordering code M17 requires.

### 2.3 Gröbner engines

```rust
pub fn buchberger<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>], order: MonomialOrder,
) -> Vec<MultivariatePolynomial<N, F>>;

pub fn buchberger_with_criteria<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>], order: MonomialOrder, criteria: &PairCriteria,
) -> (Vec<MultivariatePolynomial<N, F>>, Statistics);

pub fn f4<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>], order: MonomialOrder,
) -> Result<Vec<MultivariatePolynomial<N, F>>, F4Error>;

pub fn f4_with_options<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>], order: MonomialOrder, options: &F4Options,
) -> Result<(Vec<MultivariatePolynomial<N, F>>, F4Statistics), F4Error>;

pub fn buchberger_reference<const N: usize, F: FiniteField>(..) -> ..;  // the textbook oracle
```

The contract both engines share, and which M17 depends on:

- The result is **the** reduced Gröbner basis, unique for the ideal and order, **sorted by leading
  monomial descending**. Two engines disagreeing is a bug in one of them.
- The **empty** basis is returned for the zero ideal. So `basis.is_empty()` means `I = {0}`, which
  is positive-dimensional for `N >= 1` — not an error and not the unit ideal.
- `{1}` is returned for an inconsistent system, i.e. the unit ideal.
- Zero generators are ignored and duplicates dropped.

`F4Options::default() == F4Options::recommended()`: `Backend::Adaptive`, `ReductionStrategy::
Structured`, `PairCriteria::ALL`, and the limits `max_matrix_rows` 200,000, `max_matrix_columns`
200,000, `max_live_nonzeros` 20,000,000 (≈ 320 MB at 16 bytes per entry), with no cap on batches,
pairs per batch, or basis elements.

`F4Error` is the model M17's error type follows, including its discipline about what a variant
carries: a limit alone where the computation stops at the first crossing, and the measured value
too where the overshoot is bounded and therefore informative.

### 2.4 Solving

`src/grobner/solve.rs`, 493 lines, re-exported as `grobner::solve`.

```rust
pub fn solve<const N: usize, F: FiniteField, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>], rng: &mut R,
) -> Vec<[F; N]>;
```

It computes a lex basis with `buchberger` (not `f4`, and not `buchberger_with_criteria`), then
assigns variables from `N-1` downwards. At each level `candidate_values` collects the basis
polynomials that have become univariate in the current variable, takes `roots` of the first and
filters by the rest, and recurses on each candidate after `substitute`. A variable no basis
polynomial constrains is free, and covering it means enumerating the field — which is why the
function **panics** when a free variable meets a field of order above `MAX_FIELD_ORDER = 2^20`.

Its three private helpers — `as_univariate`, `candidate_values`, and `is_nonzero_constant` — are
directly reusable by M17-D and should be shared rather than reimplemented, which means making them
`pub(crate)` or moving them to a module both solvers use. The part that is *not* reusable is
`extend`: it accumulates every solution rather than stopping at the first, and it has no budget.

### 2.5 Root finding

```rust
pub fn roots<F: FiniteField, R: RngCore + CryptoRng>(
    f: &UnivariatePolynomial<F>, rng: &mut R,
) -> Vec<F>;
```

Distinct roots in F, by `gcd(f, x^q - x)` followed by equal-degree splitting. It reports a repeated
root once and omits roots living only in an extension.

**The proposal's §9.6 asks whether a fallible adapter is needed. It is not.** `roots` panics on
exactly one input, the zero polynomial, and that is a caller precondition which `candidate_values`
already establishes by filtering zero and constant constraints. The one panic deeper in the stack
is in `separate_equal_degree`, after `MAX_SPLIT_ATTEMPTS = 1000` failed random splits; each attempt
succeeds with probability near one half, so reaching it means a defect and not bad luck. M17-D
therefore inherits no panic that an ordinary computation can trigger, and `SolveError` needs no
variant for "root finding failed".

### 2.6 Linear algebra

`src/linalg/` offers `SparseMatrix`, `DenseRows`, `DenseAccumulator`, `row_echelon_with`, and
`reduce_rows_against_pivots_with(backend, matrix, split, max_nonzeros)`, the last of which
establishes a pivot block once and reduces later rows against it without rediscovering it.

That is close to what FGLM's dependence test needs and **still not usable for it**, for a reason
worth stating because it is the one place M17 must write linear algebra rather than call it:
`reduce_rows_against_pivots_with` rewrites the lower rows and reports *statistics*, not the
multipliers it used. FGLM needs the dependence **coefficients relative to the originally accepted
quotient vectors** — not relative to the internally reduced rows — because those coefficients are
the coefficients of the emitted lex basis polynomial. Recovering them means carrying a second
block through the elimination. §7 specifies that structure.

### 2.7 Fields

`FiniteField: Ring + ...`, where `Ring: Copy + Zero + One + Eq + Display + Debug + Arbitrary`. So
every field element is `Copy`, which is why coordinate vectors can be plain `Vec<F>` with no
lifetime or clone discipline.

`order() -> u128`, `characteristic() -> u128`, `inverse()` (panics on zero), `pow`,
`primitive_element`, `root_of_unity`. Publicly instantiable field types are
`PrimeFieldElement64<P>` and `PrimeFieldElement128<P>` with named aliases from `Zp7` up to
`Zp221360928884514619393`; the binary and extension field modules are private, so "multiple
finite fields" in M17's test matrix means prime fields of several sizes.

**No change to `FiniteField` is proposed.** FGLM is generic over it and uses nothing but the field
arithmetic and `inverse`.

### 2.8 Benchmark systems

```rust
pub fn cyclic<const N: usize, F: FiniteField>() -> Vec<MultivariatePolynomial<N, F>>;
pub fn katsura<const N: usize, F: FiniteField>() -> Vec<MultivariatePolynomial<N, F>>;
pub fn planted<const N: usize, F: FiniteField>(point: &[F]) -> Vec<MultivariatePolynomial<N, F>>;
```

See §3.1 for the correction this module needed.

---

## 3. Where the merged code and the M17 proposal disagree

Recorded because a design is only as good as the assumptions under it, and four of these were
wrong.

### 3.1 "Both families are zero-dimensional" was false

`src/grobner/benchmark_systems.rs` opened with "Both families are zero-dimensional, and both are
stated explicitly below so a reader can check the formulation rather than trust it." The second
half was true and the first was not. **cyclic-4 is positive-dimensional**, which §10 measures
directly from the leading monomials of its grevlex basis: `w` has no pure power in the leading-term
ideal. cyclic-n is zero-dimensional only for squarefree n, and 4 = 2² is the first exception.

The proposal was right to name cyclic-4 as a rejection case and right to warn against assuming a
square system is zero-dimensional. The module doc comment is corrected in this PR.

### 3.2 `SparseMultiPoly` is not a public name

The proposal's §5 says to "preserve the existing `Monomial<N>` and `SparseMultiPoly<N,F>`
representations". `SparseMultiPoly` is private; `MultivariatePolynomial` is the public re-export of
it. The intent is preserved, the name in the design is `MultivariatePolynomial`.

### 3.3 Monomial arithmetic is already checked

See §2.1. The proposal asks for checked arithmetic on exponent increments; it is already there, in
every build, and overflow is unreachable on the new paths besides. Checked arithmetic is still
required for the **dimension products and storage sizes** of §8, which are `usize` multiplications
that can genuinely wrap.

### 3.4 Root finding needs no fallible adapter

See §2.5. The proposal leaves this open; it is settled.

### 3.5 One sentence in the proposal is self-contradictory

§9.6 reads "No base-field solution should normally be represented by `Ok(None)` for `solve_one`,
not as an error." The intended semantics, which §9 of this document adopts, is: **a
zero-dimensional system with no base-field solution is `Ok(None)`, never an error**. Resource
exhaustion is `Err`. The two must be distinguishable, which is the whole point.
### 3.6 `coordinates` cannot fail, so it returns no `Result`

The design first had `coordinates` return `Result<Vec<F>, FglmError>` with a `NotAGrobnerBasis`
variant, on the reasoning that a normal-form term outside the standard monomials means the input
was not a Gröbner basis. The variant is unreachable.

`normal_form` moves a term to the remainder **exactly when** no leading monomial of its divisors
divides it, and that is the definition of a standard monomial. The divisors are the same basis
whose leading monomials defined the quotient. So every term of the result is standard, whatever the
input was — a non-Gröbner input gives wrong *coordinates*, not a term outside `B`.

One condition has to hold for that argument: the two must agree on which divisors exist.
`normal_form` drops zero divisors, so `QuotientBasis` had to drop zero basis elements too. It did
not, and the consequence was worse than an unreachable error — the zero polynomial's leading
monomial is 1, which divides everything, so a basis with a zero element appended reported quotient
dimension 0 and made a proper ideal look like the unit ideal. Fixed, with a test, in M17-2.

`NotAGrobnerBasis` is still the right error for FGLM to return, but from the place that can
actually detect it: M17-C's check that the accepted target monomials number exactly `D`.

---

## 4. Mathematical definitions

Let `R = F_q[x_0, ..., x_{N-1}]` and let `I` be the ideal generated by the input system. Let `G` be
a Gröbner basis of `I` under a source order, grevlex in the primary path. Write `A = R/I` and

```text
D = dim_{F_q}(A).
```

`D` is the **quotient vector-space dimension**, not the Krull dimension. A zero-dimensional ideal
has Krull dimension 0 and may have `D` in the thousands. For a proper zero-dimensional ideal `D`
counts the zeros over the algebraic closure **with multiplicity**, so it is an upper bound on the
number of distinct points and not a count of them, and an upper bound on the number of base-field
points in particular.

### 4.1 Standard monomials

```text
B = { m : LM(g) does not divide m for every g in G }.
```

For a proper zero-dimensional ideal the residue classes of `B` are a vector-space basis of `A`, so
`|B| = D`. `B` depends on the order but not on which Gröbner basis of `I` under that order is used,
since the leading-term ideal does not.

### 4.2 Zero-dimensionality

For a **proper** ideal, `dim A < infinity` iff the leading-term ideal contains a positive power of
every variable:

```text
for every i there is d_i > 0 with x_i^{d_i} in LT(I).
```

With a Gröbner basis this is a question about leading monomials alone: `x_i^{d_i} in LT(I)` iff
some `LM(g)` is a pure power of `x_i`. Three cases must be separated, and only the first two are
zero-dimensional:

| input | basis | class | D |
|---|---|---|---|
| inconsistent | contains a nonzero constant, i.e. `{1}` | unit ideal | 0 |
| proper, finite quotient | every variable has a pure-power leading monomial | zero-dimensional | `|B|` |
| anything else, including `I = {0}` | empty, or some variable has no pure power | positive-dimensional | infinite |

The unit ideal satisfies no pure-power condition and is nonetheless zero-dimensional, with `A = 0`.
It must be tested **first**, not rejected.

`prod_i d_i` is an upper bound on `D`, and often a very loose one: katsura-5's grevlex staircase
has pure powers giving a product in the hundreds against a true `D` of 16. **An ideal must not be
rejected because that bound exceeds the budget** — only because the enumeration itself does.

### 4.3 Multiplication operators

For each variable, `T_i : A -> A` by `a |-> x_i a`, represented in the basis `B`. Column `j` of
`T_i` is the coordinate vector of `normal_form(x_i b_j, G)`. These satisfy, and M17-B tests:

- `T_i T_j = T_j T_i`.
- Multiplication in `A` agrees with normal-form reduction modulo `G`.
- `f(T_0, ..., T_{N-1})` is the zero operator for every `f` in `I`, in particular for every input
  generator.
- The class of `1` generates `A` under polynomial combinations of the `T_i`.

For a nonradical ideal the `T_i` have nilpotent parts and need not be diagonalizable. Nothing in
the design may assume otherwise.

### 4.4 FGLM

Walk the monomials in increasing **target** order. Each one is either independent of the
target-order standard monomials accepted so far — and so extends them — or dependent, and the
dependence is a polynomial in `I` whose leading monomial under the target order is that monomial.
The dependent ones form a Gröbner basis under the target order.

No radicality and no shape position is assumed, and none may be. The classical algorithm is correct
for every zero-dimensional ideal, repeated roots included.

---

## 5. Algorithms

### 5.1 Classification — M17-A

```text
classify(G, order):
    if G is empty:                       return PositiveDimensional   # I = {0}
    if some g in G is a nonzero constant: return Unit
    for i in 0..N:
        if no LM(g) is a positive pure power of x_i: return PositiveDimensional
    return ZeroDimensional
```

`O(|G| * N)`. The emptiness test comes first because an empty basis has no leading monomials to
inspect and would otherwise fall through to "no pure power" by accident rather than by argument.

### 5.2 Standard monomials — M17-A

A frontier walk from `1`. Terminates only for a zero-dimensional ideal, so `classify` runs first.

```text
standard_monomials(G, order, max_dimension):
    L         <- { LM(g) : g in G }
    accepted  <- []
    seen      <- { 1 }
    frontier  <- [ 1 ]
    while frontier is not empty:
        m <- pop(frontier)
        if some l in L divides m:  continue          # m is not standard; its multiples are not either
        accepted.push(m)
        if |accepted| > max_dimension: return QuotientDimensionExceeded
        for i in 0..N:
            c <- m * x_i
            if c not in seen: insert c into seen; push c onto frontier
    return accepted
```

Correctness rests on the staircase being closed downwards: if `m` is standard then every divisor of
`m` is standard, so every standard monomial is reachable from `1` by multiplying one variable at a
time, and the walk visits exactly the standard monomials and their immediate multiples. Pruning at
a non-standard `m` is safe because every multiple of `m` is non-standard too.

The order of `accepted` is the traversal order, which is not a monomial order. The public basis is
**sorted by the source order** before use, so the index of a monomial is a function of the ideal
and the order alone. Determinism matters here: the coordinate vectors, the multiplication matrices
and the statistics are all indexed by it.

Cost: `O(D * N * |G|)` divisibility tests of `N` comparisons each. §10 measures it at 0.09 ms for
cyclic-6's `D = 156`, against 13.5 ms for the basis it starts from — under 1%, so there is no case
for a cleverer enumeration, and M17-A did not build one.

`max_dimension` does double duty. It is the resource limit, and it is also what makes a walk that
should never have been started terminate: the pruning is the only thing bounding the frontier, so
without the limit a caller who reached the walk with a positive-dimensional ideal would loop
forever. The classification above is the real guard; the limit is the one that does not depend on
the guard being right. Removing the pruning is the one mutation of this module that hangs the test
suite rather than failing it, which is how that was established.

### 5.3 Multiplication operators — M17-B

```text
operator(i, B, G, order):
    for j in 0..|B|:
        p <- normal_form(x_i * B[j], G, order)
        column[j] <- coordinates(p, B)
```

`coordinates` maps each monomial of the normal form to its index in `B`. A nonzero term whose
monomial is not in `B` would be an internal inconsistency — but it cannot occur, and §3.6 is why.
What must never happen is for such a term to be *silently dropped*, so the lookup panics rather
than skipping.

The common case is that `x_i * B[j]` is itself standard, and then the column is a unit vector and
no reduction is performed at all. §7.2 exploits that.

### 5.4 Incremental dependence — M17-C

Maintain echelon rows over the `D` quotient coordinates together with, for each row, its expression
in terms of the accepted vectors. Testing a candidate reduces it against the rows and accumulates
the same combination on the second block.

```text
reduce(v):                                            # v is not modified
    residue <- v
    c       <- 0 in F^k                               # k = number of accepted vectors
    for each row r with pivot column p:
        if residue[p] is nonzero:
            a       <- residue[p]                     # rows are monic at their pivot
            residue <- residue - a * r.coordinates
            c       <- c + a * r.combination
    if residue is zero: return Dependent(c)           # v = sum c_j * accepted_j
    return Independent(residue, c)

insert(residue, c):                                   # only after Independent, with v accepted as a_k
    p <- the first nonzero column of residue
    s <- residue[p]^{-1}                              # the one inverse per pivot
    rows.push(row { coordinates: s * residue, combination: s * (e_k - c), pivot: p })
```

The invariant each row carries is `coordinates = sum_j combination_j * accepted_j`, which is what
makes `Dependent(c)` a statement about the **accepted vectors** rather than about the internally
reduced rows. `insert`'s combination is `s * (e_k - c)` because the vector being accepted as `a_k`
is `v` itself, and `residue = v - sum_j c_j a_j = a_k - sum_j c_j a_j`. One modular inverse per
pivot, as the proposal requires; everything else is multiply-and-subtract.

Two invariants are cheap enough to assert in debug builds and are worth asserting, because a wrong
dependence coefficient produces a plausible polynomial that is not in the ideal:

- every reported `Dependent(c)` satisfies `v == sum_j c_j * accepted_j`, checked by recomputing;
- `pivots` are pairwise distinct and each row is zero in every earlier row's pivot column.

### 5.5 FGLM conversion — M17-C

```text
fglm_to_lex(G, source_order):
    class <- classify(G, source_order)
    if class is Unit:                 return [ 1 ]
    if class is PositiveDimensional:  return PositiveDimensional
    B <- standard_monomials(G, source_order, options.max_quotient_dimension)
    A <- quotient_algebra(B, G, source_order)          # the operators T_0 .. T_{N-1}

    target    <- []                                    # accepted lex standard monomials, with vectors
    relations <- []                                    # the emitted lex basis
    span      <- empty IncrementalSpan
    frontier  <- min-heap under lex, containing 1

    while frontier is not empty:
        m <- pop-min(frontier)
        if some LM(g) in relations divides m: continue          # the target staircase prunes it
        v <- vector(m)                                          # T_i on a known vector, or coordinates(1)
        match span.reduce(v):
            Independent(residue, c) ->
                span.insert(residue, c)
                target.push((m, v))
                for i in 0..N: push m * x_i onto frontier if not already seen
            Dependent(c) ->
                relations.push(m - sum_j c_j * target[j].monomial)
    if |target| != D: internal inconsistency
    return relations
```

`vector(m)`: `m = 1` gives the coordinate vector of `1`; otherwise `m` entered the frontier as
`x_i * t` for an accepted `t`, so `v(m) = T_i v(t)` — one matrix-vector product, never a
polynomial reduction. Storing the generating `(i, t)` with each frontier entry is what makes this
hold; it is the reason the frontier carries more than a monomial.

**The output is already the unique reduced lex Gröbner basis, and no interreduction pass is
needed.** The argument is worth writing down because it saves a stage the proposal's §8.4 implies:

- Each relation is monic, since the coefficient of `m` is 1 by construction.
- `LM(g_m) = m` under lex, since every `target[j]` was accepted before `m` and the frontier is
  processed in increasing lex order.
- On completion the accepted monomials are exactly the lex standard monomials of `I` and the
  emitted leading monomials generate the lex initial ideal. A standard monomial is by definition
  divisible by no element of the initial ideal, so **no non-leading term of any relation is
  divisible by any relation's leading monomial** — which is precisely reducedness.

Termination and budgets: every candidate is pruned, accepted, or emits a relation; at most `D` are
accepted and each enqueues `N` children, so the frontier admits at most `1 + N*D` candidates in
total and at most `N*D` relations. The candidate budget is therefore not an independent limit but a
consistency check on `D`, which is the limit that matters.

Cost: `O(N*D)` candidates, each one matrix-vector product (`O(D^2)` worst case, `O(D)` when the
operator column is a unit vector) plus one dependence test (`O(D^2)`). That is `O(N*D^3)`, matching
the proposal's estimate.

---

## 6. Proposed public API

New module `src/grobner/fglm/`, re-exported through `grobner`. Names follow the existing surface:
a plain entry point, a `_with_options` variant returning statistics, an options struct with named
constructors, and an error enum of crossed limits.

```rust
// ---- classification and the quotient basis -------------------------------- M17-A

/// What a Gröbner basis says about the dimension of the ideal it generates.
pub enum IdealClass { Unit, ZeroDimensional, PositiveDimensional }

/// `PositiveDimensional` covers the zero ideal, whose basis is empty — see §5.1.
pub fn classify_ideal<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> IdealClass;

/// The standard monomials of a zero-dimensional ideal: a basis of R/I as an F-vector space.
pub struct QuotientBasis<const N: usize> { /* Vec<Monomial<N>> + HashMap<Monomial<N>, usize> */ }

impl<const N: usize> QuotientBasis<N> {
    pub fn new<F: FiniteField>(
        basis: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
        max_dimension: usize,
    ) -> Result<Self, FglmError>;

    pub fn dimension(&self) -> usize;
    pub fn monomials(&self) -> &[Monomial<N>];       // ascending under `order`, so [0] is 1
    pub fn index_of(&self, monomial: &Monomial<N>) -> Option<usize>;
    pub fn order(&self) -> MonomialOrder;
    pub fn is_empty(&self) -> bool;                  // true exactly for the unit ideal
}

impl IdealClass {
    /// `Unit` and `ZeroDimensional`, the two cases with a finite quotient.
    pub fn is_finite_dimensional(&self) -> bool;
}

// ---- the quotient algebra ------------------------------------------------- M17-B

/// R/I for a zero-dimensional I, as D-dimensional coordinate vectors and the operators x_i * .
pub struct QuotientAlgebra<const N: usize, F: FiniteField> { /* .. */ }

impl<const N: usize, F: FiniteField> QuotientAlgebra<N, F> {
    pub fn new(
        basis: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
        options: &FglmOptions,
    ) -> Result<Self, FglmError>;

    pub fn dimension(&self) -> usize;
    pub fn quotient_basis(&self) -> &QuotientBasis<N>;

    /// The coordinate vector of the residue class of 1.
    pub fn one(&self) -> Vec<F>;

    /// T_i applied to a coordinate vector.
    pub fn multiply_by_variable(&self, variable: usize, v: &[F]) -> Vec<F>;

    /// The coordinate vector of a polynomial's residue class. Infallible — see §3.6.
    pub fn coordinates(&self, p: &MultivariatePolynomial<N, F>) -> Vec<F>;

    /// The normal form a coordinate vector represents. Inverse of `coordinates`.
    pub fn polynomial(&self, v: &[F]) -> MultivariatePolynomial<N, F>;

    /// T_i, for the commutation and vanishing tests.
    pub fn operator(&self, variable: usize) -> &MultiplicationOperator<F>;

    /// The source basis, kept so `coordinates` can reduce a polynomial the caller supplies.
    pub fn source_basis(&self) -> &[MultivariatePolynomial<N, F>];
}

impl<F: FiniteField> MultiplicationOperator<F> {
    pub fn dimension(&self) -> usize;
    pub fn apply(&self, v: &[F]) -> Vec<F>;
    pub fn column(&self, j: usize) -> Vec<F>;        // the dense matrix view
    pub fn stored_entries(&self) -> usize;           // what `max_operator_entries` counts
    pub fn standard_columns(&self) -> usize;         // columns that are unit vectors — see §7.2
}

// ---- conversion ----------------------------------------------------------- M17-C

/// The reduced lex Gröbner basis of the ideal `source_basis` generates.
///
/// # Precondition
/// `source_basis` must be a Gröbner basis under `source_order`. Not verified — see
/// `fglm_to_lex_checked`, and note that both engines in this crate satisfy it by construction.
pub fn fglm_to_lex<const N: usize, F: FiniteField>(
    source_basis: &[MultivariatePolynomial<N, F>],
    source_order: MonomialOrder,
) -> Result<Vec<MultivariatePolynomial<N, F>>, FglmError>;

pub fn fglm_to_lex_with_options<const N: usize, F: FiniteField>(
    source_basis: &[MultivariatePolynomial<N, F>],
    source_order: MonomialOrder,
    options: &FglmOptions,
) -> Result<(Vec<MultivariatePolynomial<N, F>>, FglmStatistics), FglmError>;

/// As `fglm_to_lex`, after verifying the precondition.
///
/// Every S-polynomial of the input is reduced against it and must vanish. That costs 0.6x to 27x
/// what computing the basis cost (§10.2), which is why it is a separate entry point.
pub fn fglm_to_lex_checked<const N: usize, F: FiniteField>(
    source_basis: &[MultivariatePolynomial<N, F>],
    source_order: MonomialOrder,
) -> Result<Vec<MultivariatePolynomial<N, F>>, FglmError>;

/// Whether every S-polynomial of `basis` reduces to zero modulo it: Buchberger's criterion.
///
/// Public because the test corpus of §9 needs it as an oracle and the crate had no such helper.
pub fn is_grobner_basis<const N: usize, F: FiniteField>(
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> bool;
```

The target order is lex in M17 and is not a parameter. A `target_order` parameter would be a
promise the implementation does not keep, since §5.5's reducedness argument is order-generic but
the back-substitution that consumes the result is not.

### 6.1 Solving — M17-D

```rust
pub enum SolveStrategy { DirectLexF4, GrevlexF4ThenFglm }

pub struct SolveOptions {
    pub strategy: SolveStrategy,
    pub f4: F4Options,
    pub fglm: FglmOptions,
    /// Partial assignments explored before the search gives up. None for no limit.
    pub max_branches: Option<usize>,
    /// Distinct points returned before `solve_zero_dimensional_*` gives up. None for no limit.
    pub max_solutions: Option<usize>,
}

/// One base-field solution, or `Ok(None)` if the zero-dimensional system has none.
pub fn solve_one<const N: usize, F: FiniteField, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
) -> Result<Option<[F; N]>, SolveError>;

pub fn solve_one_with_options<const N: usize, F: FiniteField, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
    options: &SolveOptions,
) -> Result<Option<[F; N]>, SolveError>;

/// Every distinct base-field solution, or an error. Never a truncated list.
pub fn solve_zero_dimensional<const N: usize, F: FiniteField, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
) -> Result<Vec<[F; N]>, SolveError>;

pub fn solve_zero_dimensional_with_options<const N: usize, F: FiniteField, R: RngCore + CryptoRng>(
    system: &[MultivariatePolynomial<N, F>],
    rng: &mut R,
    options: &SolveOptions,
) -> Result<Vec<[F; N]>, SolveError>;
```

**`grobner::solve` is unchanged** — signature, semantics, and its panic on a free variable over a
large field. It handles positive-dimensional systems by field enumeration, which the new API
refuses outright, so the two are not substitutes and neither is deprecated in M17. The new
functions go in `src/grobner/solve_zero_dimensional.rs`, a private module re-exported from
`grobner`, which is how `solve` is already arranged.

`solve_one` returns the **first** complete point found, and which point that is depends on the
traversal order and on `rng`. It is not specified, and tests must not assume one.

**There is no field-order limit, and that is a theorem rather than an omission.** `solve` has
`MAX_FIELD_ORDER = 2^20` because a variable the basis does not constrain can only be covered by
enumerating the field. For a zero-dimensional ideal no variable is ever unconstrained:
zero-dimensionality gives `x_k^d` in `LT(I)`, so some basis element has `LM(g) = x_k^d`; under lex
every monomial of `g` is at most `x_k^d` and therefore has exponent zero in `x_0 .. x_{k-1}`, so
`g` lies in `F[x_k, ..., x_{N-1}]`; substituting the already-assigned deeper variables leaves a
univariate polynomial in `x_k` whose leading coefficient is `g`'s, which is 1. So the constraint is
always there, of degree at least one, and the field's size never enters the search. §10.3 solves
over GF(2^31 - 1) throughout, two thousand times `solve`'s limit.

Two cheap checks in the search — the mid-level contradiction test and the all-zero test at the leaf
— **never fired on any system in the test corpus**, and are kept anyway. The argument that they are
unreachable is not airtight: a basis element like `x*y - 1` degenerates to the nonzero constant
`-1` if `y` is assigned zero, and `y` cannot be assigned zero only because a candidate value is
always the coordinate of a genuine solution over the algebraic closure. That holds for a reduced
lex basis of a zero-dimensional ideal and is not proved here, so the checks stay as a bound on the
damage from a mistake in that reasoning.

---

## 7. Data structures, with their storage

### 7.1 Coordinate vectors

`Vec<F>` of length `D`. `F: Copy`, so there is no indirection and no cloning discipline. Dense,
because a residue class of a random polynomial is dense in `B` and the vectors are short.

### 7.2 Multiplication operators

```rust
pub struct MultiplicationOperator<F: FiniteField> { columns: Vec<Column<F>> }

enum Column<F: FiniteField> {
    /// x_i * b_j is itself a standard monomial: the column is a unit vector. No storage, no
    /// reduction, and a matrix-vector product that is a single read.
    Standard(usize),
    /// x_i * b_j left the staircase and reduced to a combination of standard monomials.
    Reduced(Vec<(usize, F)>),
}
```

**The split is justified on two of three benchmark families and not on the third**, which was
worth measuring rather than assuming. `cargo run --release --example fglm_operators`, grevlex:

| system | N | D | columns inside the staircase | stored entries vs `N * D^2` | dense bytes / sparse bytes |
|---|---|---|---|---|---|
| katsura-3 | 3 | 4 | 25.0% | 56.25% | **0.89x** |
| katsura-5 | 5 | 16 | 27.5% | 58.67% | **0.85x** |
| katsura-7 | 7 | 64 | 27.9% | 56.70% | **0.88x** |
| cyclic-3 | 3 | 6 | 38.9% | 15.74% | 3.18x |
| cyclic-5 | 5 | 70 | 42.3% | 8.41% | 5.95x |
| cyclic-6 | 6 | 156 | 39.7% | 8.80% | 5.68x |
| planted-4 | 4 | 16 | 37.5% | 5.47% | 9.14x |
| planted-6 | 6 | 64 | 37.5% | 1.37% | 36.57x |
| planted-8 | 8 | 256 | 37.5% | 0.34% | **146.29x** |

Two corrections to the reasoning this design was first written with.

**A standard product is not the common case.** It is 25% to 42% of columns, never a majority. The
staircase is closed downwards, but in `N` variables a thin staircase has far more outer surface
than interior, so most products leave it. The first version of this section asserted "most", and
the first version of the test asserted it too; the test failed, which is how the figures above came
to be measured.

**On the katsura family the sparse form costs more memory than a dense matrix.** A stored entry is
16 bytes — a `usize` index and a 64-bit element — against 8 bytes for a dense cell, so sparsity has
to beat 50% fill to pay at all, and katsura sits at 56–59%. The table's last column is below 1.00x
on every katsura instance.

The representation is kept because it is correct, simple, and right on two families out of three by
up to 146x; **a dense or hybrid column, chosen per operator from the measured fill, is an M17-E
question and is deliberately not an option yet.** `max_operator_entries` counts entries rather than
bytes for the same reason `F4Options::max_live_nonzeros` does, and the figures above are what make
it possible to convert an entry budget into a dimension.

### 7.3 The incremental span

Two `D`-column blocks per accepted vector: the echelon coordinates and the combination over the
accepted vectors. `2 * D^2` field elements at full rank, so `16 * D^2` bytes at 8 bytes each —
389 KB at `D = 156`, 268 MB at `D = 4,096`, 1.6 GB at `D = 10,000`. Dense: the whole point of the
structure is that the rows fill in as elimination proceeds.

### 7.4 The frontier

A binary heap of `(monomial, generator)` ordered by lex **increasing**, where `generator` is the
`(variable, accepted index)` the candidate was produced from, or none for `1`. Plus a
`HashSet<Monomial<N>>` of everything ever enqueued, so no candidate is visited twice. Bounded by
`1 + N*D` entries as §5.5 shows.

Lex increasing needs a wrapper with `Ord` delegating to `MonomialOrder::cmp` and reversed, since
`Monomial<N>` has no intrinsic order and `BinaryHeap` is a max-heap.

---

## 8. Errors and resource limits

```rust
pub struct FglmOptions {
    /// Standard monomials enumerated before `QuotientDimensionExceeded`.
    pub max_quotient_dimension: usize,
    /// Stored multiplication-operator entries allowed, summed over all N operators.
    pub max_operator_entries: usize,
    /// Span rows x columns allowed, which bounds the dependence test's storage.
    pub max_span_entries: usize,
}

pub enum FglmError {
    /// The source ideal is positive-dimensional, so R/I is infinite and FGLM does not apply.
    PositiveDimensional,
    /// Enumeration passed the limit. Carries only the limit: it stops at the first crossing, so
    /// any count it reported would be the limit plus one.
    QuotientDimensionExceeded { limit: usize },
    /// The operators needed more entries than allowed. Carries the count, which is informative:
    /// it is known before the allocation, from the columns already built.
    OperatorStorageExceeded { entries: usize, limit: usize },
    /// The span needed more entries than allowed. Carries the count, computed from D up front.
    SpanStorageExceeded { entries: usize, limit: usize },
    /// A normal form had a term outside the standard monomials, or the accepted count disagreed
    /// with D. Either means the input was not a Gröbner basis under the stated order.
    NotAGrobnerBasis,
    /// The options cannot be satisfied by any computation.
    InvalidOptions { reason: &'static str },
}

pub enum SolveError {
    /// The system is not zero-dimensional. Use `grobner::solve` for those.
    PositiveDimensional,
    /// The Gröbner basis computation crossed one of its limits.
    Grobner(F4Error),
    /// The conversion crossed one of its limits.
    Fglm(FglmError),
    /// The search explored `limit` partial assignments without exhausting the tree.
    TooManyBranches { limit: usize },
    /// More distinct solutions exist than the caller allowed. Carries the limit; the list is not
    /// returned, because a truncated list that looks complete is worse than an error.
    TooManySolutions { limit: usize },
    InvalidOptions { reason: &'static str },
}
```

Proposed defaults, and where each number comes from:

| option | default | reasoning |
|---|---|---|
| `max_quotient_dimension` | 4,096 | 26x the largest `D` in the corpus (cyclic-6's 156). The enumeration itself is cheap at any such `D` — 4,096 monomials of eight `u32`s is 131 KB — so this limit exists to stop a walk that should not have started, and the operator budget is what bounds memory. |
| `max_operator_entries` | 20,000,000 | ≈ 320 MB at 16 bytes, the same figure and accounting as `F4Options::max_live_nonzeros`. With the measured fills of §7.2 and N = 8 it binds at **`D ≈ 2,100` on a katsura-shaped staircase, `D ≈ 5,300` on a cyclic-shaped one, and `D ≈ 27,000` on a planted one**. So which of the two limits fires first depends on the shape, which is why both exist. |
| `max_span_entries` | 20,000,000 | As above, `2 * D^2` entries, reached at `D ≈ 3,160`. Checked before the span is allocated rather than as it fills. |
| `max_branches` | `None` | A zero-dimensional system's search tree is finite. A limit here is for a caller with a latency budget, not for termination. |
| `max_solutions` | `None` | As above: bounded by D. |

Enforcement rules, in order of importance:

1. **Classify before enumerating.** A positive-dimensional ideal makes the frontier walk
   non-terminating, so it is rejected by §5.1 before §5.2 runs, not by a budget during it.
2. **Check products before allocating.** `D^2`, `N * D^2` and `rows * columns` are `usize`
   multiplications that can wrap on a 32-bit target and can exceed memory on any target.
   `checked_mul` and a comparison against the budget precede every allocation of that size.
3. **An exceeded budget is an error, never a partial result.** There is no `FglmError` variant for
   "converted but incomplete", exactly as there is none in `F4Error`.
4. **Representation limits are not process-memory limits.** `max_operator_entries` bounds the
   entries M17 stores. It says nothing about the allocator's overhead or about F4's own peak during
   the source-basis computation, and the documentation must not imply otherwise.
5. **F4's limits are not duplicated.** `SolveOptions` holds an `F4Options` and an `FglmOptions`
   rather than re-declaring matrix bounds.

---

## 9. Test corpus

Mandatory cases. "Exhaustive" means enumerate `F_q^N` and evaluate the original generators, which
is only affordable for small `q` and `N` and is the strongest oracle available there.

| case | expected |
|---|---|
| `<1>` — e.g. `{x, x - 1}` | unit, D = 0, lex basis `{1}`, `solve_one` = `Ok(None)` |
| `{x^d - 1}` in one variable | D = d |
| `<x^a, y^b>` | D = ab |
| `<x^2, y^2>` | D = 4, standard monomials exactly `{1, x, y, xy}`, one distinct point |
| `<x^2 - y, y^3 - 1>` | zero-dimensional, lex basis matches direct lex F4 |
| `<(x-1)^2, y - x>` | nonradical; the lex basis must keep `(x-1)^2`, not `x - 1` |
| `<xy - 1>` | `PositiveDimensional` |
| **cyclic-4** | `PositiveDimensional` — §3.1 |
| `{}` and `{0}` | `PositiveDimensional` for N >= 1 |
| `x^2 + 1` over GF(3) | zero-dimensional, D = 2, `solve_one` = `Ok(None)` |
| `x^2 + 1` over GF(5) | two distinct points |
| planted-4, -6, -8 | the planted point is among the solutions |
| several candidate roots, one valid branch | `solve_one` backtracks and finds it |
| D above `max_quotient_dimension` | `QuotientDimensionExceeded` |
| the same ideal from permuted generators | byte-identical reduced lex basis |
| GF(7), GF(13), GF(65537), GF(2^31 - 1) | identical algebraic results |

The nonradical cases carry the most weight. `<x^2, y^2>` has **one** distinct zero over the
algebraic closure and `D = 4`; a conversion that replaced `x^2` with `x` would pass every test that
only compares solution sets, and would be wrong. Multiplicity preservation is checked by comparing
the lex basis itself, not the points.

Oracles, in increasing order of independence:

1. **Defining properties.** Every emitted basis satisfies Buchberger's criterion, and ideal
   membership holds both ways: each source polynomial reduces to zero modulo the target basis and
   each target polynomial reduces to zero modulo the source basis. A reduced Gröbner basis is
   unique per ideal and order, so after canonical sorting the comparison is exact equality.
   *`grobner::is_grobner_basis` is this check, added by M17-C. It is public rather than in
   `test_support` because a caller validating input of unknown provenance needs it too.*
2. **Differential.** FGLM against direct lex `f4`, against `buchberger`, and against
   `buchberger_reference` on the small cases.
3. **Committed external values.** 29 lex bases from Singular, as literals, generated by
   `tools/reference_bases.sing`. **No external algebra system at CI runtime.** §9.1.
4. **Exhaustive search.** Already the pattern in `solve.rs`'s own tests, over GF(5), GF(7), GF(13).
5. **Planted witnesses.** Verified against the original generators, not against the basis.

### 9.1 The external oracle, and the one gap that remains

**Oracle 3 is satisfied.** 29 lexicographic bases computed by **Singular 4.4.1** are committed as
literals in `src/grobner/fglm/reference_bases.rs`, generated by `tools/reference_bases.sing` and
regenerable with one command. Singular's `std` is Buchberger/slimgb lineage, so these are
independent of Zeebra's F4 **in algorithm** and not merely in implementation — which a second F4
would not have been, since it would agree with Zeebra's partly because both implement F4.

The corpus: eleven two-variable systems, five three-variable (cyclic-3, katsura-3, a system not in
shape position, a nonradical one), two four-variable (katsura-4 and a planted system whose lex
basis has coefficients in the hundreds of millions), and ten repeats at GF(13) and GF(65537). All
29 agreed with Zeebra on the first run.

Three conventions were verified rather than assumed before any of it was generated, because each
would have silently corrupted every comparison:

- `lp` with variables declared `(x,y,...)` orders `x > y > ...`, matching Zeebra's
  `Lexicographic` with `parse(s, ["x","y",...])`. Checked on `<x*y-1, x-y>`, whose lex basis is
  `{x-y, y^2-1}` under `x > y` and `{y-x, x^2-1}` under `y > x`.
- `short=0` makes Singular print `x^2` and `2*x` rather than `x2` and `2x`; Zeebra's parser
  accepts the former only.
- Singular prints the symmetric coefficient representative, so `-y` rather than `2147483646*y`.

The generator also cross-checks each basis against Singular's **own `fglm`** — a third algorithm —
and emits a mismatch marker instead of the basis if the two disagree. That found a real problem on
first run: `fglm` requires a *reduced* standard basis as its source and silently fails without
`option(redSB)`, which cost two of the katsura entries until it was set.

**Singular cannot reach the fields that motivate this work.** Its characteristic must be a prime
below 2^31, so the largest field above is GF(2^31 - 1). Goldilocks (2^64 - 2^32 + 1), which Zeebra
already supports as `Zp18446744069414584321`, is out of reach, and so are the 254- and 255-bit
scalar fields of BN254 and BLS12-381. This is not a Singular quirk: msolve and giac share the 2^31
ceiling, for the same reason — 32-bit modular arithmetic with delayed reduction in 64-bit
accumulators is what makes them fast. Magma handles arbitrary prime fields and is not free.

So at cryptanalysis scale **no free external oracle exists**, and the assurance has to be
transferred rather than obtained. The staircase and the quotient dimension are properties of the
ideal, not of the prime; the arithmetic is what changes. The argument the test corpus makes is
therefore: Singular confirms the algebra at GF(13), GF(65537) and GF(2^31 - 1); Zeebra's own
cross-field tests confirm it gives the *same* quotient dimensions and bases at every prime it
supports, including ones Singular cannot; so a disagreement at Goldilocks would have to be a fault
in the field arithmetic rather than in the algebra, and the field arithmetic has its own property
tests. `test_the_quotient_dimension_is_the_same_at_every_prime` is that argument's first step,
made explicit.

**The gap that remains is the one the external oracle cannot close**: there is no independent
confirmation of any result at 64 bits or above. Closing it needs either a commercial system or a
second implementation in Zeebra's own terms.

**A non-Gröbner source gives a wrong answer, not an error.** The conversion works inside the
quotient that the source's leading monomials describe. If that is not `R/I`, the walk still accepts
exactly as many monomials as that space has dimensions, still finds dependences, and still emits a
basis — of the wrong ideal. The design proposed detecting this by checking that the accepted count
equals `D`; **that check cannot fire**, which was established by constructing four non-Gröbner
inputs with pure-power leading monomials in every variable and observing all four return `Ok` with
a basis that disagrees with direct lex F4. The check is now a `debug_assert` stating FGLM's theorem
rather than a validation, and `fglm_to_lex_checked` — which verifies Buchberger's criterion up
front — is the answer for input of unknown provenance. §10.2 prices it.

---

## 10. Baseline

`cargo run --release --example fglm_baseline`, GF(2^31 - 1), `F4Options::default()`, classical
Buchberger at `PairCriteria::ALL`, fastest of five runs. Rows print as they are measured, so the
hard instances can be run one per process.

`D` comes from `QuotientBasis::new`; `walk ms` is that enumeration, timed separately from the
basis it starts from. **The two engines' lex bases are asserted
equal wherever both ran.**

| system | ideal | D | grevlex ms | &#124;G&#124; | walk ms | lex f4 ms | &#124;G&#124; | lex bb ms | lex f4 / grevlex |
|---|---|---|---|---|---|---|---|---|---|
| cyclic-3 | zero-dim | 6 | 0.01 | 3 | 0.00 | 0.01 | 3 | 0.01 | 1.0x |
| cyclic-4 | **positive** | — | 0.07 | 7 | — | 0.06 | 6 | 0.10 | — |
| cyclic-5 | zero-dim | 70 | 1.51 | 20 | 0.03 | 2.59 | 11 | 4.07 | 1.7x |
| cyclic-6 | zero-dim | 156 | 13.48 | 45 | 0.09 | 298.75 | 17 | 384.10 | **22.2x** |
| katsura-3 | zero-dim | 4 | 0.02 | 4 | 0.00 | 0.02 | 3 | 0.02 | 1.0x |
| katsura-4 | zero-dim | 8 | 0.10 | 7 | 0.00 | 0.10 | 4 | 0.15 | 1.0x |
| katsura-5 | zero-dim | 16 | 0.53 | 13 | 0.01 | 0.73 | 5 | 32.59 | 1.4x |
| katsura-6 | zero-dim | 32 | 3.24 | 22 | 0.02 | 18.32 | 6 | — | 5.7x |
| katsura-7 | zero-dim | 64 | 30.54 | 41 | 0.05 | **does not finish** | — | — | **unbounded** |
| planted-4 | zero-dim | 16 | 0.02 | 6 | 0.01 | 0.02 | 4 | 0.03 | 1.0x |
| planted-6 | zero-dim | 64 | 0.03 | 9 | 0.03 | 0.03 | 6 | 0.04 | 1.0x |
| planted-8 | zero-dim | 256 | 0.05 | 12 | 0.13 | 0.05 | 8 | 0.07 | 1.0x |

"Does not finish" for katsura-7 under lex is `F4Error::TooManyNonzeros { nonzeros: 20003295,
limit: 20000000 }` — it crosses `max_live_nonzeros` and returns an error rather than a basis. And
the limit is not what is stopping it: raising `max_live_nonzeros` to 2 billion, a hundredfold, the
same computation was **still running after 13 minutes at 5.5 GB resident** and was abandoned
rather than completed. So katsura-7 under lex is out of reach of this F4 at any budget a
workstation will give it, not merely out of reach of the default one.

A dash under `lex bb ms` is M16 §8.3's finding that the classical engine does not complete the
instance in 900 s with every pair criterion enabled.

### 10.1 What the baseline says

**Eleven of the twelve instances are zero-dimensional, and the twelfth is cyclic-4.** §3.1 is the
correction; the measurement is the `positive` row above, and a test now asserts it.

**`D` is not predicted by the variable count, and it is the quantity that matters.** katsura-n has
`D = 2^(n-1)` exactly across the four sizes measured — 4, 8, 16, 32, 64 — the cyclic family has 6,
70 and 156, and the planted family has `4^(N/2)`: 16, 64, 256. planted-8 therefore has the
**largest** quotient algebra in the corpus while being the **cheapest** system in it under either
order.

**The conversion's budget, per instance, is the gap between the two basis costs.** That gap is
what FGLM gets to spend before it stops being worth doing, and with `O(N D^3)` field operations as
the estimate it divides the corpus into three:

| instance | headroom (lex f4 − grevlex f4) | `N * D^3` | verdict |
|---|---|---|---|
| katsura-7 | unbounded — lex does not finish | 1.8e6 | FGLM is the only route |
| cyclic-6 | 285 ms | 2.3e7 | FGLM should win |
| katsura-6 | 15.1 ms | 2.0e5 | FGLM should win easily |
| cyclic-5 | 1.1 ms | 2.1e6 | close; could go either way |
| planted-8 | 0.00 ms | 1.3e8 | **FGLM will lose, by orders of magnitude** |
| cyclic-3, katsura-3/4, planted-4/6 | ≈ 0 | small | no gain available |

These are predictions from an operation count, not measurements, and M17-E's job is to check them
rather than to repeat them. The one worth stating in advance is **planted-8**, because it is the
documented counterexample the milestone needs: `D = 256` against a direct lex basis that costs
50 microseconds. No conversion through a 256-dimensional quotient algebra competes with that, and
a milestone that only measured the instances FGLM wins would be hiding it. It is also why
`SolveStrategy` stays explicit in M17 — a heuristic keyed on variable count would pick FGLM for
planted-8, which is the worst available choice.

**katsura-7 is the milestone's central instance.** Its grevlex basis takes 30 ms and its quotient
algebra has dimension 64, so the seven operators hold 16,257 entries between them — 260 KB — and
the span is a 64-row, 128-column dense block. Everything FGLM needs is trivially small. The direct lex route, meanwhile, does not arrive at a hundredfold the default budget and
thirteen minutes. The milestone's case is not that FGLM is faster here but that **the direct route
does not arrive at all**.

**Standard monomial enumeration is free.** `walk ms` never exceeds 0.13 ms, and on cyclic-6 it is
0.09 ms against the 13.48 ms basis it starts from — 0.7%. There is no case for a cleverer
enumeration than §5.2's frontier walk, and M17-A should not build one.

**Buchberger is not the baseline to beat; lex F4 is.** The classical engine is slower than lex F4
on every paired instance here — 61x on katsura-5 — and cannot finish katsura-6 or katsura-7 at all.
`grobner::solve` nevertheless calls `buchberger`, so the honest statement of the opportunity is
that M17's new solver should be compared against lex F4, while the *existing* solver has a second,
independent speedup available to it that has nothing to do with FGLM. M16 §9.1 already records
this.

### 10.2 The conversion measured, end to end

`cargo run --release --example fglm_conversion`, GF(2^31 - 1), fastest of three, both bases
asserted equal wherever both exist. `pipeline` is `build + convert` — the grevlex basis plus the
conversion — against `lex f4`, which is what it replaces.

| system | D | build ms | algebra ms | convert ms | pipeline ms | lex f4 ms | pipeline vs direct | verify ms |
|---|---|---|---|---|---|---|---|---|
| cyclic-3 | 6 | 0.01 | 0.01 | 0.01 | 0.02 | 0.01 | 0.50x | 0.01 |
| cyclic-5 | 70 | 1.48 | 1.90 | 2.14 | 3.62 | 2.58 | 0.71x | 4.37 |
| cyclic-6 | 156 | 14.09 | 27.56 | 25.67 | 39.77 | 294.96 | **7.42x** | 130.89 |
| katsura-3 | 4 | 0.03 | 0.01 | 0.01 | 0.04 | 0.02 | 0.50x | 0.02 |
| katsura-4 | 8 | 0.11 | 0.06 | 0.07 | 0.18 | 0.11 | 0.61x | 0.15 |
| katsura-5 | 16 | 0.60 | 0.46 | 0.50 | 1.10 | 0.84 | 0.76x | 2.34 |
| katsura-6 | 32 | 3.66 | 3.43 | 3.60 | 7.26 | 18.23 | **2.51x** | 31.72 |
| katsura-7 | 64 | 29.97 | 36.23 | 38.13 | 68.10 | **no basis** | **unbounded** | 869.29 |
| planted-4 | 16 | 0.02 | 0.03 | 0.05 | 0.07 | 0.02 | 0.29x | 0.03 |
| planted-6 | 64 | 0.03 | 0.28 | 0.40 | 0.44 | 0.03 | 0.07x | 0.09 |
| planted-8 | 256 | 0.05 | 1.78 | 3.18 | 3.23 | 0.05 | **0.015x** | 0.20 |

`algebra` is the quotient-algebra construction, which `convert` **includes** rather than adds to.
`no basis` is `F4Error::TooManyNonzeros` at the default limit.

**The M17-0 predictions held, including the one about losing.** §10.1 predicted from an operation
count that FGLM would win on cyclic-6 and katsura-6, be the only route on katsura-7, be close on
cyclic-5, and lose by orders of magnitude on planted-8. The measurement: 7.4x, 2.5x, the only
route, 0.71x, and **0.015x — a 65x loss**. Three wins, eight losses, and the losses are not
marginal.

**katsura-7 is the result.** The whole pipeline takes 68 ms. Direct lex F4 returns no basis at the
default limit and does not finish at a hundredfold limit in thirteen minutes (§10). The quotient
algebra is 16,257 operator entries and the dependence test performs 2,335 row operations.

**The quotient-algebra construction dominates the conversion, not the linear algebra.** On
katsura-7 `algebra` is 36.2 ms of a 38.1 ms `convert`, so the frontier and the dependence test
together are about 2 ms — the 2,335 row operations touch roughly 300,000 field elements, which is
nothing. The cost is the `N * D` operator columns, each needing a `normal_form` against the source
basis for the 72% of products that leave the staircase. **So the thing to optimize in M17-E is
operator construction, and `O(N D^3)` is not where the time goes at these dimensions.** The
`O(N D^3)` term would dominate at larger `D`; it does not dominate anywhere in this corpus.

**cyclic-6's win is 7.4x, not the 22x its basis costs suggested.** §10's `lex f4 / grevlex` column
was 22.2x, but the conversion costs 25.7 ms on top of the 14.1 ms basis, so the pipeline is 39.8 ms
against 295 ms. The basis-cost ratio is an upper bound on the achievable speedup and not an
estimate of it.

**Verifying the source costs more than computing it.** 0.6x the basis computation on the smallest
instances and **27x on katsura-7** — 869 ms against a 30 ms basis and a 38 ms conversion. This is
what settles §8's open question about input validation in favour of a trusted default with an
explicit checked entry point: unconditional verification would cost an order of magnitude more than
the conversion it protects. §9.1 is the hazard that follows from that choice.

### 10.3 Solving, measured

`cargo run --release --example solve_one`, GF(2^31 - 1). `first` is time to one point, `all` to
every distinct point.

| system | route | first ms | all ms | result |
|---|---|---|---|---|
| planted-6 | direct | 0.88 | 6.42 | 64 points |
| planted-6 | fglm | 1.35 | 6.86 | 64 points |
| cyclic-3 | direct | 0.41 | 0.50 | 6 points |
| katsura-3 | direct | 0.32 | 0.35 | 4 points |
| katsura-4 | direct | 0.46 | 0.50 | 3 points |
| katsura-5 | direct | 2.14 | 1.97 | 5 points |
| katsura-6 | direct | 22.37 | 21.58 | 2 points |
| katsura-6 | fglm | **10.47** | **10.44** | 2 points |
| katsura-7 | direct | — | — | **no basis**: 20,003,295 live nonzeros over the 20,000,000 limit |
| katsura-7 | fglm | **82.80** | 82.26 | 5 points |
| planted-10 | direct | **1.23** | **100.77** | 1024 points |
| planted-10 | fglm | 34.93 | 135.48 | 1024 points |
| planted-12 | direct | **1.88** | **413.12** | 4096 points |
| planted-12 | fglm | — | — | **no conversion**: the span needs 33,554,432 entries over 20,000,000 |
| planted-14 | direct | **1.93** | **1602.98** | 16384 points |
| planted-14 | fglm | — | — | **no conversion**: quotient dimension over the 4,096 limit |

**Neither strategy dominates, and the failures are symmetric.** katsura-7 is solvable only by
conversion; **planted-12 and planted-14 are solvable only directly**, because their quotient
algebras have dimension 4096 and 16384 while their lex bases are trivial. Each route has a system
at a comparable size that the other cannot do at the default limits. That is a stronger argument
for keeping `SolveStrategy` explicit than §10.2's timing spread was, and it is why no heuristic is
proposed: a heuristic would have to predict which *resource* runs out, not which is faster.

`DirectLexF4` is the default because it is the conservative choice — it is what `solve` already
does — and **not** because it is uniformly better. It is slower than conversion on katsura-6, by
2.1x, which agrees with §10.2's 2.5x on the basis alone.

**Time to one solution is nearly independent of how many there are.** It is dominated by the
Gröbner basis; the search itself is almost free. Time to *all* solutions scales with the count, and
the gap is the entire case for a separate `solve_one`:

| system | points | first ms | all ms | ratio |
|---|---|---|---|---|
| katsura-6 | 2 | 22.37 | 21.58 | 1.0x |
| planted-6 | 64 | 0.88 | 6.42 | 7x |
| planted-10 | 1024 | 1.23 | 100.77 | 82x |
| planted-12 | 4096 | 1.88 | 413.12 | 220x |
| planted-14 | 16384 | 1.93 | 1602.98 | **830x** |

So `solve_one` is not a convenience wrapper over `solve_zero_dimensional`; on a system with many
solutions it is three orders of magnitude cheaper, and `first ms` barely moves across four
instances whose solution counts span 256x.

A smaller observation worth recording: the planted family's solution count **equals** its quotient
dimension, `4^(N/2)` — 64, 1024, 4096, 16384. So those ideals are radical and every zero is
rational, which is why they are a good witness corpus and a poor multiplicity corpus. The
nonradical cases in §9 carry that part.

### 10.4 Branch counts, which say it without a clock

`SolveStatistics::branches` counts candidate assignments tried. From the same run:

| system | N | points | branches for one | branches for all |
|---|---|---|---|---|
| katsura-3 | 3 | 4 | 3 | 12 |
| cyclic-3 | 3 | 6 | 3 | 15 |
| katsura-6 | 6 | 2 | 6 | 12 |
| katsura-7 | 7 | 5 | 7 | 35 |
| planted-6 | 6 | 64 | 6 | 168 |
| planted-10 | 10 | 1024 | 10 | 2,728 |
| planted-12 | 12 | 4096 | 12 | 10,920 |
| planted-14 | 14 | 16384 | 14 | 43,688 |

**Finding one solution costs exactly `N` branches on every instance in the corpus, and finding all
of them costs about 2.7 times the solution count.** So the search's own cost for one point is
linear in the variable count and *independent of how many solutions exist* — which is the same
conclusion §10.3 reached from the clock, obtained without timing anything.

One honest consequence: `N` branches means **no backtracking happened on any corpus instance** —
the first candidate at every level extended to a full point every time. Backtracking is exercised
by a constructed case instead, `<y^2 - 1, x^2 - y - 1>` over GF(5), where `y = 1` leads to
`x^2 = 2` with no root in the field. The corpus does not happen to contain a system that needs it,
and saying so is better than implying the 14 above is evidence that it works.

---

## 11. Sub-milestones and merge gates

| PR | content | gate | status |
|---|---|---|---|
| M17-0 | this document, the corrected `benchmark_systems` doc comment, `examples/fglm_baseline.rs` | design reviewed, baseline reproducible | **merged**, `31b72c9` |
| M17-1 | `classify_ideal`, `QuotientBasis` | correct classification on §9's cases, bounded enumeration | **done** |
| M17-2 | `QuotientAlgebra`, `MultiplicationOperator` | operators commute, generators vanish, columns agree with normal forms | **done** |
| M17-3 | `IncrementalSpan`, `fglm_to_lex` | exact equality with direct lex F4 and with the committed external bases | **done** — 29 Singular bases, §9.1 |
| M17-4 | `solve_one`, `solve_zero_dimensional` | exhaustive-search and planted-witness agreement, budgets enforced | **done** — §10.3 |
| M17-5 | benchmarks and the milestone report | measurements reproducible, §12 satisfied | **done** — §12, §14 |

Each PR compiles and tests independently. The order is forced by the mathematics: each stage
establishes the invariant the next one assumes.

Benchmark harness work, the external reference literals, and the `test_support` Gröbner-basis
verifier can proceed in parallel once this document is approved.

---

## 12. Acceptance criteria

Each criterion from M17-0, with where it is met or why it is not.

### Mathematical correctness

- [x] **Classification correct on every case in §9**, unit ideal and zero ideal included.
      `classify_ideal`, tested across all three orders.
- [x] **Standard monomials are the quotient basis**, deterministic and bounded. Also checked to be
      closed downwards, and `D` checked to be independent of the monomial order — a real
      cross-check, since the monomial *sets* differ between lex and grevlex.
- [x] **Operators agree with normal forms and commute.** Each column compared against an
      independently computed `normal_form`, not against `coordinates`, which would reuse the same
      reduction.
- [x] **Dependence coefficients verified by reconstruction**, on every reported dependence, and the
      rank compared against textbook dense Gaussian elimination.
- [x] **FGLM preserves the ideal**, checked in both directions by reduction as well as by equality
      of reduced bases.
- [x] **Multiplicities preserved.** `<x^2, y^2>` converts to `{x^2, y^2}` and explicitly not to
      `{x, y}`; `T_x` is nonzero and nilpotent, so the nonradical structure survives in the
      operators too.
- [x] **Output is the unique reduced lex basis**, with monicity and reducedness asserted term by
      term — and **no interreduction pass**, for the reason argued in §5.5.
- [x] **Agrees with direct lex F4** from all three source orders, with `buchberger`, with the naive
      `buchberger_reference`, and with **29 Singular bases** (§9.1).
- [x] **Positive-dimensional input rejected before any unbounded enumeration**, cyclic-4 included.

### Solving

- [x] **`solve_one` finds a point when one exists**, and **backtracks** when it must (§10.4 names
      the constructed case, since the corpus does not need it).
- [x] **`Ok(None)` and `Err` are never confused.** `x^2 + 1` over GF(3) is zero-dimensional with
      quotient dimension two and no base-field point, and that is `Ok(None)`.
- [x] **All-solutions is complete or an error**, never truncated.
- [x] **Points verified against the original generators**, not against any basis derived from them.
- [x] **`grobner::solve` unchanged** — signature, semantics, and its panic on a free variable over a
      large field — with a test that the two agree on zero-dimensional systems.
- [x] **Every new entry point bounded**, and each budget tested as a structured error.

### Engineering

- [x] Stable Rust. F4 and Buchberger APIs untouched. Polynomial representation unchanged.
- [x] **No external algebra system at CI runtime.** Singular is a development-time tool; its output
      is committed as literals and regenerable with one command.
- [x] Fast tests in ordinary CI; the release job runs the same suite in release.
- [x] `cargo fmt --all --check` and `cargo clippy --all-targets --all-features -- -D warnings`
      clean.
- [ ] **Not met: there is no independent confirmation above 2^31.** Singular's characteristic must
      be a prime below 2^31, and msolve and giac share that ceiling. §9.1 states what the corpus
      can and cannot transfer.

### Performance

- [x] **All three pipelines measured on identical inputs** — lex Buchberger (§10), lex F4, and
      grevlex F4 plus FGLM (§10.2) — with the bases asserted equal wherever both exist.
- [x] **Conversion timed separately from basis computation**, and its stages separately again,
      which is how the quotient-algebra construction was found to dominate.
- [x] **`D`, operator storage, and linear-algebra counts recorded**, in `FglmStatistics` and in
      `examples/fglm_operators`.
- [x] **Time to first solution and to all solutions reported separately** (§10.3), and the branch
      counts behind them (§10.4).
- [x] **Cases where FGLM loses are documented** — eight of eleven instances in §10.2, by up to 65x,
      and two systems it cannot convert at all in §10.3.
- [x] Resource-limit behaviour verified for every option.
- [ ] **Partly met: memory is estimated, not measured.** `FglmStatistics::estimated_bytes` reports
      what the conversion stores; process memory is not instrumented, exactly as M16 reported peak
      live nonzeros rather than RSS. §8's distinction between representation limits and memory
      limits is the reason, not an excuse — but it does mean no figure here bounds what a
      conversion will actually cost a machine.

## 13. Risks

| risk | mitigation |
|---|---|
| FGLM silently accepts a non-Gröbner input and returns a plausible wrong basis | `NotAGrobnerBasis` from the two internal consistency checks of §8, plus `fglm_to_lex_checked` for external input. Both engines in this crate satisfy the precondition by construction. |
| `D` grows beyond memory | Classify first, then bound the enumeration, then check the storage products before allocating. §8. |
| Wrong dependence coefficients | Reconstruct and compare on every reported dependence in debug builds; differential test against dense elimination on small cases. |
| An implementation assumes radicality or shape position | §9's nonradical cases, compared on the **basis** and not on the solution set. |
| grevlex + FGLM is slower than direct lex F4 | Measured both ways; `SolveStrategy` stays explicit. No automatic heuristic in M17. |
| The new solver changes legacy semantics | `solve` is untouched and separately tested; the new API is a different module. |
| Root finding becomes the bottleneck | Measured as its own stage. §2.5 establishes it needs no rewrite for correctness or failure semantics. |

---

## 14. Definition of done, and what to do next

Zeebra can take a zero-dimensional polynomial system over a supported finite field and return a
verified solution, by either of two routes, under budgets that fail with a structured error rather
than a panic or a partial answer. The conversion agrees with direct lex F4, with both classical
engines, and with 29 bases from an independent computer-algebra system. **That is the milestone.**

The result worth quoting is **katsura-7**: 68 ms for the conversion pipeline and 91 ms to a
verified solution, where direct lex F4 returns no basis at its default limit and does not finish at
a hundredfold limit in thirteen minutes. The milestone's value is a capability, not a speedup — on
eight of eleven instances the direct route is faster, by up to 65x.

### 14.1 Known limitations

- **The quotient-algebra construction dominates the conversion**, not the linear algebra: 36 ms of
  katsura-7's 38 ms. The `O(N D^3)` term that the design was budgeted around does not dominate
  anywhere in this corpus.
- **The sparse operator representation does not pay on the katsura family.** 56–59% fill at 16
  bytes an entry against 8 bytes a dense cell, so a dense matrix would be smaller there, while on
  planted-8 the sparse form wins by 146x. No per-operator choice is made.
- **No independent oracle above 2^31**, and no free system can provide one. §9.1.
- **`fglm_to_lex` returns a wrong basis, not an error, on a non-Gröbner input.** Verification costs
  0.6x to 27x what computing the basis cost, so it is opt-in. §9.1.
- **No automatic strategy selection**, and §10.3 is the reason: each route has a system at a
  comparable size the other cannot do, so a heuristic would have to predict which *resource* runs
  out.
- **`grobner::solve` still uses `buchberger`** and still has no `Result`. M16 §9.1 recorded this and
  it is unchanged; the new entry points are a separate API rather than a migration.
- **Single-threaded**, like everything else in the crate.
- **No 128-bit field measurement**, unchanged from M15 and M16.
- **`N` is still a const generic.**
- **The corpus does not exercise backtracking.** §10.4.

### 14.2 Recommendations for the next milestone, in the order the measurements support

1. **Operator construction**, which is 95% of the conversion on katsura-7. The cost is `N * D`
   columns, 72% of which need a `normal_form` against the source basis. Reducing many monomials
   against one basis at once is the shape F4 already exploits for its Macaulay matrices, and
   nothing here does.
2. **A dense or hybrid operator column**, chosen per operator from the measured fill. §7.2 has the
   evidence and deliberately does not act on it.
3. **A strategy heuristic keyed on `D`**, which is now cheap to obtain — a grevlex basis plus the
   standard monomial walk is under 1% of the conversion. The open question is not whether `D`
   predicts the winner but whether it predicts *reachability*, which is what §10.3 showed matters.
4. **Give `solve` the criteria, then switch it to F4.** Still the cheap half of M16 §9.2's third
   recommendation, still untouched, and now with a fallible sibling to migrate toward.
5. **Sparse FGLM**, Faugère and Mou (2017), which exploits the structure of the multiplication
   matrices rather than treating them as dense maps. Out of scope for M17 by design, and the
   natural successor once operator construction is faster.
6. **Larger prime fields**, where the project's longer-term workloads live and where no external
   oracle exists.

## 15. References

1. Faugère, J.-C., Gianni, P., Lazard, D., Mora, T. (1993). *Efficient Computation of
   Zero-dimensional Gröbner Bases by Change of Ordering.* Journal of Symbolic Computation 16(4),
   329–344. <https://doi.org/10.1006/jsco.1993.1051>
2. Cox, D., Little, J., O'Shea, D. *Ideals, Varieties, and Algorithms*, Ch. 2 §2.2 and Ch. 5 for
   the finiteness theorem, standard monomials, and the quotient algebra.
3. Faugère, J.-C., Mou, C. (2017). *Sparse FGLM algorithms.* Journal of Symbolic Computation 80,
   538–569. <https://doi.org/10.1016/j.jsc.2016.07.025> — out of scope for M17.
4. Macaulay2, *FGLM — Compute Gröbner bases via the FGLM algorithm.*
   <https://macaulay2.com/doc/Macaulay2-1.25.05/share/doc/Macaulay2/FGLM/html/index.html>
5. Singular 4.4.1, <https://www.singular.uni-kl.de/> — the reference bases of §9.1, generated by
   `tools/reference_bases.sing`. Read as an oracle only; no code is taken from it.
6. The preceding milestones: [`MILESTONE-F4.md`](MILESTONE-F4.md) and
   [`MILESTONE-F4-OPTIMIZATION.md`](MILESTONE-F4-OPTIMIZATION.md), whose §9.2 ranks FGLM fourth
   among the next milestone's candidates and explains why grevlex becoming F4's best order made it
   more attractive than it was.

Published algorithm descriptions are the primary references. Existing implementations are read for
architecture only, under their own licenses; no code is copied.
