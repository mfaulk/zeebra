# Milestone: FGLM and Zero-Dimensional Polynomial-System Solving

**Status:** M17-0 complete — design approved against the merged M16 code, baseline measured.
**Prerequisite:** M16 on `main` at `494c16e`, CI green. Satisfied.

This document is the M17-0 deliverable: the mathematical design, the API contracts, the resource
semantics, the test corpus, and the measured baseline the implementation will be judged against.
It is written against the code as merged, not against the proposal — §3 records where the two
differ.

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

- **cyclic-6**: grevlex in 12.6 ms, lex in 288 ms with F4 and 378 ms with Buchberger. The source
  basis costs **23x less** than the target one, and the quotient algebra it has to be converted
  through has dimension 156.
- **katsura-7**: grevlex in 29.4 ms, and **lex does not finish at all** at the default limits — it
  crosses `max_live_nonzeros` at 20,003,295 live entries. Its quotient algebra has dimension
  **64**, so the entire conversion fits in well under a megabyte.

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

Cost: `O(D * N * |G|)` divisibility tests of `N` comparisons each. §10 measures it at 0.08 ms for
cyclic-6's `D = 156`, against 12.6 ms for the basis it starts from — under 1%, so there is no case
for a cleverer enumeration.

### 5.3 Multiplication operators — M17-B

```text
operator(i, B, G, order):
    for j in 0..|B|:
        p <- normal_form(x_i * B[j], G, order)
        column[j] <- coordinates(p, B)
```

`coordinates` maps each monomial of the normal form to its index in `B`. **A nonzero term whose
monomial is not in `B` is an internal inconsistency** — either the input was not a Gröbner basis or
`B` is not the standard monomial set — and must be an error, never a silently dropped term.

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
    pub fn monomials(&self) -> &[Monomial<N>];
    pub fn index_of(&self, monomial: &Monomial<N>) -> Option<usize>;
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

    /// The coordinate vector of a polynomial's residue class.
    pub fn coordinates(&self, p: &MultivariatePolynomial<N, F>) -> Result<Vec<F>, FglmError>;

    /// The normal form a coordinate vector represents. Inverse of `coordinates`.
    pub fn polynomial(&self, v: &[F]) -> MultivariatePolynomial<N, F>;

    /// T_i as a matrix, for the commutation and vanishing tests. Columns, in basis index order.
    pub fn operator(&self, variable: usize) -> &MultiplicationOperator<F>;
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
/// Every S-polynomial of the input is reduced against it and must vanish. That costs what a
/// Buchberger pass costs, which is why it is a separate entry point rather than the default.
pub fn fglm_to_lex_checked<const N: usize, F: FiniteField>(
    source_basis: &[MultivariatePolynomial<N, F>],
    source_order: MonomialOrder,
) -> Result<Vec<MultivariatePolynomial<N, F>>, FglmError>;
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

The split is not a premature optimization, it is the shape of the object: `x_i * b_j` is standard
for most `(i, j)`, since the staircase is closed downwards and only its outer surface leaves it
under multiplication. A dense `D x D` matrix per variable would store `N * D^2` field elements
where the great majority are structurally zero.

Storage, at 8 bytes per `PrimeFieldElement64` and 16 bytes per `(usize, F)` entry:

| D | dense, N = 8 | sparse, N = 8, at 10% fill |
|---|---|---|
| 64 | 262 KB | 52 KB |
| 156 | 1.6 MB | 312 KB |
| 1,024 | 67 MB | 13 MB |
| 4,096 | 1.07 GB | 215 MB |

So the operators are what sets the ceiling on `D`, not the span of §7.3, and `max_operator_entries`
counts entries rather than bytes for the same reason `F4Options::max_live_nonzeros` does.

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
| `max_quotient_dimension` | 4,096 | §7.2: 215 MB of operators at 10% fill with N = 8, 1.07 GB dense. 26x the largest D in the corpus (156). |
| `max_operator_entries` | 20,000,000 | ≈ 320 MB at 16 bytes, the same figure and the same accounting as `F4Options::max_live_nonzeros`. |
| `max_span_entries` | 20,000,000 | As above. Reached at `D ≈ 3,160`, so it binds slightly before `max_quotient_dimension` does — deliberately, since the span is allocated before the conversion runs. |
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
   *Note: the crate has no "is a Gröbner basis" helper today. M17-C adds one to `test_support`.*
2. **Differential.** FGLM against direct lex `f4`, against `buchberger`, and against
   `buchberger_reference` on the small cases.
3. **Committed external values.** Selected lex bases from SageMath, Singular, or Groebner.jl, as
   literals. **No external algebra system at CI runtime.**
4. **Exhaustive search.** Already the pattern in `solve.rs`'s own tests, over GF(5), GF(7), GF(13).
5. **Planted witnesses.** Verified against the original generators, not against the basis.

---

## 10. Baseline

`cargo run --release --example fglm_baseline`, GF(2^31 - 1), `F4Options::default()`, classical
Buchberger at `PairCriteria::ALL`, fastest of five runs. Rows print as they are measured, so the
hard instances can be run one per process.

`D` is computed by the frontier walk of §5.2, which M17-A moves into the library; `walk ms` is that
walk, timed separately from the basis it starts from. **The two engines' lex bases are asserted
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
algebra has dimension 64, so the operators are 7 columns-sets of at most 64 entries each — tens of
kilobytes — and the span is a 64-row, 128-column dense block. Everything FGLM needs is trivially
small. The direct lex route, meanwhile, does not arrive at a hundredfold the default budget and
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

---

## 11. Sub-milestones and merge gates

| PR | content | gate |
|---|---|---|
| M17-0 | this document, the corrected `benchmark_systems` doc comment, `examples/fglm_baseline.rs` | design reviewed, baseline reproducible |
| M17-1 | `classify_ideal`, `QuotientBasis` | correct classification on §9's cases, bounded enumeration |
| M17-2 | `QuotientAlgebra`, `MultiplicationOperator` | operators commute, generators vanish, columns agree with normal forms |
| M17-3 | `IncrementalSpan`, `fglm_to_lex` | exact equality with direct lex F4 and with the committed external bases |
| M17-4 | `solve_one`, `solve_zero_dimensional` | exhaustive-search and planted-witness agreement, budgets enforced |
| M17-5 | benchmarks and the milestone report | measurements reproducible, §12 satisfied |

Each PR compiles and tests independently. The order is forced by the mathematics: each stage
establishes the invariant the next one assumes.

Benchmark harness work, the external reference literals, and the `test_support` Gröbner-basis
verifier can proceed in parallel once this document is approved.

---

## 12. Acceptance criteria

**Correctness.** Classification correct on every case in §9, including the unit ideal and the zero
ideal. Standard monomials are the quotient basis, deterministic, and bounded. Operators agree with
normal forms and commute. Dependence coefficients verified by reconstruction. FGLM preserves the
ideal in both directions and preserves multiplicities. Output is the unique reduced lex basis.
Positive-dimensional input is rejected before any unbounded enumeration.

**Solving.** `solve_one` finds a point when one exists and backtracks when it must. `Ok(None)` and
`Err` are never confused. All-solutions is complete or an error, never truncated. Points verified
against the original generators. `grobner::solve` unchanged. Every new entry point bounded.

**Engineering.** Stable Rust. F4 and Buchberger APIs untouched. Polynomial representation
unchanged. No external algebra system in CI. Fast tests in ordinary CI, the heavy differential
comparisons in the release job. `cargo fmt --check` and `cargo clippy --all-targets --all-features`
clean.

**Performance.** All three pipelines measured on identical inputs: lex Buchberger, lex F4, and
grevlex F4 plus FGLM. Conversion timed separately from basis computation. `D`, operator storage and
linear-algebra counts recorded. Time to first solution and to all solutions reported separately.
**Cases where FGLM loses are documented rather than omitted** — a universal speedup is not the
criterion and will not be obtained. Resource-limit behaviour verified.

---

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

## 14. References

1. Faugère, J.-C., Gianni, P., Lazard, D., Mora, T. (1993). *Efficient Computation of
   Zero-dimensional Gröbner Bases by Change of Ordering.* Journal of Symbolic Computation 16(4),
   329–344. <https://doi.org/10.1006/jsco.1993.1051>
2. Cox, D., Little, J., O'Shea, D. *Ideals, Varieties, and Algorithms*, Ch. 2 §2.2 and Ch. 5 for
   the finiteness theorem, standard monomials, and the quotient algebra.
3. Faugère, J.-C., Mou, C. (2017). *Sparse FGLM algorithms.* Journal of Symbolic Computation 80,
   538–569. <https://doi.org/10.1016/j.jsc.2016.07.025> — out of scope for M17.
4. Macaulay2, *FGLM — Compute Gröbner bases via the FGLM algorithm.*
   <https://macaulay2.com/doc/Macaulay2-1.25.05/share/doc/Macaulay2/FGLM/html/index.html>
5. The preceding milestones: [`MILESTONE-F4.md`](MILESTONE-F4.md) and
   [`MILESTONE-F4-OPTIMIZATION.md`](MILESTONE-F4-OPTIMIZATION.md), whose §9.2 ranks FGLM fourth
   among the next milestone's candidates and explains why grevlex becoming F4's best order made it
   more attractive than it was.

Published algorithm descriptions are the primary references. Existing implementations are read for
architecture only, under their own licenses; no code is copied.
