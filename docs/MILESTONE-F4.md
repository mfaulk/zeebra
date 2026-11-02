# Milestone: Sparse Linear Algebra and F4 Gröbner Bases

Status: in progress. Baseline commit `9d7f3d9` (tree-identical to `main` at `bf73532`, the merge of
PR #14), 537 tests passing.

The primary deliverable is a **correct, benchmarked F4 implementation**, not an optimized one.
Buchberger reduces one S-polynomial at a time and discards most of the work: on katsura-5 under
grevlex, 39 of 49 reductions produce zero, and under lex 1725 of 1790 do. F4 replaces those
individual reductions with batched symbolic preprocessing plus one finite-field linear algebra
problem per batch, so the cancellations that Buchberger pays full price to discover become row
operations shared across a whole batch.

Everything here is guided by the architecture, not by any application: `buchberger` stays, the
public polynomial representation stays, `N` stays a const generic, and F4 is added alongside.

## 1. Objective

Zeebra is successful at this milestone if it can

1. construct Macaulay matrices from batches of critical pairs,
2. perform deterministic sparse finite-field row reduction,
3. extract valid new basis elements from the reduced matrices,
4. repeat until the critical-pair queue is empty,
5. produce the same reduced Gröbner basis as `buchberger` and `buchberger_reference`, and
6. report measured scaling behaviour against Buchberger on progressively harder systems.

F4 being *slower* than Buchberger on small systems is an acceptable outcome. Being *wrong* is not,
and neither is returning a partial basis as though it were complete.

## 2. Scope

### In scope

Sparse finite-field matrix representation and elimination; deterministic monomial-to-column
mapping; symbolic preprocessing; Macaulay matrix construction; batch reduction and candidate
extraction; integration with the critical-pair queue; final interreduction; F4-specific
instrumentation; resource limits as explicit errors; tests against independent oracles;
benchmarks against Buchberger; documentation.

### Out of scope

F5 and signature-based algorithms; FGLM and order conversion; cryptanalysis; GPU, threads, and
distribution; prime fields beyond 128 bits; redesigning `SparseMultiPoly<N, F>`; replacing
`const N: usize`; the chain criterion and Gebauer–Möller; dense/sparse hybrid strategies;
competing with Singular, msolve, or Groebner.jl.

The code should not *preclude* these. It should not contain them.

### Architectural decisions

| Decision | Reason |
|---|---|
| Keep `const N: usize` | F4 does not need a runtime variable count. The matrix has runtime dimensions; its columns are still labelled `Monomial<N>`. |
| Keep `buchberger` and `buchberger_reference` unchanged in behaviour | They are the correctness oracles for F4. Changing them would remove the thing F4 is checked against. |
| Stay generic over `FiniteField` | Specializing for one modulus is an M16 question, and would need measurements this milestone produces. |
| A new sparse backend, not `Matrix<T>` | Elimination on a dense `Matrix<T>` over an F4-shaped matrix (thousands of columns, a few percent dense) is the wrong cost. The dense implementation stays as the test oracle. |
| Determinism everywhere | Pair selection, reducer choice, pivot choice, candidate ordering, and basis output are all a function of the input and the order. Reproducibility is what makes the benchmarks and the oracle comparisons meaningful. |
| Resource exhaustion is a return value | F4 matrices can grow without warning. Exceeding a limit is an `F4Error`, never a truncated basis. |

## 3. Algorithm

```text
generators
  -> drop zeros and duplicates, make monic                     f4()
  -> seed the critical-pair queue                              grobner::pairs
  -> loop while pairs remain:
       select the batch of minimum lcm degree                  PairQueue::select_batch
       drop pairs by the product criterion
       symbolic preprocessing: pair multiples + reducer closure f4::symbolic
       build the sparse Macaulay matrix                        f4::macaulay
       sparse row echelon reduction                            linalg::sparse
       extract rows with new leading monomials                 f4::reduction
       append to the basis, enqueue their pairs
  -> minimize and interreduce                                  reduce_grobner_basis
  -> canonical reduced basis, descending by leading monomial
```

### 3.1 Source organization

```text
src/linalg/sparse/
  mod.rs            SparseRow, SparseMatrix, row_echelon, EliminationStatistics
  row.rs            the sorted-unique-nonzero row and its arithmetic
  matrix.rs         a vector of rows plus a column count
  elimination.rs    deterministic row echelon and reduced row echelon

src/grobner/
  pairs.rs          CriticalPair, PairQueue — shared with buchberger
  f4/
    mod.rs          f4, f4_with_options, F4Options, F4Error
    symbolic.rs     pair multiples and the reducer-multiple closure
    macaulay.rs     monomial-to-column mapping and matrix construction
    reduction.rs    reduce_batch and candidate extraction
    statistics.rs   F4Statistics
```

### 3.2 Sparse rows

```rust
struct SparseRow<F: FiniteField> {
    entries: Vec<(usize, F)>,
}
```

Invariants, which every operation preserves and `debug_assert`s check:

- column indices strictly increasing,
- no duplicate columns,
- no zero coefficients,
- an empty row is the zero vector.

A compressed sorted vector, not a `HashMap` per row: elimination merges two rows end to end, which
a sorted vector does in one linear pass with sequential memory access, and iteration order comes
free. `SparseMatrix` is a `Vec<SparseRow<F>>` plus a column count — not CSR, because elimination
changes every row's sparsity and CSR would have to be rebuilt.

Operations: scale by a nonzero element, subtract a scalar multiple of another row (two-pointer
merge into a reused scratch buffer), leading column, normalize the pivot to one, eliminate a
column using a pivot row, test for zero.

**One inverse per pivot**, not one per eliminated entry. This is the same mistake the dense
implementation made before PR #14 (defect C5 of the previous milestone); the sparse implementation
must not reintroduce it.

### 3.3 Row echelon form

Deterministic elimination, driven by a column-to-pivot-row map:

```text
for each row i, in index order:
    loop:
        c = leading column of row i, or stop if the row is zero
        if some row p is already the pivot for column c:
            row i -= row i[c] * row p
        else:
            normalize row i so its pivot is one; record it as the pivot for c; stop
```

Each surviving row ends with a distinct leading column and a unit pivot, and every row processed
after a pivot was recorded has a zero in that pivot's column. Sorting the nonzero rows by leading
column therefore yields a genuine row echelon form, and the zero rows are exactly the linear
dependencies in the batch. Taking rows in index order and columns leftmost-first makes the result
a function of the input alone.

Reduced row echelon form needs a second pass that eliminates each pivot column from the rows above
it, in decreasing column order. F4 does not need it — a candidate's leading monomial is all that
candidate extraction reads — so it is a separate function, computed only when asked. The
correctness tests ask for it, because the dense oracle produces RREF.

### 3.4 Symbolic preprocessing

For a critical pair `(f, g)` with `m = lcm(LM(f), LM(g))`, F4 puts **both** multiples

```text
(m / LT(f)) * f        and        (m / LT(g)) * g
```

into the matrix rather than their difference. The S-polynomial is their difference, so elimination
recovers it; keeping the halves separate is what lets one matrix cancel across the whole batch.

A row is then nothing more than a multiplier and a basis index:

```rust
struct PreprocessedRow<const N: usize> {
    multiplier: Monomial<N>,
    basis_index: usize,
    kind: RowKind,          // PairComponent or Reducer
}
```

Storing `(multiplier, basis_index)` rather than an expanded polynomial means no `HashMap` is
rebuilt per row: the row's terms are the basis element's terms with every monomial shifted by the
multiplier, generated on demand straight into the sparse row.

The closure is Faugère's `SymbolicPreprocessing`. Its fixed point is this invariant:

> **Closure invariant.** For every row `h` and every monomial `u` in the support of `h`: if `u` is
> divisible by `LM(g)` for some basis element `g`, then some row has leading monomial `u`.

The pair multiples satisfy it at `u = m` by themselves — each half has leading monomial `m` — which
is why the lcm must be seeded as already covered and must not get a reducer of its own. Every other
reducible monomial gets `(u / LM(g)) * g`, whose leading monomial is `u`. The invariant is
independent of the order monomials are examined in, so a deterministic worklist suffices;
termination follows from a monomial order being a well-order, since the pending set's maximum
strictly decreases.

This invariant is what makes candidate extraction sound, and it is tested directly.

Reducer selection is the first basis element, in index order, whose leading monomial divides `u`.
Deterministic, and the plan permits it; smarter policies are M16.

### 3.5 Macaulay matrix

```rust
struct MacaulayMatrix<const N: usize, F: FiniteField> {
    columns: Vec<Monomial<N>>,     // descending under the monomial order
    matrix: SparseMatrix<F>,
    rows: Vec<PreprocessedRow<N>>, // provenance, parallel to matrix.rows
}
```

Columns are the distinct monomials of all rows, sorted **descending under the requested
`MonomialOrder`** — not by `Monomial`'s derived `Ord`, which is lex regardless of the order under
computation. Column zero is the largest monomial, so a row's leading column is its leading
monomial and the elimination's leftmost-first pivot rule coincides with the monomial order.

### 3.6 Candidate extraction

After reduction, a nonzero row is a **candidate** exactly when its leading column's monomial is
not the leading monomial of any preprocessed row. That is Faugère's `F+ = {f : LM(f) ∉ LM(F)}`.

Every nonzero echelon row has a distinct leading column, so candidates are automatically distinct
and need no deduplication. More importantly, the closure invariant gives the extraction its
soundness: every column monomial that is divisible by some `LM(g)` is the leading monomial of some
row, hence covered, hence excluded. So **a candidate's leading monomial is never top-reducible by
the current basis** — it is genuinely new information, not a relation the basis already implies.
That consequence is asserted in the tests rather than assumed.

Treating every nonzero echelon row as a new basis element would be wrong in the cheap direction
(redundant elements, same ideal); dropping a required one would be wrong in the expensive
direction (an incomplete basis). The invariant plus the leading-monomial test is what separates
the two.

### 3.7 Public API

```rust
pub fn f4<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) -> Result<Vec<MultivariatePolynomial<N, F>>, F4Error>;

pub fn f4_with_options<const N: usize, F: FiniteField>(
    generators: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &F4Options,
) -> Result<(Vec<MultivariatePolynomial<N, F>>, F4Statistics), F4Error>;
```

Same input semantics as `buchberger`: zero generators ignored, duplicates dropped, the empty basis
for the zero ideal, `{1}` for an inconsistent system, output sorted descending by leading monomial.

`F4Options` carries the batch limit and the resource ceilings. `F4Error` reports which ceiling was
exceeded and by how much. `solve` keeps using `buchberger`; switching it is not this milestone's
decision to make.

## 4. Correctness and independent verification

Correctness is the primary acceptance criterion.

**Properties checked for every computed basis `G`.** Every original generator reduces to zero
modulo `G`; every S-polynomial of a pair in `G` reduces to zero modulo `G` (Buchberger's
criterion); every element is monic with no redundant leading monomial and no term divisible by
another element's leading monomial; repeated runs and permuted inputs give the identical ordered
basis.

**Reference comparisons.** Against `buchberger`, against `buchberger_reference` on small
instances, and against bases committed from Groebner.jl. A reduced Gröbner basis is unique for a
given ideal and order, and all three implementations sort canonically, so agreement is exact
equality of sequences — not of sets. No external computer algebra system is needed to run the
suite.

**Layer by layer.** Sparse elimination against the dense implementation (rank, row space, pivot
normalization). Symbolic preprocessing against the closure invariant directly. Matrix construction
by round-tripping rows back to polynomials. Batch reduction by checking that the selected pairs'
S-polynomials reduce to zero modulo the basis augmented with the batch's output — which is the
property that matters, since batch reduction legitimately produces different intermediate
polynomials from one-pair-at-a-time reduction.

**Edge cases.** Empty systems, the zero ideal, unit ideals, duplicate and scalar-multiple and
redundant generators, positive- and zero-dimensional ideals, homogeneous and inhomogeneous
systems, batches that reduce entirely to zero, duplicate leading monomials within a batch,
characteristic-dependent cancellation over small fields, and batch limits down to one pair.

All three monomial orders. grevlex is the performance target; correctness may not depend on it.

Slow reference comparisons are `#[ignore]`d and run with `cargo test --release -- --ignored`.

## 5. Benchmarks

Extending the existing Criterion suites, not replacing them.

| Family | Sizes | Purpose |
|---|---|---|
| Katsura | 3–7 variables | the standard benchmark, with sharply increasing difficulty |
| Cyclic | 3–5 variables | dense algebraic dependencies, heavy intermediate growth |
| Random quadratic | 4–8 variables | generic nonlinear systems, deterministic from a seed |
| Planted solution | 4–8 variables | an independently known witness |

Sizes are candidates, not promises. Fields: GF(13) and GF(541) for correctness, GF(2^31 - 1) for
the performance comparison, and the largest 64-bit prime for arithmetic regression. Field
arithmetic is unchanged this milestone except for correctness fixes.

Instrumentation beyond Buchberger's counters: batches, pairs per batch, matrix rows and columns,
rank, initial and final nonzeros, peak live nonzeros, zero rows, row operations, pivot inversions,
candidates per batch, and the largest matrix seen. Counters are counters — they go in an example
binary, not in Criterion, because they do not need sampling. Timing instrumentation stays out of
the inner loop.

Paired comparisons use the same compiler, profile, and machine. The question is how cost *scales*,
not who wins on katsura-3.

### 5.1 Baseline — Buchberger, before F4

Machine: AMD Ryzen Threadripper PRO 5995WX, 64 cores. `rustc 1.97.0`, release profile, Criterion
defaults with sample size 10. GF(2^31 - 1). Measured at `9d7f3d9` with `cargo bench --bench
grobner`, before any F4 code existed.

| system | lex | grlex | grevlex |
|---|---|---|---|
| cyclic-3 | 19.2 us | 19.4 us | 19.7 us |
| cyclic-4 | 185 us | 154 us | 153 us |
| katsura-3 | 41.5 us | 30.9 us | 33.4 us |
| katsura-4 | 790 us | 218 us | 126 us |
| katsura-5 | 180 ms | 2.42 ms | 1.14 ms |
| random-3 | 361 us | 54.6 us | 36.7 us |
| random-4 | 33.4 ms | 841 us | 961 us |
| planted-6 | 57.3 us | 39.3 us | 40.1 us |

These agree with the figures recorded at the close of the previous milestone, which is the point
of re-running them: the comparison in section 7 is against numbers from this machine at this
commit, not against numbers quoted from a document.

The two entries that matter most are the slowest: katsura-5 under lex at 180 ms and random-4 under
lex at 33.4 ms. Both are dominated by zero reductions — 1725 of 1790 on the former — which is
exactly the work F4 is supposed to absorb into linear algebra.

## 6. Implementation phases and pull requests

| PR | Deliverable | Merge gate |
|---|---|---|
| M15-1 | sparse rows, matrix, deterministic elimination | agrees with dense elimination, including rank-deficient and fill-in-heavy cases |
| M15-2 | shared pair queue; symbolic preprocessing; Macaulay construction | closure invariant holds; every row round-trips to its polynomial exactly |
| M15-3 | `reduce_batch` and candidate extraction | selected pairs are resolved by the augmented basis; extracted relations lie in the ideal |
| M15-4 | `f4`, `f4_with_options`, options, errors, statistics | agrees with Buchberger across the corpus under all three orders |
| M15-5 | benchmarks, statistics example, documentation | reproducible measurements, limitations, and next steps committed |

M15-5 is not the place for late algorithm changes. Defects it exposes get their own commits.

## 7. Results

Filled in as the milestone proceeds.

## 8. Risks

| Risk | Mitigation |
|---|---|
| Symbolic preprocessing misses a reducer multiple | Test the closure invariant directly; hand-verifiable small matrices; re-check selected S-pairs after every batch. |
| Candidate extraction accepts or drops the wrong rows | Track the preprocessed leading-monomial set; assert candidates are not top-reducible; verify the batch resolves its pairs. |
| Fill-in makes sparse storage lose | Measure peak nonzeros and density; enforce configurable ceilings; defer hybrid representations until the numbers justify them. |
| F4 is slower on the whole initial corpus | Benchmark progressively harder cases; keep Buchberger; if no crossover is found, document the bottleneck and name it as the M16 starting point. |
| Sharing the pair queue regresses Buchberger | Extract it as its own commit, guarded by Buchberger's existing tests — including the reference-agreement and determinism tests. |
| Scope drifts into a general matrix framework | Build only what F4 needs. Abstractions wait for a second caller. |

## 9. Acceptance criteria

**Mathematical correctness.** Sparse elimination validated against dense; symbolic preprocessing
reaches its fixed point; Macaulay matrices preserve coefficients and the monomial order; batch
reduction produces correct relations; the full algorithm satisfies Buchberger's criterion; bases
are monic, reduced, and canonically ordered; F4 agrees with both reference implementations; all
three orders supported; degenerate, redundant, and inconsistent systems handled.

**Engineering.** `buchberger` and `solve` unchanged; the public polynomial representation
unchanged; deterministic for fixed input and options; resource exhaustion is an explicit error; no
silently incomplete basis; stable Rust; `cargo test`, `cargo fmt --check`, and
`cargo clippy --all-targets --all-features -- -D warnings` all clean.

**Performance and diagnostics.** Standalone sparse-matrix benchmarks; F4 against Buchberger on
identical inputs; matrix dimensions, sparsity, fill-in, and reduction counters recorded;
progressively larger systems over a large prime field; every performance claim backed by a
measurement, including the cases F4 loses.

**Documentation.** This document; README coverage of the new API and when to use it; references;
explicit limitations and deferred optimizations; next steps chosen from observed bottlenecks.

## 10. Definition of done

Zeebra computes reduced Gröbner bases by either classical Buchberger reduction or F4 over sparse
finite-field linear algebra; both agree; and F4's costs and limits are measured rather than
assumed.

M16 is then selected from this milestone's instrumentation. The likely candidates are the chain
criterion and Gebauer–Möller pair elimination, better sparse pivot strategies, dense/sparse hybrid
matrices, cheaper monomial and divisor indexing, reuse of reducer multiples across batches,
specialized large-prime arithmetic, and parallel elimination. FGLM remains a separate, later
milestone.

## 11. References

1. Faugère, J.-C. (1999). *A new efficient algorithm for computing Gröbner bases (F4)*. Journal of
   Pure and Applied Algebra 139, 61–88. <https://doi.org/10.1016/S0022-4049(99)00005-5>
2. Cox, D., Little, J., O'Shea, D. *Ideals, Varieties, and Algorithms*, Sec. 2.7–2.10.
3. Demin, A., Gowda, S. *Groebner.jl: A package for Gröbner bases computations in Julia*.
   <https://arxiv.org/abs/2304.06935>
4. Groebner.jl — <https://github.com/sumiya11/Groebner.jl>, for implementation architecture.
5. msolve — <https://github.com/algebraic-solving/msolve>, a mature F4 implementation.
6. The preceding milestone: [`MILESTONE-ALGEBRA-FOUNDATION.md`](MILESTONE-ALGEBRA-FOUNDATION.md).

Published algorithm descriptions are the primary references. Existing implementations are read for
architecture and performance strategy, under their own licenses; no code is copied.
