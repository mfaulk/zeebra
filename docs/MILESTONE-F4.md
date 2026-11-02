# Milestone: Sparse Linear Algebra and F4 Gröbner Bases

Status: complete, in review. Baseline commit `9d7f3d9` (tree-identical to `main` at `bf73532`, the
merge of PR #14), 544 tests passing; 642 at the close of the milestone.

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

As built:

```text
src/linalg/sparse/
  mod.rs            re-exports
  row.rs            SparseRow: the sorted-unique-nonzero row and its arithmetic
  matrix.rs         SparseMatrix: a vector of rows plus a column count
  elimination.rs    row_echelon, row_echelon_within, reduced_row_echelon,
                    EliminationStatistics

src/grobner/
  pairs.rs          CriticalPair, PairQueue — shared with buchberger
  f4/
    mod.rs          f4, f4_with_options, and the main loop
    symbolic.rs     MonicBasis, symbolic_preprocessing, the reducer closure
    macaulay.rs     MacaulayMatrix: monomial-to-column mapping and construction
    reduction.rs    reduce_batch and candidate extraction
    options.rs      F4Options, F4Error
    statistics.rs   F4Statistics, BatchStatistics
    tests.rs        end-to-end correctness

benches/sparse_linear_algebra.rs   sparse against dense elimination
benches/grobner.rs                 both engines on identical inputs
examples/f4_statistics.rs          matrix and elimination counters
```

Options and errors moved into their own module rather than living in `mod.rs`, and the end-to-end
tests into their own file, because `mod.rs` would otherwise be the main loop plus two hundred
lines of unrelated declarations.

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

Sizes are candidates, not promises. What was actually run: katsura-3 through 7, cyclic-3 through 5,
random quadratics at 3 and 4 variables, planted solutions at 6 and 8. Random quadratics above 4
variables were not run — random-4 under lex already takes Buchberger 34 ms and the growth is steep
enough that random-5 would not be a paired comparison.

Two families from the plan are **not** benchmarked: mixed-degree systems at degrees 2, 3, 5, 7, and
sparse linear/quadratic mixtures at 6 to 10 variables. Neither generator exists in
`grobner::benchmark_systems`, and adding benchmark families is a different piece of work from
implementing F4 — the four families above already span the behaviour the comparison needed, from
instances where F4 loses to instances Buchberger cannot finish. They are listed here as a gap
rather than quietly dropped.

Fields: GF(7), GF(13), GF(541) and GF(2^31 - 1) for correctness, GF(2^31 - 1) for the performance
comparison. Field arithmetic is unchanged this milestone.

Instrumentation beyond Buchberger's counters: batches, pairs per batch, matrix rows and columns,
rank, initial and final nonzeros, peak live nonzeros, zero rows, row operations, pivot inversions,
candidates per batch, and the largest matrix seen. Counters are counters — they go in an example
binary, not in Criterion, because they do not need sampling. Timing instrumentation stays out of
the inner loop.

Paired comparisons use the same compiler, profile, and machine. The question is how cost *scales*,
not who wins on katsura-3.

A note on what is *not* measured: peak resident memory. The plan asked for memory estimates or
measured RSS. What is reported instead is `max_live_nonzeros`, the exact count of nonzero entries
live at the peak of the largest elimination, which is the quantity the budget is enforced on and
is directly convertible to bytes — 16 per entry for a 64-bit field. RSS would fold in allocator
behaviour and the rest of the process, and would not be the number that decides whether a
computation fits.

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

| PR | Deliverable | Merge gate | Status |
|---|---|---|---|
| M15-1 | sparse rows, matrix, deterministic elimination | agrees with dense elimination, including rank-deficient and fill-in-heavy cases | done — `src/linalg/sparse/` |
| M15-2 | shared pair queue; symbolic preprocessing; Macaulay construction | closure invariant holds; every row round-trips to its polynomial exactly | done — `src/grobner/pairs.rs`, `f4/symbolic.rs`, `f4/macaulay.rs` |
| M15-3 | `reduce_batch` and candidate extraction | selected pairs are resolved by the augmented basis; extracted relations lie in the ideal | done — `f4/reduction.rs`, `f4/options.rs`, `f4/statistics.rs` |
| M15-4 | `f4`, `f4_with_options`, options, errors, statistics | agrees with Buchberger across the corpus under all three orders | done — `f4/mod.rs`, `f4/tests.rs` |
| M15-5 | benchmarks, statistics example, documentation | reproducible measurements, limitations, and next steps committed | done — `benches/`, `examples/f4_statistics.rs`, this document |

M15-5 is not the place for late algorithm changes. Defects it exposes get their own commits. One
non-algorithmic change was made during M15-5: `F4Statistics` gained
two fill-in counters, in two steps and for the same underlying reason: the ratio the example
printed was not measuring fill-in. The first version divided one matrix's peak by a sum over every
batch, which is meaningless. The second divided the largest matrix's peak by its own as-built
count, which is meaningful but answers a different question — review found that the batch with the
largest absolute peak is not the batch that densified most, and that the difference is up to 2.2x
on the lex instances. Both ratios are now reported. The counters are new; no computation changed.

CI gained a release-mode job that runs the two Gröbner engine-agreement tests that are `#[ignore]`d
for speed, so the cross-check against the naive reference is enforced rather than merely
available.

## 7. Results

### 7.1 What the algorithm does differently

From `cargo run --release --example f4_statistics`, over GF(2^31 - 1). `bb:red` is the number of
critical pairs Buchberger reduces one at a time; `batches` is the number of matrices F4 builds to
cover the same pairs. `bb:0` and `empty` are the same comparison for the work that produces
nothing. `scaffld` is the share of matrix rows that symbolic preprocessing added to make the
reduction possible rather than being halves of a critical pair.

Two fill-in columns, because they answer different questions and are usually different batches.
`worst` is the largest ratio of peak live entries to as-built entries over **every** batch — how
badly sparse elimination densifies. `big` is that ratio for the single largest matrix — the one
that sized memory. A batch going from 100 entries to 800 densifies eightfold; one going from 1000
to 1500 has the larger absolute peak but densifies by half. Reporting only the second understates
the first, which is the number a dense/sparse threshold has to rest on.

| system | order | bb:red | batches | max/batch | bb:0 | empty | max matrix | scaffld | peak nz | worst | big | basis |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| cyclic-3 | lex | 6 | 4 | 3 | 4 | 2 | 8x8 | 45.5% | 23 | 1.11 | 1.05 | 3 |
| cyclic-3 | grevlex | 6 | 4 | 3 | 4 | 2 | 9x9 | 52.0% | 25 | 1.09 | 1.09 | 3 |
| cyclic-4 | lex | 44 | 12 | 7 | 37 | 6 | 28x29 | 57.1% | 128 | 1.80 | 1.33 | 6 |
| cyclic-4 | grlex | 35 | 7 | 9 | 29 | 2 | 40x39 | 54.2% | 180 | 1.31 | 1.31 | 7 |
| cyclic-4 | grevlex | 35 | 7 | 9 | 29 | 2 | 47x40 | 59.3% | 204 | 1.12 | 1.00 | 7 |
| cyclic-5 | lex | 1222 | 32 | 137 | 1173 | 16 | 565x351 | 71.8% | 13993 | 3.31 | 1.83 | 11 |
| cyclic-5 | grlex | 1454 | 23 | 305 | 1401 | 10 | 732x228 | 35.7% | 11379 | 1.77 | 1.00 | 30 |
| cyclic-5 | grevlex | 868 | 22 | 171 | 827 | 9 | 635x463 | 65.5% | 17061 | 3.58 | 3.58 | 20 |
| katsura-3 | lex | 10 | 4 | 4 | 6 | 1 | 15x15 | 51.2% | 61 | 1.22 | 1.17 | 3 |
| katsura-3 | grevlex | 7 | 3 | 4 | 4 | 1 | 15x15 | 53.3% | 54 | 1.04 | 1.04 | 4 |
| katsura-4 | lex | 84 | 13 | 12 | 70 | 6 | 56x49 | 70.5% | 567 | 2.34 | 1.48 | 4 |
| katsura-4 | grlex | 27 | 5 | 10 | 20 | 2 | 51x57 | 69.8% | 405 | 1.38 | 1.16 | 8 |
| katsura-4 | grevlex | 15 | 4 | 6 | 10 | 1 | 51x56 | 75.6% | 546 | 1.65 | 1.65 | 7 |
| katsura-5 | lex | 1790 | 29 | 84 | 1725 | 14 | 381x249 | 72.9% | 9285 | 3.39 | 1.53 | 5 |
| katsura-5 | grlex | 100 | 7 | 30 | 85 | 3 | 162x176 | 73.7% | 3126 | 1.62 | 1.62 | 16 |
| katsura-5 | grevlex | 49 | 6 | 15 | 39 | 2 | 278x291 | 87.2% | 7818 | 2.96 | 2.96 | 13 |
| katsura-6 | grlex | 387 | 9 | 104 | 356 | 4 | 644x674 | 77.9% | 34746 | 2.45 | 2.45 | 32 |
| katsura-6 | grevlex | 147 | 8 | 39 | 129 | 3 | 1388x1412 | 94.0% | 103314 | 6.56 | 6.16 | 22 |
| katsura-6 | lex | — | 59 | 563 | — | 26 | 1954x1030 | 77.5% | 151624 | 4.91 | 4.72 | 6 |
| katsura-7 | grlex | — | 11 | 414 | — | 5 | 2450x2476 | 80.0% | 368156 | 3.78 | 3.78 | 64 |
| katsura-7 | grevlex | — | 10 | 146 | — | 4 | 6810x6862 | 95.9% | 1390812 | 13.58 | 13.19 | 41 |
| planted-6 | lex | 12 | 3 | 6 | 6 | 1 | 15x16 | 27.3% | 42 | 1.20 | 1.08 | 6 |

A dash means Buchberger does not finish that instance here, so there is nothing to compare against.

Four things in this table are worth stating plainly.

**The batching is real, and it is where the saving comes from.** On katsura-5 under lex, 1790
individual reductions become 29 matrices, and 1725 zero reductions become 14 empty matrices. On
cyclic-5 under grlex it is 1454 reductions against 23 matrices. The largest batch
reaches 563 pairs on katsura-6 under lex. This is the mechanism the algorithm exists for, and the
counters confirm it is actually happening rather than being assumed.

**Most of the matrix is scaffolding.** Between 27% and 96% of rows are reducer multiples added by
symbolic preprocessing rather than halves of a critical pair — 94% on katsura-6 grevlex and 96% on
katsura-7 grevlex. Those rows exist only so the matrix can perform reductions that polynomial
division would do directly. They are not waste in the sense of being wrong, but they are the
single largest cost F4 pays for batching, and reusing reducer multiples across batches is the
obvious thing to attack next.

**Fill-in is real and grows with the instance.** From 1.04x on katsura-3 to 13.58x on katsura-7
grevlex, whose largest matrix alone goes from 105 thousand entries as built to 1.39 million live.
That is the measurement that justifies the `max_live_nonzeros` budget existing at all, and it says
a dense representation would be the better choice for the late, dense matrices — a hybrid worth
measuring, and deliberately not attempted here.

The gap between the two columns is itself informative, and it is largest under lex: katsura-5 lex
densifies 3.39x at worst while its biggest matrix only densifies 1.53x, and katsura-4 lex is
2.34x against 1.48x. Lex builds many matrices of very different sizes, and the ones that densify
worst are not the ones that grow largest — so sizing a hybrid threshold off the biggest matrix
would set it from the wrong batch. Under grevlex the two mostly coincide, because there are fewer
matrices and the last one dominates both.

**grevlex produces fewer, denser matrices; grlex more, sparser ones.** On katsura-7, grlex builds
11 matrices peaking at 368 thousand entries and grevlex builds 10 peaking at 1.39 million. The
usual expectation that grevlex is the cheapest order holds for Buchberger at every size measured,
and for F4 it reverses from katsura-6 upward: 23.9 ms grlex against 30.2 ms grevlex on katsura-6,
554 ms against 898 ms on katsura-7. Section 7.2 has the rest.

### 7.2 Wall clock

From `cargo bench --bench grobner`, which runs both engines on the identical system under the
identical order, same machine, same profile, Criterion medians at sample size 10. GF(2^31 - 1).
The two engines return the same basis, which the benchmark's own correctness tests establish and
`examples/f4_statistics.rs` asserts again at run time.

| system | order | Buchberger | F4 | F4 speedup |
|---|---|---|---|---|
| cyclic-3 | lex | 19.9 us | 19.2 us | 1.04x |
| cyclic-3 | grlex | 20.3 us | 19.1 us | 1.06x |
| cyclic-3 | grevlex | 20.6 us | 20.8 us | 0.99x |
| cyclic-4 | lex | 189 us | 179 us | 1.05x |
| cyclic-4 | grlex | 156 us | 134 us | 1.17x |
| cyclic-4 | grevlex | 160 us | 158 us | 1.02x |
| cyclic-5 | lex | 53.3 ms | **27.1 ms** | 1.97x |
| cyclic-5 | grlex | 64.3 ms | **21.2 ms** | 3.03x |
| cyclic-5 | grevlex | 38.8 ms | **23.0 ms** | 1.69x |
| katsura-3 | lex | 42.5 us | 42.6 us | 1.00x |
| katsura-3 | grlex | 32.4 us | 32.4 us | 1.00x |
| katsura-3 | grevlex | 33.4 us | 33.6 us | 0.99x |
| katsura-4 | lex | 853 us | **567 us** | 1.50x |
| katsura-4 | grlex | 225 us | 244 us | 0.92x |
| katsura-4 | grevlex | **136 us** | 177 us | 0.77x |
| katsura-5 | lex | 191 ms | **14.8 ms** | **12.96x** |
| katsura-5 | grlex | 2.47 ms | 1.92 ms | 1.29x |
| katsura-5 | grevlex | **1.31 ms** | 1.82 ms | 0.72x |
| katsura-6 | grlex | 40.0 ms | **23.9 ms** | 1.67x |
| katsura-6 | grevlex | **14.1 ms** | 30.2 ms | 0.47x |
| random-3 | lex | 362 us | 293 us | 1.23x |
| random-3 | grlex | 53.9 us | 58.0 us | 0.93x |
| random-3 | grevlex | **35.5 us** | 42.7 us | 0.83x |
| random-4 | lex | 33.8 ms | **8.46 ms** | **4.00x** |
| random-4 | grlex | 831 us | 805 us | 1.03x |
| random-4 | grevlex | 1.09 ms | 940 us | 1.16x |
| planted-6 | lex | 57.7 us | 48.8 us | 1.18x |
| planted-6 | grlex | 39.6 us | 37.1 us | 1.07x |
| planted-6 | grevlex | 41.1 us | 38.1 us | 1.08x |
| planted-8 | lex | 90.2 us | 72.9 us | 1.24x |
| planted-8 | grlex | 66.0 us | 61.2 us | 1.08x |
| planted-8 | grevlex | 66.6 us | 62.7 us | 1.06x |

Instances Buchberger does not finish here, from the `grobner_f4_only` group:

| system | order | F4 | Buchberger |
|---|---|---|---|
| katsura-6 | lex | **3.19 s** | did not finish in 1800 s |
| katsura-7 | grlex | **554 ms** | not attempted |
| katsura-7 | grevlex | **898 ms** | not attempted |

katsura-6 under lex is the clearest single result in the milestone: **F4 computes it in 3.19 s
where Buchberger did not finish in 1800 s**, measured by running `buchberger` on that one instance
under a thirty-minute budget, which it exhausted. That is a lower bound of 564x and, since the
computation was still running when it was killed, an underestimate by an unknown margin. katsura-7
is not reachable by Buchberger here at all.

These are `grobner_f4_only` rather than paired benchmarks precisely because putting Buchberger in
them would hang the suite, and leaving them out would understate the milestone. The bound is
stated as a bound rather than converted into a speedup figure that implies a measurement nobody
made.

**The desired outcome was achieved, and the shape of it is specific.** F4 wins decisively where
Buchberger wastes the most work — 13.0x on katsura-5 under lex, 4.0x on random-4 under lex, 3.0x
on cyclic-5 under grlex — and loses by up to 2.1x on grevlex at small and medium sizes.

The pattern is consistent with the counters in section 7.1 and is worth stating as a rule rather
than as a list of numbers:

**F4's advantage tracks the number of reductions Buchberger wastes.** katsura-5 lex has 1725
useless reductions out of 1790 and F4 is 13x faster. katsura-5 grevlex has 39 out of 49 and F4 is
1.4x *slower*. When the pair count is already small, there is little to amortise and the matrix
machinery — symbolic preprocessing, column sorting, construction — is pure overhead.

**Under grevlex, F4's matrices get dense, and that is where it loses.** katsura-6 grevlex is 94%
scaffolding with 6.6x fill-in, and it is the worst paired result in the table at 0.47x. The same
system under grlex is 78% scaffolding with 2.5x fill-in, and F4 wins at 1.67x. grevlex is the
cheapest order for Buchberger and, at these sizes, the *worst* order for this F4 implementation —
the opposite of the usual guidance, and a direct consequence of the fill-in rather than of
anything about grevlex itself.

**On the smallest systems the two are indistinguishable**, within a few percent on cyclic-3 and
katsura-3. Matrix construction costs about what the handful of reductions it replaces costs.

None of this is evidence that Zeebra is competitive with established F4 implementations. It is
evidence that this F4 implementation is correct, that it batches as intended, and that its costs
are now measured well enough to say what to fix next.

### 7.3 Sparse against dense elimination

From `cargo bench --bench sparse_linear_algebra`, n x n matrices over GF(2^31 - 1) at four
densities. The sparse figure is row echelon form; the dense figure is `gauss_jordan_elimination`,
which computes the *reduced* form and therefore does strictly more work. The comparison is
indicative of the representation, not a like-for-like algorithm comparison, and is reported that
way deliberately.

| n | density | sparse | dense (RREF) |
|---|---|---|---|
| 16 | 2% | 2.39 us | 4.46 us |
| 16 | 100% | 15.1 us | 19.6 us |
| 32 | 2% | 6.32 us | 12.8 us |
| 32 | 100% | 66.5 us | 98.0 us |
| 64 | 2% | 22.4 us | 70.5 us |
| 64 | 10% | 157 us | 358 us |
| 64 | 100% | 407 us | 675 us |
| 128 | 2% | 75.0 us | 467 us |
| 128 | 10% | 1.83 ms | 3.58 ms |
| 128 | 30% | 2.85 ms | 4.84 ms |
| 128 | 100% | 2.91 ms | 5.13 ms |

The gap widens with sparsity exactly as expected: 6.2x at n = 128 and 2% dense, 2.0x at 10%. At
full density the sparse representation is still ahead, but by a factor consistent with the dense
implementation doing a second back-substitution pass, so **no crossover was found within this
range** and none should be claimed. Finding the real crossover needs a dense row-echelon-only
implementation to compare against, which is an M16 task and the prerequisite for any hybrid.

F4-shaped matrices — more columns than rows, a handful of entries per row, leading entries
colliding in low columns — are benchmarked separately:

| shape | entries/row | time |
|---|---|---|
| 64 x 256 | 8 | 125 us |
| 256 x 1024 | 12 | 13.0 ms |
| 512 x 2048 | 16 | 221 ms |

The growth from 13 ms to 221 ms for a 2x increase in each dimension is fill-in, not arithmetic
volume, and it is the clearest single cost in the whole milestone.

## 8. Risks

| Risk | Mitigation | Outcome |
|---|---|---|
| Symbolic preprocessing misses a reducer multiple | Test the closure invariant directly; hand-verifiable small matrices; re-check selected S-pairs after every batch. | Did not occur. The invariant is asserted directly over ten systems under all three orders, as one wide batch and one pair at a time. |
| Candidate extraction accepts or drops the wrong rows | Track the preprocessed leading-monomial set; assert candidates are not top-reducible; verify the batch resolves its pairs. | Did not occur. Exact agreement with both reference engines is the end-to-end confirmation. |
| Fill-in makes sparse storage lose | Measure peak nonzeros and density; enforce configurable ceilings; defer hybrid representations until the numbers justify them. | **Occurred, and is the main finding.** Up to 13.6x on katsura-7 grevlex. The budget catches it; a hybrid representation is now a measured need rather than a guess. |
| F4 is slower on the whole initial corpus | Benchmark progressively harder cases; keep Buchberger; if no crossover is found, document the bottleneck and name it as the M16 starting point. | Partly occurred: F4 loses on the small systems and wins where Buchberger wastes the most work. See section 7.2. |
| Sharing the pair queue regresses Buchberger | Extract it as its own commit, guarded by Buchberger's existing tests — including the reference-agreement and determinism tests. | Did not occur. The extraction was its own commit and the existing tests passed unchanged. |
| Scope drifts into a general matrix framework | Build only what F4 needs. Abstractions wait for a second caller. | Held. `linalg::sparse` is a row, a matrix, and two elimination functions; no representation policy, no traits. |

## 9. Acceptance criteria

### Mathematical correctness

| Criterion | Status |
|---|---|
| Sparse row echelon reduction independently validated | Met — equality with dense Gauss–Jordan on hand-written and random matrices over GF(7), GF(13), GF(541), GF(2^31 - 1), at five shapes and four densities; rank agrees with `Matrix::rank`; the row space is certified by an augmented identity block |
| Symbolic preprocessing reaches a correct fixed point | Met — the closure invariant asserted directly, ten systems x three orders x two batch shapes, plus a chained case needing several rounds |
| Macaulay matrices preserve coefficients and the monomial order | Met — every row round-trips to its polynomial; columns strictly descending under the order in force; a dedicated test shows the column order follows grevlex rather than `Monomial`'s derived lex `Ord` |
| F4 batch reduction produces correct algebraic relations | Met — candidates lie in the ideal, are never top-reducible by the basis, and resolve the pairs the batch selected |
| The complete algorithm satisfies Buchberger's criterion | Met — asserted for every basis over a 23-system corpus under all three orders |
| Bases are monic, reduced, and canonically ordered | Met — asserted against the definition, not against a known answer |
| F4 agrees with the reference implementations | Met — exact sequence equality with `buchberger` and `buchberger_reference` over the corpus; with `buchberger` on cyclic-3/4/5, katsura-3/4/5/6, planted-6/8; with a basis committed from Groebner.jl |
| All three monomial orders supported | Met, and distinguished: grevlex gives a 2-element basis where grlex gives 5 on the same ideal |
| Degenerate, redundant, and inconsistent systems handled | Met — zero ideal, zero generators, unit ideals, duplicates, scalar multiples, redundant generators, positive- and zero-dimensional, homogeneous and inhomogeneous, shared leading monomials, characteristic-dependent cancellation |

### Engineering

| Criterion | Status |
|---|---|
| Existing `buchberger` APIs remain available | Met — signature and behaviour unchanged; it now calls the shared pair queue |
| Existing `solve` semantics unchanged | Met — `solve` still uses `buchberger` |
| Public polynomial representation preserved | Met — `SparseMultiPoly<N, F>` and `Monomial<N>` untouched; `const N: usize` retained |
| Deterministic for fixed input and options | Met — asserted at every layer: elimination, preprocessing, matrix construction, batch reduction, and the whole algorithm, including under permuted and duplicated generators |
| Resource exhaustion produces explicit errors | Met — five `F4Error` variants, each tested; the nonzero budget is checked after every row operation |
| No F4 computation silently returns an incomplete result | Met — there is no error variant and no code path that returns a partial basis |
| Stable Rust, tests, formatting, strict Clippy | Met — 642 tests pass, plus two slow engine-agreement tests in release; `cargo fmt --all --check` and `cargo clippy --all-targets --all-features -- -D warnings` are clean |

### Performance and diagnostics

| Criterion | Status |
|---|---|
| Standalone sparse-matrix benchmarks | Met — `benches/sparse_linear_algebra.rs`, four sizes x four densities plus three F4-shaped matrices |
| F4 compared with Buchberger on identical inputs | Met — `benches/grobner.rs` runs both engines on every paired instance under the same order |
| Matrix dimensions, sparsity, fill-in, and reduction statistics recorded | Met — section 7.1, from `examples/f4_statistics.rs` |
| Progressively larger systems over a large prime field | Met — katsura-3 through 7 and cyclic-3 through 5 over GF(2^31 - 1) |
| Performance advantages demonstrated with reproducible measurements | Met — section 7.2 |
| Cases where F4 loses documented | Met — section 7.2, and they are the majority of the small instances |

One criterion from the plan is **not** met as stated: a 68-bit `PrimeFieldElement128` stress run.
It was listed as "if runtime permits" and was not attempted; the correctness suite covers GF(7)
through GF(2^31 - 1) and the largest 64-bit prime is exercised by the existing field benchmarks,
not by F4. Nothing in `linalg::sparse` or `grobner::f4` is specialized to a word size, so this is
a gap in measurement rather than in capability.

### Documentation

| Criterion | Status |
|---|---|
| `docs/MILESTONE-F4.md` documents the algorithm and implementation | Met — this document |
| README explains the new API and when to use it | Met — a Gröbner/F4 section with both entry points, the `Result` rationale, and guidance on which engine to pick |
| Mathematical references recorded | Met — section 11, and in the module documentation at each stage |
| Known limitations and deferred optimizations explicit | Met — section 10 |
| Next steps recommended from observed bottlenecks | Met — section 10, ordered by what the measurements say |

## 10. Definition of done, limitations, and next steps

Zeebra computes reduced Gröbner bases by either classical Buchberger reduction or F4 over sparse
finite-field linear algebra; both agree exactly wherever both can run; and F4's costs and limits
are measured rather than assumed. That is the milestone.

### 10.1 Known limitations

- **Reducer multiples are recomputed every batch.** 27% to 96% of every matrix is reduction
  scaffolding, rebuilt from scratch each time. Nothing is cached across batches.
- **Reducer selection is first-applicable.** The first basis element in index order whose leading
  monomial divides. Choosing the one with the largest leading monomial would give smaller
  multiples and smaller matrices.
- **Divisor lookup is a linear scan** over the basis, for every monomial tested. No divisor tree,
  no monomial hashing.
- **One representation.** Sparse rows throughout, including for the late matrices that fill in to
  several times their initial density and would be better served dense.
- **No chain criterion.** Only Buchberger's first criterion, inherited from the Buchberger
  implementation. Gebauer–Möller would cut the pair count before the matrices are ever built.
- **Matrix construction is single-threaded**, as is elimination.
- **`max_live_nonzeros` is checked after every row operation**, so a single row operation can
  overshoot the budget before it is noticed. The overshoot is bounded by one row, which is stated
  in the function's documentation rather than left implicit.
- **No 128-bit field measurement** (section 9).
- **`N` is still a const generic**, so a variable count cannot be chosen at runtime. This did not
  constrain F4 itself — the matrix has runtime dimensions — but it does mean each benchmark size
  needs its own instantiation.

### 10.2 M16, ordered by what the measurements say

1. **Reuse reducer multiples across batches.** The scaffolding share is the largest single cost
   this milestone measured, and it is pure recomputation.
2. **A dense/sparse hybrid, with a measured threshold.** Fill-in reaches 13.6x and the
   F4-shaped benchmark goes from 13 ms to 221 ms for a 2x shape increase. This needs a
   dense row-echelon-only implementation first, so that the crossover can be located rather than
   guessed — section 7.3 could not locate it because the dense comparison computes more.
3. **The chain criterion and Gebauer–Möller.** Cheaper than making the matrices faster, because it
   prevents rows from existing.
4. **Better reducer selection and divisor indexing.** Smaller multiples and sub-linear lookup.
5. **Parallel elimination.** The machine has 64 cores and the implementation uses one.
6. **Specialized arithmetic for large prime fields**, which the previous milestone identified as
   the remaining arithmetic bottleneck for 128-bit fields.

FGLM remains a separate, later milestone focused on solving rather than on basis computation.
Whether `solve` should switch to F4 is a decision for after (1) and (2): on the lex bases `solve`
needs, F4 is already the faster engine on the harder instances, but `solve`'s own instances are
small enough that it is not yet clear.

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
