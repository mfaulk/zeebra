# Milestone: F4 Computational Efficiency

Status: in progress. Baseline commit `b19eefc` (`origin/main`, the merge of PR #19), 653 tests
passing in debug.

The preceding milestone delivered a **correct** F4. This one makes it **fast enough to be the
engine Zeebra actually uses**. The difference is not rhetorical: F4 currently loses to classical
Buchberger on five of the thirteen paired grevlex and grlex instances in
[`MILESTONE-F4.md`](MILESTONE-F4.md) §7.2, including by 2.1x on katsura-6 grevlex — the instance
the previous milestone named as the next thing to fix.

Everything here is a performance milestone on a fixed mathematical contract. `f4` and
`f4_with_options` keep their signatures and their semantics. A reduced Gröbner basis is unique for
a given ideal and order, so **every optimization in M16 is required to return the identical
sequence of polynomials the baseline returns**. That is not an aspiration; it is the acceptance
test, and it is what makes an optimization milestone safe to execute in parallel.

## 1. Objective

Zeebra is successful at this milestone if

1. the practical size of system it can solve within a fixed time and memory budget grows,
2. every optimization is justified by a measurement taken *before* it was implemented,
3. an optimization that measurement does not justify is **rejected with its evidence preserved**,
   not merged because it was written,
4. the combined engine returns exactly the baseline's basis on the whole correctness corpus, and
5. the cost of an F4 computation is attributable to a stage rather than only to the whole.

(3) is stated as an objective because the M15 report's bottleneck list is a list of *hypotheses*.
"94% of rows are reducer multiples" does not imply those multiples recur across batches, and
"13.6x fill-in" does not imply any matrix is dense. Both are measured in M16-0 before anyone acts
on them.

## 2. Scope

### In scope

Structured (block) elimination of the Macaulay matrix; divisibility indexing and reducer-selection
policy; cross-batch reuse of reducer multiples; the chain criterion and Gebauer–Möller; a dense
row-echelon backend with the sparse implementation's exact contract; density-adaptive elimination;
per-stage cost attribution; an ablation study over the four workstreams; the measurements and the
report.

### Out of scope

FGLM and order conversion. F5 and signature-based algorithms. Prime fields above 128 bits.
Cryptanalysis-specific functionality or workflows. GPU kernels. Distributed computation. Public
API redesign. Unrelated computational algebra features. Parallel elimination may be *investigated*
if a measurement strongly justifies it, but it is not a deliverable.

The motivating workloads — tens of variables, sparse low-degree systems with large intermediate
growth, degrees 2/3/5/7, 31–64 bit primes now and 128–255 bit later, zero-dimensional systems —
shape which benchmark families are run. They do not license building anything specific to them.

### Architectural decisions

| Decision | Reason |
|---|---|
| The public `f4` / `f4_with_options` signatures do not change | Every optimization is selected through `F4Options`, which has public fields and a `Default`. A caller who ignores M16 entirely gets the fastest configuration that is known-good, and a caller comparing configurations has one knob per workstream. |
| `F4Options` and `F4Statistics` are **frozen by M16-0**, with every variant A–D will need declared up front | These two files are what all four workstreams would otherwise edit simultaneously. Declaring the complete surface in M16-0 — each new arm initially delegating to the baseline — converts four merge conflicts into zero. |
| Elimination is selected by an enum, not a trait object | `F4Options` is `Clone + Debug + Eq`, which `Box<dyn EliminationBackend>` is not. Enum dispatch also keeps the backend monomorphized over `F: FiniteField`, which a trait object cannot be without boxing the field. |
| The elimination interface lives in `linalg`, and F4 calls it through two frozen functions | M16-A needs block primitives; M16-D needs to re-implement them per representation. Putting the interface in `src/linalg/echelon.rs` means A never edits a file in `linalg` and D never edits a file in `grobner`. |
| Stage timing is opt-in (`F4Options::measure_stages`) and off by default | M15 kept timing out of the inner loop, correctly. Four `Instant::now()` calls per *batch* — not per row — is the granularity that attributes cost without distorting it, and a default of `false` means the shipping path has none. |
| Cross-batch state is passed explicitly, not held in a global or a `thread_local` | A reducer cache is the one M16 optimization that makes a batch's output depend on earlier batches. Threading it as an explicit `&mut` argument is what keeps "deterministic for fixed input and options" checkable. |
| Pair criteria operate on leading monomials, not on polynomials | `SparseMultiPoly::leading_monomial` is a scan of the whole term map, and the baseline calls it three times per pair created. Gebauer–Möller needs the leading monomials of the whole basis at once; passing them is both the cheaper and the only workable interface. |
| Buchberger keeps its behaviour and remains the oracle | Unchanged from M15, and more important here: an optimization milestone with no independent oracle cannot distinguish "faster" from "wrong". |

## 3. Sub-milestones

| ID | Sub-milestone | Depends on | Branch |
|---|---|---|---|
| M16-0 | Shared interfaces, benchmarks, and execution plan | — | `feat/m16-foundation` |
| M16-A | Structured F4 elimination | M16-0 | `feat/m16-structured-f4` |
| M16-B | Symbolic preprocessing and monomial indexing | M16-0 | `feat/m16-symbolic` |
| M16-C | Improved critical-pair criteria | M16-0 | `feat/m16-pair-criteria` |
| M16-D | Dense and adaptive linear algebra | M16-0 | `feat/m16-hybrid-linalg` |
| M16-I | Integration, ablation benchmarks, and final report | A, B, C, D | `feat/m16-integration` |

A, B, C and D are each based on the **same** M16-0 commit and are not stacked on one another. They
are combined only on the integration branch, where conflicts are resolved once rather than four
times.

### 3.1 File ownership

The point of this table is that no two concurrent workstreams own the same file. A workstream that
needs a change outside its own column proposes an interface change to the integrator instead of
making it.

| Path | Owner |
|---|---|
| `src/grobner/f4/options.rs` | M16-0, then frozen |
| `src/grobner/f4/statistics.rs` | M16-0, then frozen |
| `src/grobner/f4/mod.rs` | M16-0, then the integrator |
| `src/grobner/f4/observer.rs` | M16-0, then frozen |
| `src/linalg/echelon.rs` | M16-0, then M16-D |
| `src/grobner/f4/reduction.rs`, `macaulay.rs`, `structured.rs` | M16-A |
| `src/grobner/f4/symbolic.rs`, `divisors.rs` | M16-B |
| `src/grobner/pairs.rs`, `src/grobner/buchberger.rs` | M16-C |
| `src/linalg/**` except `echelon.rs` | M16-D |
| `src/grobner/f4/tests.rs` | shared, append-only — add tests, do not rewrite existing ones |
| `benches/**`, `examples/**` | shared, append-only |
| `docs/MILESTONE-F4-OPTIMIZATION.md` | §7 onwards is per-workstream, append-only; §1–6 are the integrator's |

## 4. M16-0 — shared interfaces and the baseline

### 4.1 The option surface

One enum or flag per workstream, every variant declared now, each non-baseline variant initially
behaving exactly like the baseline so that the surface compiles and the tests pass before any
optimization exists.

```rust
pub enum EliminationBackend { Sparse, Dense, Adaptive }     // M16-D
pub enum ReductionStrategy  { Unstructured, Structured }    // M16-A
pub enum ReducerSelection   { FirstApplicable, LargestLeadingMonomial }  // M16-B
pub struct PairCriteria { product: bool, chain: bool, gebauer_moller: bool }  // M16-C

pub struct F4Options {
    // ... the M15 fields, unchanged ...
    pub elimination: EliminationBackend,
    pub reduction: ReductionStrategy,
    pub reducer_selection: ReducerSelection,
    pub criteria: PairCriteria,
    pub reuse_reducers: bool,          // M16-B
    pub measure_stages: bool,          // M16-0
}
```

`F4Options::default()` is the M15 configuration exactly, so the default path is the measured
baseline until M16-I changes it deliberately and says so. `F4Options::baseline()` names that
configuration permanently, so the ablation study can always reconstruct it even after the default
moves.

### 4.2 The elimination interface

`src/linalg/echelon.rs`, two functions, frozen:

```rust
/// Row echelon form of the whole matrix, under the chosen representation.
pub fn row_echelon_with<F: FiniteField>(
    backend: Backend, matrix: &mut SparseMatrix<F>, max_nonzeros: usize,
) -> Result<EliminationStatistics, usize>;

/// Eliminate rows `[split..]` against the pivots of rows `[..split]`, then echelonize them.
///
/// Rows `[..split]` must already have distinct leading columns and unit pivots. They are left
/// in place and are not reduced against each other, which is what lets a caller that knows its
/// upper block is already triangular skip establishing those pivots at all.
pub fn reduce_rows_against_pivots_with<F: FiniteField>(
    backend: Backend, matrix: &mut SparseMatrix<F>, split: usize, max_nonzeros: usize,
) -> Result<EliminationStatistics, usize>;
```

`Backend` is `linalg`'s own enum; `F4Options::elimination` maps onto it. `linalg` does not depend
on `grobner`, and that stays true.

The second function is the one M16-A is built on and M16-D must honour. Its contract is stated in
terms of pivots and row space, not in terms of a representation, so a dense or adaptive
implementation is substitutable.

### 4.3 The batch observer

`f4_with_options` delegates to a private generic driver taking `&mut impl BatchObserver`, and
passes a no-op that monomorphizes away. One frozen method:

```rust
pub trait BatchObserver<const N: usize, F: FiniteField> {
    fn batch(&mut self, basis: &MonicBasis<N, F>, pairs: &[CriticalPair<N>]);
}
```

This exists because every workstream's first task is a measurement on **real** batches, and the
alternative — each agent reimplementing the main loop to capture them — would give four subtly
different main loops and four incomparable measurements. `f4::observer::BatchTrace` collects
`(basis, pairs)` snapshots so a stage can be replayed, benchmarked, or counted in isolation:

- M16-A replays batches to compare block elimination against the one-pass echelon on identical
  matrices.
- M16-B counts how often the same `(basis_index, multiplier)` recurs across batches — the
  measurement that decides whether a reducer cache is worth building at all.
- M16-D harvests real Macaulay matrices to locate the sparse/dense crossover on the shapes F4
  actually produces rather than on synthetic ones.

### 4.4 Stage attribution

`F4Statistics::stages: StageTimings { symbolic, construction, elimination, extraction, total }`,
populated only when `measure_stages` is set. Four `Instant` reads per batch.

`examples/f4_profile.rs` prints the breakdown for a named configuration, which is how each
workstream reports its effect and how M16-I builds the ablation table.

`benches/f4_stages.rs` times symbolic preprocessing, matrix construction, and elimination
separately on batches captured from real runs, so a change that moves cost from one stage to
another is visible as such instead of as a small change in the total.

### 4.5 Baseline

Recorded in §6 below: machine, toolchain, profile, Criterion configuration, and the measurements.

### 4.6 Exit criteria

- The option and statistics surfaces compile with every A–D variant present and behaving as the
  baseline, and the full suite passes.
- `linalg::echelon`'s two functions exist with sparse implementations and the documented contract.
- The observer exists and `f4_with_options` returns bit-identical results through it.
- Stage attribution and the three measurement entry points run.
- Baselines for katsura-5/6/7, cyclic-5, and the deterministic quadratic systems are committed.
- The four workstreams can be started from one commit with no file in two columns of §3.1.

## 5. The four implementation sub-milestones

Each states the hypothesis, the measurement that tests it, and what "reject" looks like — because
rejecting an optimization with evidence is a successful outcome, and merging one that the
measurement did not support is not.

### 5.1 M16-A — Structured F4 elimination

**Hypothesis.** Sorting the Macaulay matrix into a reducer block above a pair block makes the
upper-left block unit upper triangular *by construction*, because symbolic preprocessing gives
every reducer row a distinct leading monomial. Writing

```text
M = [ A  B ]        A: reducer rows x reducer-lead columns, unit upper triangular
    [ C  D ]        C, D: the pair rows
```

the new pivots are exactly the pivots of `D - C A^{-1} B`, so the elimination never has to
discover `A`'s pivots and never fills in `A` or `B` at all. The baseline reduces all rows in index
order and pays for both.

**Measurement.** Replay real batches through both paths; compare row operations, peak live
nonzeros, and wall clock on the identical matrix. The reducer-row share (27–96% in M15 §7.1) is
the upper bound on what this can save, not evidence that it saves it.

**Reject if** the block path does not reduce row operations or peak nonzeros on the grevlex
instances where the reducer share is highest. Keep the one-pass path as the default in that case
and record the numbers.

**Correctness.** Candidate extraction semantics are unchanged: a candidate is still a nonzero row
whose leading monomial is not the leading monomial of any input row. The block path must produce
the same set of new leading monomials, and `f4` must return the identical basis under all three
orders.

**Owns** `src/grobner/f4/reduction.rs`, `macaulay.rs`, new `src/grobner/f4/structured.rs`.
**Must not** modify `src/linalg/**` or `f4/symbolic.rs`.

### 5.2 M16-B — Symbolic preprocessing and monomial indexing

**The §6.2 baseline reorders this workstream before it starts.** Symbolic preprocessing is 2% to
15% of the computation, and it is *smallest* on exactly the instances with the largest reducer
share — 2.1% on katsura-7 grevlex, which is 95.9% scaffolding. The preceding milestone put reducer
reuse first on the strength of that 95.9%. The breakdown says reducer rows are expensive because
they enlarge the **matrix**, which elimination then pays for, not because finding them is slow.

So the hypothesis worth pursuing is the one that produces **fewer and smaller rows**, whose benefit
lands in elimination; and the hypothesis to measure-then-probably-reject is caching, whose entire
ceiling is a fraction of 2–15%.

**Hypotheses, in the order the measurement puts them.**

1. **Smaller multipliers.** First-applicable reducer selection takes the first divisor in index
   order. Choosing the divisor with the **largest** leading monomial gives the smallest multiple,
   hence fewer new monomials, hence a smaller closure and a smaller matrix. This is the one with
   leverage on the 65–88% that elimination costs, and it must be measured by its effect on the
   **whole computation**, not on preprocessing alone — it can easily make preprocessing slower and
   the computation faster, or the reverse.
2. **Faster divisor lookup.** §6.3 confirms the scan: 4.7 to 47.2 basis elements examined per
   query, worst under lex. A degree filter, a variable-support bitmask, or a divisibility index
   should cut it. Worth having; bounded by the stage's share of the total, so worth bounded effort.
3. **Reducer reuse.** Measure the repetition rate of `(basis_index, multiplier)` across batches
   with `CacheMode::Count` **before** implementing `CacheMode::Store`. Successive batches work at
   successive degrees, so recurrence is not obvious, and the payoff is capped low either way.

**Reject if** smaller multipliers do not shrink the closure or do not shorten the computation; if
an index does not reduce scan steps per query; or if the repetition rate is low. A rejection with
the number attached is the deliverable in that case — not an unused cache.

**Correctness.** The closure invariant — every monomial of every preprocessed row that is
divisible by some `LM(g)` is the leading monomial of some row — is preserved exactly, and the
existing direct assertion of it must pass unchanged over all ten systems and three orders. Any
index must answer `find_divisor` **identically** to the linear scan, including which divisor it
picks, or reducer selection changes and with it the matrix; a differential test against the scan
is required. A cache must be deterministic and bounded.

**Owns** `src/grobner/f4/symbolic.rs`, new `src/grobner/f4/divisors.rs`.
**Must not** modify pair scheduling or elimination internals.

### 5.3 M16-C — Critical-pair criteria

**Hypothesis.** Only Buchberger's first criterion is implemented. The chain criterion and
Gebauer–Möller discard pairs *before* a matrix is built, which is strictly cheaper than reducing
them, and they are the standard reason real implementations build far fewer matrices.

**The soundness condition is the whole deliverable.** The chain criterion discards the pair
`(i, j)` when there is a `k` with `LM(f_k)` dividing `lcm(LM f_i, LM f_j)` **and both `(i, k)` and
`(k, j)` already handled**. Dropping the second half — discarding on divisibility of the lcm alone
— is unsound and is the classic way to return an incomplete basis that passes casual testing.
Gebauer–Möller is the standard insertion-time formulation of the same three conditions; it is
implemented as published and cited, with the conditions named in the code.

**Measurement.** Pairs eliminated per criterion, matrices built, and wall clock, for both engines,
over all three orders.

**Reject if** a criterion does not reduce matrices built. It cannot be rejected for being
*correct* and slow on small inputs; it can be rejected for not paying on any instance.

#### 5.3.1 A second deliverable: interreduction

§6.2 found that `reduce_grobner_basis` is **2479 ms of katsura-6 lex's 2963 ms**, which is the
largest single cost in the whole baseline. It lives in `src/grobner/buchberger.rs`, which this
workstream already owns, it is shared by both engines, and it is the same kind of work as the rest
of M16-C — removing work that does not have to be done. So it is assigned here, and reported
separately from the criteria so the two effects stay distinguishable.

The costs are visible without a profiler, and all three are quadratic in the pre-interreduction
basis size with a large constant:

- `minimize_grobner_basis` deduplicates with `monic.contains(&scaled)`: a full polynomial equality
  against every element kept so far. On katsura-6 lex the elements are both numerous and wide.
- It then calls `leading_monomial` — a scan of a polynomial's whole term map — inside a double loop
  over the basis. The leads can be taken once.
- `reduce_grobner_basis` clones all `n - 1` other polynomials once per element, to build the slice
  `normal_form` takes, before computing anything.

None of this changes the result: minimization and interreduction are defined by the properties
they establish, and the output is already canonically ordered. **The returned basis must be
identical**, which the existing uniqueness tests already check and which a direct before/after
comparison should check too.

Note that this benefits classical Buchberger as well — it calls the same function — so it is one of
the few M16 changes that improves the oracle. The oracle's *result* must not move.

**Correctness.** The computed reduced basis is unchanged — exact sequence equality against the
baseline and against `buchberger_reference`, over all three orders, under permuted generators,
duplicated generators, and redundant generators. Differential tests over generator orderings are
required, not optional: an unsound criterion typically survives the fixed corpus and fails on a
permutation.

**Owns** `src/grobner/pairs.rs`, `src/grobner/buchberger.rs`.
**Must not** modify F4 matrix construction, symbolic preprocessing, or elimination.

### 5.4 M16-D — Dense and adaptive finite-field linear algebra

**Hypothesis.** Fill-in reaches 13.6x and the F4-shaped sparse benchmark goes from 13 ms to 221 ms
for a 2x shape increase, so above some density a dense representation wins. M15 §7.3 could not
locate the crossover because it compared sparse row echelon against dense *reduced* row echelon —
strictly more work — and so is not evidence of anything about storage.

**The first deliverable is therefore a fair comparison**: dense row echelon, same pivot rule, same
normalization, same field, same input matrices, with representation-conversion time reported
separately from algorithm time.

**Then** adaptive strategies: dense row accumulators, per-row representation switching,
density-aware pivoting, dense treatment of selected blocks, buffer reuse. Note explicitly that
**global density can stay low while individual rows or blocks become dense** — M15's 13.6x is a
ratio of peak live entries to as-built entries on a matrix with thousands of columns, which is
consistent with a few very dense rows and is not evidence that the matrix is dense. A selection
policy keyed on global density would therefore be keyed on the wrong number.

**Reject** any adaptive policy whose crossover is not established by measurement. A dense backend
that loses everywhere is still a deliverable, as the honest answer to M15's open question.

**Correctness.** Dense and sparse agree on rank and row space over rectangular, singular, sparse,
dense, and fill-in-heavy matrices and over GF(7), GF(13), GF(541), GF(2^31 - 1), and a 64-bit
prime. `reduce_rows_against_pivots_with` honours the contract in §4.2 under every backend. Backend
choice cannot change a Gröbner basis: that is asserted end to end.

**Owns** `src/linalg/**`.
**Must not** modify F4 symbolic preprocessing or candidate extraction.

## 6. Baseline measurements

Machine: AMD Ryzen Threadripper PRO 5995WX, 64 cores / 128 threads, 503 GB RAM.
`rustc 1.97.0 (2d8144b78 2026-07-07)`, `cargo 1.97.0`. Release profile (`[profile.release]` is
Cargo's default: `opt-level = 3`, `debug-assertions = false`, `overflow-checks = false`).
Criterion 0.5 with `sample_size(10)`. GF(2^31 - 1) for performance, GF(7)/GF(13)/GF(541) and a
64-bit prime for correctness.

Measured at the M16-0 commit on `feat/m16-foundation`, which is the commit all four
implementation branches are based on.

### 6.1 The algorithm did not change

From `cargo run --release --example f4_statistics`. Every counter in
[`MILESTONE-F4.md`](MILESTONE-F4.md) §7.1 is reproduced **exactly** at the M16-0 commit: cyclic-5
lex still builds 32 matrices over 1222 Buchberger reductions, katsura-7 grevlex still peaks at
1 390 812 live nonzeros with 13.58x worst fill-in and 95.9% scaffolding, and all 24 rows agree
digit for digit.

That is the point of re-running them. M16-0 refactored pair scheduling onto leading monomials,
moved the product criterion into the queue, routed elimination through a backend selector, and
added an observer to the main loop. None of it changed what the algorithm does, and the counters
are how that is established rather than asserted.

### 6.2 Where the time actually goes

From `cargo run --release --example f4_profile`, which is new in M16-0. `other` is the total less
every stage: pair selection and basis bookkeeping. Milliseconds.

| system | order | total | symbolic | construction | elimination | extraction | interreduction | other |
|---|---|---|---|---|---|---|---|---|
| cyclic-4 | lex | 0.27 | 0.07 | 0.08 | 0.07 | 0.01 | 0.02 | 0.02 |
| cyclic-5 | lex | 29.97 | 3.39 | 5.20 | 14.69 | 0.24 | 6.09 | 0.36 |
| cyclic-5 | grlex | 21.79 | 2.20 | 3.44 | 14.68 | 0.16 | 0.87 | 0.44 |
| cyclic-5 | grevlex | 25.31 | 2.10 | 3.59 | **18.36** | 0.20 | 0.73 | 0.33 |
| katsura-4 | lex | 0.63 | 0.13 | 0.19 | 0.22 | 0.02 | 0.04 | 0.03 |
| katsura-5 | lex | 15.64 | 2.36 | 3.90 | 6.79 | 0.16 | 2.16 | 0.27 |
| katsura-5 | grlex | 1.95 | 0.32 | 0.52 | 0.74 | 0.04 | 0.27 | 0.05 |
| katsura-5 | grevlex | 1.87 | 0.29 | 0.48 | 0.72 | 0.04 | 0.30 | 0.05 |
| katsura-6 | lex | 2963.26 | 40.55 | 68.87 | 371.02 | 1.44 | **2479.28** | 2.09 |
| katsura-6 | grlex | 22.69 | 2.40 | 4.29 | 13.55 | 0.22 | 2.00 | 0.23 |
| katsura-6 | grevlex | 27.01 | 2.12 | 3.63 | **18.04** | 0.20 | 2.83 | 0.20 |
| katsura-7 | grlex | 509.23 | 24.58 | 37.00 | **412.53** | 1.30 | 32.37 | 1.44 |
| katsura-7 | grevlex | 896.32 | 19.05 | 34.09 | **791.81** | 1.82 | 45.30 | 4.25 |
| random-4 | lex | 7.73 | 1.33 | 2.27 | 3.74 | 0.10 | 0.13 | 0.16 |
| planted-6 | lex | 0.06 | 0.01 | 0.01 | 0.01 | 0.00 | 0.02 | 0.01 |

Three results here matter more than the rest, and two of them contradict the priority order the
preceding milestone proposed.

**Elimination is the computation.** 65% to 88% of the total on every instance above a millisecond:
791 of 896 ms on katsura-7 grevlex, 412 of 509 on katsura-7 grlex, 18.0 of 27.0 on katsura-6
grevlex. The linear algebra is where the time is, which is what M16-A and M16-D are aimed at, and
the measurement supports aiming there.

**Symbolic preprocessing is 2% to 15%, and it is smallest exactly where the reducer share is
largest.** katsura-7 grevlex is 95.9% scaffolding and spends **2.1%** of its time in symbolic
preprocessing. The preceding milestone put "reuse reducer multiples across batches" first on the
M16 list, on the strength of that 95.9%. The stage breakdown says the reducer rows are expensive
because they make the *matrix* larger — which elimination then pays for — and not because finding
them is slow. **Caching the rows attacks 2% of the cost; producing fewer of them attacks the 88%.**
That reorders M16-B: the valuable hypothesis is smaller multipliers, not reuse. The repetition rate
should still be measured, and `CacheMode::Count` exists to measure it, but the ceiling on what a
cache can win is now known and it is low.

**The final interreduction is 84% of katsura-6 under lex.** 2479 ms of 2963. That instance builds
59 matrices and returns a six-element basis, so the cost is neither in the matrices nor in the
answer but in `reduce_grobner_basis` between them. No counter in the preceding milestone could have
shown this, and it is the largest single cost anywhere in this baseline — larger than every
elimination in the table put together. It is a real finding, it is in shared machinery both engines
use, and §5.3 assigns it.

The suspects are visible in the code rather than needing a profiler: `minimize_grobner_basis`
deduplicates with `monic.contains(&scaled)`, which is a full polynomial equality against every
element kept so far; it then calls `leading_monomial` — a scan of the whole term map — inside a
double loop over the basis; and `reduce_grobner_basis` clones all `n - 1` other polynomials once
per element before taking a normal form. All three are quadratic in the pre-interreduction basis
size with a large constant, and katsura-6 lex is where that basis is both long and wide.

### 6.3 Divisor lookup really is a linear scan

From the same run. `scan/q` is basis elements examined per divisor query — one for a perfect index,
and the basis size for a scan.

| system | order | reducer rows | divisor queries | scan steps / query |
|---|---|---|---|---|
| cyclic-4 | grevlex | 102 | 151 | 4.7 |
| cyclic-5 | lex | 4823 | 5372 | 19.8 |
| katsura-5 | lex | 3186 | 3661 | 21.6 |
| katsura-6 | lex | 31816 | 33758 | **47.2** |
| katsura-6 | grevlex | 4572 | 4816 | 5.7 |
| katsura-7 | grlex | 12388 | 13073 | 22.0 |
| katsura-7 | grevlex | 25908 | 26503 | 6.1 |

The scan is confirmed, and it is worst under lex, where the intermediate basis is longest. It is
also, per §6.2, a scan inside the stage that costs 2% to 15% — so an index is worth having and is
not worth very much. The two facts belong together, and reporting the first without the second is
how a milestone spends itself on the wrong thing.

### 6.4 Reducer-multiple repetition

`CacheMode::Count` records which `(basis_index, multiplier)` pairs recur across batches without
serving anything, so the rate is measurable at the baseline. M16-B reports it; the measurement is
the gate on whether `CacheMode::Store` is implemented at all.

### 6.5 Wall clock

From `cargo bench --bench grobner`, Criterion medians at sample size 10, both engines on identical
inputs.

> Measured at the M16-0 commit and recorded in §6.6 below.

## 7. Results

> Per-workstream results are appended here by A, B, C and D; the integrated result and the
> ablation study by M16-I.

## 8. References

1. Faugère, J.-C. (1999). *A new efficient algorithm for computing Gröbner bases (F4)*. Journal of
   Pure and Applied Algebra 139, 61–88. <https://doi.org/10.1016/S0022-4049(99)00005-5>
2. Gebauer, R., Möller, H. M. (1988). *On an installation of Buchberger's algorithm*. Journal of
   Symbolic Computation 6, 275–286. <https://doi.org/10.1016/S0747-7171(88)80048-8>
3. Buchberger, B. (1979). *A criterion for detecting unnecessary reductions in the construction of
   Gröbner bases*. EUROSAM '79, LNCS 72, 3–21.
4. Cox, D., Little, J., O'Shea, D. *Ideals, Varieties, and Algorithms*, Sec. 2.9–2.10, for the
   product and chain criteria and their soundness proofs.
5. Faugère, J.-C., Lachartre, S. (2010). *Parallel Gaussian elimination for Gröbner bases
   computations in finite fields*. PASCO '10, 89–97, for the block structure of a Macaulay matrix.
6. Demin, A., Gowda, S. *Groebner.jl*. <https://arxiv.org/abs/2304.06935>, and
   <https://github.com/sumiya11/Groebner.jl> for implementation architecture.
7. msolve — <https://github.com/algebraic-solving/msolve>, a mature F4 implementation.
8. The preceding milestone: [`MILESTONE-F4.md`](MILESTONE-F4.md).

Published algorithm descriptions are the primary references. Existing implementations are read for
architecture and performance strategy, under their own licenses; no code is copied.

### 7.3 M16-C — critical-pair criteria and interreduction

Two deliverables, reported separately because they are independent changes to the same workstream's
files. Counters are deterministic and are the primary evidence. Wall clock was taken on the §6
machine in release, but **three sibling workstreams were building on it concurrently**, so the
times below are indicative and the integrator's serial run is authoritative. The counters are not
affected by that.

Measured at `20b6602` on `feat/m16-pair-criteria`, against the `a11cbab` M16-0 baseline.

#### 7.3.1 The interreduction

§6.2 found `reduce_grobner_basis` to be 2479 ms of katsura-6 lex's 2963 ms. **None of the cost was
in the three suspects §5.3.1 named.** Instrumenting the function directly:

| | katsura-6 lex |
|---|---|
| pre-interreduction basis | 113 elements, 3660 terms |
| minimal basis | 6 elements, 174 terms |
| `minimize_grobner_basis` | 0.5 ms |
| the interreduction loop | 2534 ms |

So the quadratic deduplication and the double `leading_monomial` scan together account for 0.02% of
it, and the cloned divisor slice cannot account for anything: there are six polynomials of 174
terms to clone. All of the cost is two calls to `normal_form`, one of 1.27 s each:

```text
ELEM 0 lead=x1   7 terms -> 33 terms in 1.272936527s
ELEM 1 lead=x2  32 terms -> 32 terms in 1.271073570s
ELEM 2 lead=x3  35 terms -> 32 terms in  22.750310ms
ELEM 3 lead=x4  36 terms -> 32 terms in 374.489000µs
ELEM 4 lead=x5  32 terms -> 32 terms in  11.873000µs
ELEM 5 lead=x6^32                      in   9.819000µs
```

The cause is substitution depth, not basis size. That basis is in shape position: five elements
with linear leading monomials over one univariate of degree 32. Reducing the tail of the `x1`
element against an **unreduced** `x2` element substitutes 31 terms, each of which then has to be
reduced against an unreduced `x3` element, and so on down the chain — and the elements were being
reduced in descending leading-monomial order, which is the worst possible one.

**The fix is to interreduce in ascending leading-monomial order, writing each remainder back in
place.** Every divisor below the element being reduced is then already fully reduced, so a
substitution introduces monomials that are already in normal form. The element being reduced is
swapped to the end of the vector so that the others are a contiguous slice, which removes the clone
as well and needs no change to `normal_form`'s interface.

This cannot change the answer, and the argument is worth stating because it is what makes the
reordering safe. A remainder `r` is congruent to its element modulo the ideal, has that element's
leading monomial — minimization left it divisible by no other leading monomial, so division cannot
cancel it — and has no monomial divisible by any other element's leading monomial. Two elements
with those three properties differ by an ideal member all of whose monomials are irreducible, which
is zero. So `r` depends only on the element's leading monomial, and not on which divisor was
applied first or on whether a divisor's tail had been reduced yet; those change only how many steps
the reduction takes. Reducing an element never changes its leading monomial, which is all that
divisibility is tested against.

Interreduction, milliseconds, baseline criteria in both columns:

| system | order | M16-0 | M16-C | |
|---|---|---|---|---|
| cyclic-5 | lex | 6.09 | 0.37 | 16.5x |
| cyclic-5 | grlex | 0.87 | 0.65 | |
| katsura-5 | lex | 2.16 | 0.16 | 13.5x |
| **katsura-6** | **lex** | **2479.28** | **1.04** | **2384x** |
| katsura-6 | grlex | 2.00 | 1.75 | |
| katsura-6 | grevlex | 2.83 | 2.54 | |
| katsura-7 | grlex | 32.37 | 29.12 | |
| katsura-7 | grevlex | 45.30 | 39.85 | |

katsura-6 lex as a whole goes from 2963 ms to 520 ms. The instances that barely move are the ones
whose minimal basis is large — katsura-7 grlex returns 64 elements and 4663 terms — where the
reduction is work that genuinely has to be done rather than work done twice. Interreduction is
still the largest single stage on those two instances after the criteria are enabled.

Both engines call this function, so classical Buchberger gets the same improvement; its *result*
does not move, which the existing reference-agreement tests and a new differential test against the
naive formulation both check.

The minimization was also cleaned up — leading monomials taken once rather than once per
comparison, and duplicates compared only against elements sharing a leading monomial and term
count — but on the evidence above that is tidiness, not a measured win, and it is reported as such.

#### 7.3.2 The criteria

Buchberger's chain criterion at selection time and Gebauer–Möller pair-set minimization at
insertion time, both in `pairs.rs` and so available to both engines, each behind its own flag.

**The soundness conditions, as implemented.** The chain criterion is Cox, Little and O'Shea's
`Criterion(f_i, f_j, B)` (*Ideals, Varieties, and Algorithms* §2.10): discard `(i, j)` when some
`k ∉ {i, j}` has `LM(f_k)` dividing `lcm(LM f_i, LM f_j)` **and** neither `(i, k)` nor `(k, j)` is
in `B`. Gebauer–Möller is the published installation (Gebauer & Möller 1988, criteria B, M and F;
Becker & Weispfenning, *Gröbner Bases*, Algorithm 5.5 `UPDATE`): B discards a pending `(g1, g2)`
when `LM(h)` divides its lcm and **both** `lcm(LM g1, LM h)` and `lcm(LM h, LM g2)` differ from it;
M keeps one new pair per lcm under divisibility; F drops a relatively prime new pair *after* it has
served as an lcm representative under M, which is why F is a second pass.

Two points where the implementation is deliberately stronger than a naive reading, both stated in
the code:

1. "In `B`" is read as **"selected and processed"**, not "absent from the pending set". A pair
   selected in the same F4 batch has left the pending set but has not been reduced, and three pairs
   on one another's lcms could then each be discarded on the strength of the other two. A pair
   Gebauer–Möller removed is likewise absent from the pending set, and its own redundancy is
   justified by two pairs that are still pending — letting it witness one of those closes the loop.
   With Gebauer–Möller off, every pair leaves the pending set by being selected, so the two
   readings coincide and this is exactly the published criterion.
2. Gebauer–Möller's criterion F is Buchberger's first criterion, so it is applied only when
   `PairCriteria::product` is also set, and its eliminations are counted under `gebauer_moller` so
   that `product` keeps meaning what the baseline measured.

The invariant both installations maintain is the same: every pair not in `B` has a standard
representation modulo the final basis, justified either by a pair processed strictly earlier or by
pairs whose lcm divides its own strictly. That is what makes the justification well-founded rather
than circular, and it is why (1) is not optional.

**F4: pairs reduced, matrices built, largest matrix.** From
`cargo run --release --example pair_criteria`. `product` is the measured baseline. `chain` is
product plus the chain criterion; `gm` is product plus Gebauer–Möller; `all` is all three.

| system | order | criteria | batches | reduced | prod | chain | gm | max rows | ms |
|---|---|---|---|---|---|---|---|---|---|
| cyclic-5 | lex | product | 32 | 948 | 180 | 0 | 0 | 565 | 23.6 |
| cyclic-5 | lex | chain | 23 | 212 | 187 | 777 | 0 | 160 | 4.8 |
| cyclic-5 | lex | gm | 24 | 106 | 0 | 0 | 1169 | 161 | 3.7 |
| cyclic-5 | grevlex | product | 22 | 868 | 167 | 0 | 0 | 635 | 25.5 |
| cyclic-5 | grevlex | chain | 14 | 204 | 167 | 664 | 0 | 161 | 3.2 |
| cyclic-5 | grevlex | gm | 14 | 116 | 0 | 0 | 919 | 110 | 2.0 |
| katsura-5 | lex | product | 29 | 593 | 353 | 0 | 0 | 381 | 13.8 |
| katsura-5 | lex | chain | 19 | 188 | 353 | 405 | 0 | 166 | 4.6 |
| katsura-5 | lex | gm | 20 | 50 | 0 | 0 | 896 | 38 | 0.9 |
| katsura-6 | lex | product | 59 | 4611 | 1717 | 0 | 0 | 1954 | 556.8 |
| katsura-6 | lex | chain | 38 | 785 | 1648 | 3345 | 0 | 790 | 68.9 |
| katsura-6 | lex | gm | 107 | 231 | 0 | 0 | 20884 | 92 | 23.2 |
| katsura-6 | grlex | product | 9 | 387 | 279 | 0 | 0 | 644 | 26.3 |
| katsura-6 | grlex | chain | 6 | 214 | 279 | 173 | 0 | 378 | 9.9 |
| katsura-6 | grlex | gm | 6 | 103 | 0 | 0 | 563 | 353 | 6.5 |
| katsura-6 | grevlex | product | 8 | 147 | 129 | 0 | 0 | 1388 | 33.1 |
| katsura-6 | grevlex | chain | 6 | 93 | 129 | 54 | 0 | 754 | 9.4 |
| katsura-6 | grevlex | gm | 6 | 68 | 0 | 0 | 208 | 670 | 6.9 |
| katsura-7 | grlex | product | 11 | 1553 | 862 | 0 | 0 | 2450 | 573.8 |
| katsura-7 | grlex | chain | 7 | 616 | 862 | 937 | 0 | 1046 | 122.3 |
| katsura-7 | grlex | gm | 7 | 264 | 0 | 0 | 2151 | 1051 | 76.8 |
| katsura-7 | grevlex | product | 10 | 555 | 348 | 0 | 0 | 6810 | 928.2 |
| katsura-7 | grevlex | chain | 7 | 243 | 348 | 312 | 0 | 2817 | 146.7 |
| katsura-7 | grevlex | gm | 7 | 166 | 0 | 0 | 737 | 2633 | 110.9 |

Both criteria pay on every instance, and they pay in the currency the hypothesis named: fewer
matrices, and smaller ones. Gebauer–Möller is the stronger of the two throughout, and
**`all` is identical to `gm` in every row** — `chain` is 0 whenever Gebauer–Möller is on. That is
the expected consequence of §7.3.2 (1): a pair Gebauer–Möller removed never becomes a chain
witness, and the pair set Gebauer–Möller maintains is already lcm-minimal, so the selection-time
criterion has nothing left to find. The chain criterion earns its place as the criterion that works
without insertion-time bookkeeping, not as an addition to Gebauer–Möller.

katsura-6 lex is the one row where Gebauer–Möller *increases* the batch count, 59 to 107. It is
building many more, far smaller matrices — 92 rows against 1954 — and is 24x faster for it.

**Classical Buchberger.** From `cargo run --release --example pair_criteria -- buchberger`.

| system | order | criteria | considered | reduced | zero | prod | chain | gm | ms |
|---|---|---|---|---|---|---|---|---|---|
| katsura-4 | lex | product | 153 | 84 | 70 | 69 | 0 | 0 | 1.1 |
| katsura-4 | lex | chain | 153 | 25 | 11 | 69 | 59 | 0 | 0.4 |
| katsura-4 | lex | gm | 16 | 16 | 2 | 0 | 0 | 137 | 0.2 |
| katsura-5 | lex | product | 2415 | 1790 | 1725 | 625 | 0 | 0 | 184.2 |
| katsura-5 | lex | chain | 3240 | 134 | 58 | 813 | 2293 | 0 | 12.4 |
| katsura-5 | lex | gm | 162 | 162 | 5 | 0 | 0 | 12879 | 35.7 |
| katsura-5 | grevlex | product | 105 | 49 | 39 | 56 | 0 | 0 | 1.3 |
| katsura-5 | grevlex | chain | 105 | 33 | 23 | 56 | 16 | 0 | 0.8 |
| katsura-5 | grevlex | gm | 30 | 30 | 20 | 0 | 0 | 75 | 0.8 |
| cyclic-5 | grlex | product | 1653 | 1454 | 1401 | 199 | 0 | 0 | 63.6 |
| cyclic-5 | grlex | chain | 1653 | 144 | 91 | 199 | 1310 | 0 | 5.6 |
| cyclic-5 | grlex | gm | 147 | 147 | 94 | 0 | 0 | 1506 | 5.5 |
| katsura-6 | grlex | product | 666 | 387 | 356 | 279 | 0 | 0 | 37.6 |
| katsura-6 | grlex | chain | 666 | 133 | 102 | 279 | 254 | 0 | 11.0 |
| katsura-6 | grevlex | product | 276 | 147 | 129 | 129 | 0 | 0 | 14.5 |
| katsura-6 | grevlex | chain | 276 | 73 | 55 | 129 | 74 | 0 | 5.4 |

In the classical engine **neither criterion dominates**: on katsura-5 lex the chain criterion
reduces 134 pairs to Gebauer–Möller's 162 and is 2.9x faster, because Gebauer–Möller's criterion B
rescans the pending set on every insertion and that set is longest under lex. Elsewhere
Gebauer–Möller wins. Zero reductions — the pairs Buchberger pays full price to discover are
useless — fall from 1725 to 58 on katsura-5 lex, which is the clearest statement of what these
criteria are for.

**Combined, against the M16-0 baseline.** Both deliverables, from
`cargo run --release --example f4_profile -- c` against §6.2. Total milliseconds.

| system | order | M16-0 | M16-C | |
|---|---|---|---|---|
| cyclic-5 | lex | 29.97 | 3.85 | 7.8x |
| cyclic-5 | grevlex | 25.31 | 1.97 | 12.8x |
| katsura-5 | lex | 15.64 | 1.02 | 15.3x |
| **katsura-6** | **lex** | **2963.26** | **23.36** | **127x** |
| katsura-6 | grlex | 22.69 | 6.85 | 3.3x |
| katsura-6 | grevlex | 27.01 | 7.66 | 3.5x |
| katsura-7 | grlex | 509.23 | 76.41 | 6.7x |
| katsura-7 | grevlex | 896.32 | 105.86 | 8.5x |
| random-4 | lex | 7.73 | 1.03 | 7.5x |

**This moves the bottleneck, which the other workstreams should know.** §6.2's headline was that
elimination is 65–88% of the computation. With the criteria enabled it is 2.84 ms of katsura-6 lex's
23.36 — 12% — and symbolic preprocessing is now the largest stage there at 6.95 ms. On katsura-7
the ranking is unchanged and elimination is still 41–51%, with interreduction second. The criteria
do not make elimination faster; they remove rows, which makes the matrices small enough that the
other stages matter.

**Defaults are unchanged.** `F4Options::default()` and `PairCriteria::default()` are still the
measured baseline, per §4.1: M16-I moves the default deliberately. On this evidence the
configuration to move it to is `PairCriteria::ALL`, which is `gebauer_moller` plus `product` in
effect.

#### 7.3.3 Correctness

- Every one of the eight criteria combinations returns the criteria-free computation's basis
  exactly, in **both** engines, over all three orders: the 22-system corpus, every rotation and the
  reversal of each generator list, a duplicated generator, a scalar multiple, a generator already
  in the ideal, inconsistent systems, and 24 randomized sparse quadratic systems over GF(7) and
  GF(13).
- A regression test pins the unsound shortcut: three leading monomials each dividing the lcm of the
  other two, where naive lcm-divisibility fires on the first pair selected and the sound criterion
  must not.
- Hand-verified unit tests assert *which* criterion eliminated a pair, one per Gebauer–Möller
  condition.
- The interreduction is checked against the naive formulation element for element, on
  pre-interreduction bases rather than on finished ones, plus the four properties it is defined by
  and idempotence.
- `test_pair_criteria_do_not_change_the_basis`,
  `test_every_configuration_agrees_with_the_baseline`, and both slow `#[ignore]`d
  engine-agreement tests pass unchanged. 703 tests pass in debug and release.

#### 7.3.4 Notes for the integrator

- `Statistics` (classical Buchberger) gained a `criteria: CriterionCounts` field, which forced a
  one-line addition to the exhaustive destructuring pattern in `examples/grobner_statistics.rs`.
  That is the only edit to existing content in an append-only file.
- `examples/pair_criteria.rs` is new and reports the tables above.
- No interface change is needed outside M16-C's files. In particular `normal_form` was left alone:
  swapping the element under reduction to the end of the vector makes the other elements a
  contiguous slice, so the clone §5.3.1 identified can be removed without touching `src/poly`.
