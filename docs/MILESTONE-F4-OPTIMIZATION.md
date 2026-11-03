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

### 7.2 M16-B — symbolic preprocessing and monomial indexing

All three hypotheses §5.2 names were implemented and measured. **All three were rejected**, two of
them after the code that implements them had been written and benchmarked. What did pay was none of
them: it was how a monomial is hashed, which is what the three measurements kept pointing at.

The default configuration is unchanged — `ReducerSelection::FirstApplicable`, `CacheMode::Off` —
and `f4` returns the identical basis under every selection policy, every cache mode and all three
orders, which `test_every_configuration_agrees_with_the_baseline` asserts over the cross product.

Measured on the §6 machine and toolchain, release profile, `cargo run --release --example
f4_selection` and `--example f4_profile`. **Caveat:** three sibling workstreams were building and
running on the same machine throughout, so every wall clock here is from an interleaved A/B of two
binaries run back to back, five rounds, median reported — not from an idle machine. The counters
(`reducers`, `rows`, `cols`, `peak nz`, `row ops`, `scan/q`, `reuse`) are deterministic and are not
affected. The authoritative serial timing is the integrator's.

#### 7.2.1 Rejected: smaller multipliers (`ReducerSelection::LargestLeadingMonomial`)

Implemented as specified: the divisor whose leading monomial is largest under the order in force,
ties broken by the smaller basis index — a tiebreaker that is needed, since two basis elements can
lead with the same monomial, and is exercised by `test_find_largest_divisor_tiebreak`.

The hypothesis was that the smallest multiplier introduces the fewest new monomials, so the closure
and the matrix shrink. **It is the other way round on every instance that matters.**

| system | order | reducers first → largest | largest matrix | peak nz | row ops | total/ms |
|---|---|---|---|---|---|---|
| cyclic-4 | lex | 117 → **105** | 28x29 → 26x26 | 128 → 106 | 278 → 252 | 0.25 → **0.17** |
| cyclic-5 | lex | 4823 → **4550** | 565x351 → 532x337 | 13993 → 12200 | 58164 → 56522 | 27.9 → **25.2** |
| cyclic-5 | grlex | 1614 → 1779 | 732x228 → 726x277 | 11379 → 12019 | 93664 → 98404 | 20.5 → 23.5 |
| cyclic-5 | grevlex | 3292 → 4418 | 635x463 → 873x712 | 17061 → 55309 | 79775 → 114079 | 23.3 → 50.0 |
| katsura-5 | lex | 3186 → 3186 | unchanged | unchanged | unchanged | 13.0 → 13.4 |
| katsura-5 | grevlex | 666 → 842 | 278x291 → 390x403 | 7818 → 8907 | 3179 → 4334 | 1.63 → 2.19 |
| katsura-6 | lex | 31816 → 31816 | unchanged | unchanged | unchanged | 3005 → 3177 |
| katsura-6 | grlex | 2728 → 3913 | 644x674 → 1262x1292 | 34746 → 65129 | 50043 → 66236 | 22.1 → 36.7 |
| katsura-6 | grevlex | 4572 → 6371 | 1388x1412 → 2593x2623 | 103314 → 209347 | 44023 → 63388 | 28.6 → 61.4 |
| katsura-7 | grlex | 12388 → 22105 | 2450x2476 → 6946x7008 | 368156 → 1017564 | 638769 → 964997 | 544 → 1228 |
| katsura-7 | grevlex | 25908 → **43453** | 6810x6862 → **16750x16812** | 1.39M → **3.06M** | 608356 → 1068505 | 887 → **3045** |

katsura-7 under grevlex — the instance §6.2 identifies as the one to fix — gets a 68% larger
closure, a 2.5x larger matrix, 2.2x the peak live entries and takes **3.4x as long**. The only wins
are the lex instances of cyclic, where the closure shrinks 2–6% and the computation gets 7–10%
shorter.

The mechanism is visible once stated the right way round. The reducer row for a monomial `u` is
`(u / LM(g)) * g`, and its leading monomial is `u` whichever `g` is chosen — the multiplier's size
is not what the matrix pays for. What the matrix pays for is the row's *tail*, `(u / LM(g)) * t` for
each tail monomial `t` of `g`. A small `g` low in the basis has a tail far below its own leading
monomial, so dividing through by a large multiplier drops those monomials well down the order, where
they are likelier to be irreducible or already covered. A large `g` has a tail close to `LM(g)`, so
the tail of its multiple sits just below `u` — reducible, and each reducible monomial is another
row. Choosing the largest divisor minimizes the multiplier and maximizes the fan-out.

**Kept, not merged into the default.** The variant is reachable through `F4Options` because the
option surface declares it and the ablation study needs it; `FirstApplicable` remains the default
and the measurement above is why.

#### 7.2.2 Rejected: a divisibility index (`src/grobner/f4/divisors.rs`, reverted)

Built, tested against the reference scan, measured, and reverted in commit `fcf81df`. The structure
grouped the leading monomials by total degree — necessary condition `deg LM <= deg u` — and gave
first-applicable selection a precomputed ascending list of the indices at or below the query's
degree, so the scan it replaced was restricted to a subsequence of itself in the same order. That
construction is what makes the answer provably identical; a plainer walk over the degree groups is
not, because a divisor found in a low-degree group does not license skipping a lower-indexed one
above it — and measured, that walk examined **more** elements than the plain scan (katsura-6 lex
47.2 → 48.5).

It did reduce examinations, and it was still slower:

| system | order | scan/q scan → index | symbolic/ms scan → index |
|---|---|---|---|
| cyclic-4 | grevlex | 4.7 → 3.8 | 0.05 → 0.05 |
| cyclic-5 | lex | 19.8 → 17.9 | 3.26 → 3.27 |
| cyclic-5 | grlex | 17.4 → 12.0 | 2.25 → 2.34 |
| katsura-5 | lex | 21.6 → 19.6 | 2.27 → 2.30 |
| katsura-6 | lex | **47.2 → 44.7** | 42.8 → 44.0 |
| katsura-6 | grevlex | 5.7 → 5.3 | 2.40 → 2.48 |
| katsura-7 | grlex | 22.0 → 20.5 | **23.9 → 28.4** |
| katsura-7 | grevlex | 6.1 → 5.8 | **20.2 → 23.6** |

The scan it replaced is sequential, and that is the whole of it. Examining elements `0, 1, 2, ...`
walks one array in order and the prefetcher covers it; examining `0, 2, 5, 7, ...` reads the same
array through an index list and can take a cache miss per skip. Fewer examinations bought more
misses than they saved divisions.

**And the divisions were never the cost.** katsura-6 under lex performs 33 758 divisor queries at
47.2 elements each — 1.59 million divisibility tests, each a handful of integer comparisons — inside
a stage that is 41 ms of a 3005 ms computation. Eliminating divisor lookup *entirely* would save
about 1% of the symbolic stage's share of 1.4%. §6.3 reports the scan correctly and the scan is
nonetheless not worth indexing; the two facts belong together.

A support bitmask over the variables was measured alongside and also rejected: for these bases the
mask rarely rejects, so it adds a word operation ahead of a `checked_div` that already exits on the
first variable it fails.

#### 7.2.3 Rejected: reducer reuse (`CacheMode::Store`, measured and not merged)

`CacheMode::Count` first, as §5.2 requires, before anything was implemented. **The repetition rate
is high** — the preceding milestone's expectation of recurrence was right:

| system | order | reducer rows | reused | rate |
|---|---|---|---|---|
| cyclic-4 | lex | 117 | 34 | 29% |
| cyclic-5 | lex | 4823 | 2796 | 58% |
| cyclic-5 | grevlex | 3292 | 1417 | 43% |
| katsura-4 | lex | 292 | 225 | 77% |
| katsura-5 | lex | 3186 | 2841 | **89%** |
| katsura-6 | lex | 31816 | 30169 | **95%** |
| katsura-6 | grevlex | 4572 | 2763 | 60% |
| katsura-7 | grlex | 12388 | 7974 | 64% |
| katsura-7 | grevlex | 25908 | 16485 | 64% |
| random-4 | lex | 2314 | 2077 | **90%** |

So the gate §5.2 set is passed, and `CacheMode::Store` was implemented: the shifted terms of a
multiple — not its sparse row, whose column indices belong to one batch's column set — stored and
served. It is slower everywhere, at every one of those rates:

| system | order | reuse | symbolic/ms off → count → store |
|---|---|---|---|
| cyclic-5 | lex | 58% | 1.60 → 1.72 → 1.89 |
| katsura-5 | lex | 89% | 1.00 → 1.06 → 1.09 |
| katsura-6 | lex | 95% | 20.3 → 21.8 → 21.9 |
| katsura-6 | grevlex | 60% | 1.05 → 1.12 → 1.27 |
| katsura-7 | grlex | 64% | 13.2 → 13.9 → 14.8 |
| katsura-7 | grevlex | 64% | 9.9 → 11.8 → **14.9** |

The rate was the wrong question. What a cache avoids is building a multiple's terms, and that is one
integer addition per variable per term — a few nanoseconds for a monomial. Serving them instead
costs a hash of `(basis_index, multiplier)` and a pointer chase to a heap vector, which is more.
A 95% hit rate on work that cheap still loses. `Store` is left delegating to `Count`, and its doc
comment records the measurement.

#### 7.2.4 Merged: how a monomial is hashed

The three rejections agree on where the stage's time actually is. It is not the divisor scan and it
is not rebuilding multiples; it is the two hash-set operations the closure traversal performs for
every monomial it meets — `examined.insert`, to handle no monomial twice, and `covered.contains`, to
ask whether the invariant already holds there.

`Monomial<N>` is `[u32; N]`, which the standard library hashes through `hash_slice` as one byte
slice, under `SipHash-1-3`. SipHash is the default because it withstands adversarially chosen keys.
These keys are monomials the computation produced itself, and a caller who can choose them can
already choose the ideal, so the guarantee buys nothing here. A multiplicative word hash with a
`splitmix64` finalizer replaces it:

| system | order | symbolic/ms | total/ms |
|---|---|---|---|
| cyclic-4 | lex | 0.07 → 0.05 (−29%) | 0.30 → 0.25 |
| cyclic-5 | lex | 3.22 → 1.64 (−49%) | 29.7 → 27.6 |
| cyclic-5 | grlex | 2.25 → 1.19 (−47%) | 22.7 → 21.3 |
| cyclic-5 | grevlex | 1.83 → 0.96 (−48%) | 24.0 → 23.3 |
| katsura-4 | lex | 0.13 → 0.07 (−46%) | 0.63 → 0.56 |
| katsura-5 | lex | 2.23 → 1.11 (−50%) | 15.3 → 14.1 |
| katsura-5 | grevlex | 0.29 → 0.15 (−48%) | 1.91 → 1.74 |
| katsura-6 | lex | 41.1 → 19.4 (−53%) | 2997 → 2988 |
| katsura-6 | grlex | 2.40 → 1.25 (−48%) | 23.7 → 23.7 |
| katsura-6 | grevlex | 2.34 → 1.06 (−55%) | 31.4 → 28.7 |
| katsura-7 | grlex | 23.6 → 13.9 (−41%) | 559 → 512 |
| katsura-7 | grevlex | 18.9 → 9.63 (−49%) | 904 → 851 |
| random-4 | lex | 1.46 → 0.68 (−53%) | 8.42 → 7.29 |

Symbolic preprocessing roughly halves — 25% to 55% off, about −50% on everything above a
millisecond. The totals move 0% to 19%, which is what a stage worth 2–15% can contribute, and
katsura-6 under lex barely moves at all because §6.2's interreduction finding owns 84% of it.

Two details are load-bearing, and both were found by measuring rather than by reasoning:

- **Without the finalizer it is twice as slow as SipHash.** The low bits of a multiplicative
  accumulator depend only on the low bits of the key, and `hashbrown` takes the bucket index from
  exactly those bits. Small exponent vectors collided enough to double the stage. Two shifts and a
  multiply fix it. `test_monomial_hasher` compares the low-bit bucket spread against the standard
  hasher so this cannot regress silently.
- **A byte-at-a-time `write` is also slower than SipHash.** It is the hot path, because an integer
  array arrives as one byte slice: 28 rounds for a seven-variable monomial. Eight bytes at a time is
  the version that pays.

Nothing about the computation changes. The hasher affects iteration order of nothing that is read in
order: `Preprocessed::leading_monomials` is used only for membership, and the row sequence is built
in the deterministic order the `VecDeque` traversal produces.

#### 7.2.5 Tests added

In `symbolic.rs`: the closure invariant asserted directly under every selection policy and every
cache mode over the ten-system corpus and all three orders, and over both the widest and narrowest
batch shapes; a differential test of each policy's dispatch against its reference scan over
randomized bases and monomials, asserting the same index *and* the same quotient; a round trip of
every constructed row against independently computed polynomial arithmetic; cache clearing not
changing the rows; the largest-leading-monomial tiebreaker; and the hasher's agreement with equality
and its low-bit spread. In `tests.rs`: identical basis under both policies against `buchberger` over
the corpus, under permuted, duplicated and redundant generators, and determinism of the basis *and*
the counters across repeated runs. 698 library tests pass in debug and in release, 8 ignored, up
from 693 at the baseline.

#### 7.2.6 Notes for the integrator

- **One edit outside M16-B's column, since reverted.** Adding `src/grobner/f4/divisors.rs` required
  `pub mod divisors;` in the frozen `f4/mod.rs`. The revert removed both, so `f4/mod.rs` is
  byte-identical to the baseline on this branch. M16-A will need the same one-line addition for
  `structured.rs`.
- **`ReducerSelection::LargestLeadingMonomial`'s doc comment in `options.rs` says "Not yet
  implemented; currently first-applicable", which is now false.** `options.rs` is frozen, so it was
  left alone. It wants one line: the policy is implemented, and `FirstApplicable` is the default
  because §7.2.1 measured the alternative as 3.4x slower on katsura-7 grevlex.
- **The per-worktree `.cargo/config.toml` does not take effect.** The ambient environment sets
  `CARGO_TARGET_DIR=/buildcache/cargo-target/interactive-mfaulk`, and an environment variable
  overrides `[build] target-dir` in `.cargo/config.toml`. All four workstreams were therefore
  sharing one target directory and overwriting each other's test binaries — which showed up as the
  library test count changing between runs, at one point reporting M16-C's interreduction tests on
  this branch. Every measurement and test run reported here was taken with `CARGO_TARGET_DIR` set
  explicitly to the worktree. Anyone measuring on this machine has to do the same.
- **`cargo test --doc` fails, at the baseline commit too.** `Cargo.toml` sets `[lib] doctest =
  false`, so `cargo test` never runs them and nothing is broken; forcing them finds four untagged
  code fences of prose in `src/fft/evaluate.rs` and `src/linalg/crout.rs` that `rustdoc` tries to
  compile. Pre-existing and untouched here; worth `text` fences at some point outside M16.

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
