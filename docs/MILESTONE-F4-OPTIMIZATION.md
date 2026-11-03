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
inputs under the identical order, at the M16-0 commit. The `M15` columns are the same measurement
from [`MILESTONE-F4.md`](MILESTONE-F4.md) §7.2 on the same machine, so the two are comparable and
the difference is M16-0's own effect.

| system | order | Buchberger | F4 | F4 speedup | M15 Buchberger | M15 F4 |
|---|---|---|---|---|---|---|
| cyclic-3 | lex | 18.4 us | 18.3 us | 1.00x | 19.9 us | 19.2 us |
| cyclic-3 | grlex | 18.3 us | 18.6 us | 0.98x | 20.3 us | 19.1 us |
| cyclic-3 | grevlex | 18.3 us | 20.5 us | 0.89x | 20.6 us | 20.8 us |
| cyclic-4 | lex | 175 us | 180 us | 0.97x | 189 us | 179 us |
| cyclic-4 | grlex | 148 us | **132 us** | 1.12x | 156 us | 134 us |
| cyclic-4 | grevlex | **138 us** | 150 us | 0.92x | 160 us | 158 us |
| cyclic-5 | lex | 47.8 ms | **25.7 ms** | 1.86x | 53.3 ms | 27.1 ms |
| cyclic-5 | grlex | 57.0 ms | **20.1 ms** | 2.83x | 64.3 ms | 21.2 ms |
| cyclic-5 | grevlex | 34.2 ms | **21.6 ms** | 1.58x | 38.8 ms | 23.0 ms |
| katsura-3 | lex | 38.2 us | 41.7 us | 0.92x | 42.5 us | 42.6 us |
| katsura-3 | grlex | 29.5 us | 31.5 us | 0.93x | 32.4 us | 32.4 us |
| katsura-3 | grevlex | 29.8 us | 30.9 us | 0.96x | 33.4 us | 33.6 us |
| katsura-4 | lex | 719 us | **566 us** | 1.27x | 853 us | 567 us |
| katsura-4 | grlex | **200 us** | 233 us | 0.86x | 225 us | 244 us |
| katsura-4 | grevlex | **119 us** | 170 us | 0.70x | 136 us | 177 us |
| katsura-5 | lex | 172 ms | **14.2 ms** | **12.1x** | 191 ms | 14.8 ms |
| katsura-5 | grlex | 2.18 ms | **1.81 ms** | 1.20x | 2.47 ms | 1.92 ms |
| katsura-5 | grevlex | **1.21 ms** | 1.69 ms | 0.71x | 1.31 ms | 1.82 ms |
| katsura-6 | grlex | 36.0 ms | **22.8 ms** | 1.58x | 40.0 ms | 23.9 ms |
| katsura-6 | grevlex | **12.8 ms** | 28.1 ms | **0.46x** | 14.1 ms | 30.2 ms |
| random-3 | lex | 325 us | **278 us** | 1.17x | 362 us | 293 us |
| random-3 | grlex | **48.1 us** | 55.2 us | 0.87x | 53.9 us | 58.0 us |
| random-3 | grevlex | **32.2 us** | 41.3 us | 0.78x | 35.5 us | 42.7 us |
| random-4 | lex | 31.1 ms | **8.04 ms** | **3.86x** | 33.8 ms | 8.46 ms |
| random-4 | grlex | **748 us** | 771 us | 0.97x | 831 us | 805 us |
| random-4 | grevlex | 993 us | **885 us** | 1.12x | 1.09 ms | 940 us |
| planted-6 | lex | 53.4 us | **47.6 us** | 1.12x | 57.7 us | 48.8 us |
| planted-6 | grlex | 35.9 us | 34.8 us | 1.03x | 39.6 us | 37.1 us |
| planted-6 | grevlex | 36.1 us | 34.9 us | 1.04x | 41.1 us | 38.1 us |
| planted-8 | lex | 77.4 us | **66.6 us** | 1.16x | 90.2 us | 72.9 us |
| planted-8 | grlex | 58.8 us | 55.2 us | 1.07x | 66.0 us | 61.2 us |
| planted-8 | grevlex | 57.7 us | 57.1 us | 1.01x | 66.6 us | 62.7 us |

And the instances Buchberger does not finish here, from `grobner_f4_only`:

| system | order | F4 | M15 F4 |
|---|---|---|---|
| katsura-6 | lex | 3.06 s | 3.19 s |
| katsura-7 | grlex | 532 ms | 554 ms |
| katsura-7 | grevlex | 809 ms | 898 ms |

**M16-0 made both engines a few percent faster without changing the algorithm.** Every one of the
36 paired figures is at or below its M15 counterpart: Buchberger by 4% to 16% (katsura-5 lex 191 ms
to 172 ms, planted-8 lex 90.2 us to 77.4 us), F4 by 0% to 10% (katsura-7 grevlex 898 ms to 809 ms,
katsura-6 grevlex 30.2 ms to 28.1 ms). That is the leading-monomial refactor: `leading_monomial` is
a scan of a polynomial's whole term map, the queue asked for one per pair created, and Buchberger
asked for two more per pair to apply the product criterion. Buchberger gains more than F4 because
it creates pairs more often relative to the work it does per pair.

It is also the only *performance* change in M16-0, and it was a side effect of an interface
refactor rather than the point of it. The relative picture is unchanged: **katsura-6 grevlex is
still the worst paired result at 0.46x**, and it remains the milestone's headline target.

The three `grobner_f4_only` figures and the last few paired ones were measured while the four
implementation agents were starting up on the same machine. They came out *faster* than M15 rather
than slower, so the contamination was evidently small, but they are preliminary: §7 records an
authoritative serial re-measurement taken with the machine quiet.

## 7. Results

> Per-workstream results are appended here by A, B, C and D; the integrated result and the
> ablation study by M16-I.

### 7.4 M16-D — dense and adaptive linear algebra

Three backends behind `linalg::echelon`, all running the *same* algorithm — leftmost nonzero
column, first row to reach it, unit pivot, one inverse per pivot — so they agree on the resulting
matrix and on every counter in `EliminationStatistics`, and a comparison between them measures
storage and nothing else. That equality is asserted directly, including on the matrices F4 really
builds.

| backend | storage |
|---|---|
| `Sparse` | sorted-vector rows throughout. The M15 implementation, unchanged. |
| `Dense` | `DenseRows`: the whole matrix densified, eliminated, sparsified again. |
| `Adaptive` | `DenseAccumulator`: sparse pivots, and the row being reduced scattered into a dense buffer that is reused across the elimination. |

**`Adaptive` wins everywhere; `Dense` loses everywhere.** The crossover M15 §7.3 went looking for
does not exist in the range F4 produces, and the reason is not that these matrices are too sparse
for a dense representation to help at the margin — it is that nothing in them is dense at all, at
any granularity. The win that *is* available comes from a mixed representation, not a dense one.

Every wall-clock figure below was taken while three sibling workstreams were building on the same
64-core machine, so absolute times run a few percent above §6.2's. Every ratio is taken within one
session against a baseline measured in that session, which is what the contention does not move.
§7.4.6 reports the same comparison through Criterion, twice, as the stability check.

#### 7.4.1 The confound M15 §7.3 could not remove

M15 compared sparse row echelon against `gauss_jordan_elimination`, which computes the *reduced*
form — a second back-substitution pass the sparse side never performs — and correctly refused to
draw a conclusion from it. `DenseRows` removes the confound: the same pivot rule, the same
first-row-to-reach-it choice, the same unit-pivot normalization, one inverse per pivot and not one
per eliminated entry, the same statistics. `benches/sparse_linear_algebra.rs` keeps the old group
for continuity and adds `matched_echelon`, which is the comparison that can be read.

Conversion is reported apart from the algorithm throughout, because densifying a matrix is real
cost but it is not elimination. `f4_stages/conversion` and `matched_echelon/*/conversion` time it
on its own.

One asymmetry cannot be removed, so it is stated instead: **the entry budget does not bound a dense
backend's memory.** Every backend counts a nonzero the same way — a field element that is not
zero — so `peak_nonzeros` and `max_live_nonzeros` mean the same thing under all three, and the
budget is tested after every row operation under all three, with `Dense` additionally refusing
before it densifies anything. But `DenseRows` allocates `num_rows * num_columns` cells whatever the
budget says: katsura-7 grevlex's largest matrix is 6810 x 6862, which is 374 MB of field elements
to hold 112 200 entries. The budget bounds entries, not bytes, and a dense representation's bytes
are a property of the shape alone.

#### 7.4.2 Nothing in an F4 matrix is dense — not globally, not per row, not per block

From `cargo run --release --example elimination_density`. Row density is a row's nonzeros over the
matrix width; the percentiles are over every row of every matrix of the instance.

| instance | matrices | largest rows x cols | global density | row density p50 | p90 | p99 | max |
|---|---|---|---|---|---|---|---|
| cyclic-4 lex | 12 | 28 x 28 | 18.70% | 19.05% | 30.00% | 57.14% | 57.14% |
| cyclic-5 grevlex | 22 | 624 x 463 | 3.84% | 2.94% | 9.54% | 24.58% | 57.81% |
| katsura-5 lex | 29 | 381 x 249 | 9.45% | 9.81% | 16.48% | 29.41% | 32.31% |
| katsura-5 grevlex | 6 | 278 x 291 | 4.99% | 4.35% | 17.18% | 25.49% | 28.57% |
| katsura-6 lex | 59 | 1954 x 945 | 4.65% | 4.66% | 7.80% | 15.00% | 32.12% |
| katsura-6 grlex | 9 | 644 x 674 | 4.75% | 4.47% | 11.65% | 18.71% | 25.00% |
| katsura-6 grevlex | 8 | 1388 x 1410 | 1.28% | 0.65% | 5.05% | 20.13% | 25.00% |
| katsura-7 grevlex | 10 | 6810 x 6862 | 0.41% | 0.13% | 1.40% | 14.41% | 22.22% |

Density *as built* is not the whole question, though: elimination is what fills a matrix in, and
M15's 13.58x is a fill-in ratio. The quantity a per-row representation switch would actually have
to predict is **each row's own peak nonzero count during its reduction**, which no counter in
`EliminationStatistics` reports — `peak_nonzeros` is a total over the whole matrix, and a matrix
total cannot distinguish a thousand rows that doubled from one row that became full. The example
instruments the elimination to record it, on each instance's largest matrix.

| instance | rows x cols | built | peak | final | row peak density p50 | p90 | p99 | max | rows over 50% |
|---|---|---|---|---|---|---|---|---|---|
| cyclic-4 lex | 28 x 28 | 108 | 120 | 105 | 14.29% | 21.43% | 35.71% | 35.71% | 0 of 28 |
| cyclic-5 grevlex | 624 x 463 | 7 505 | 16 603 | 16 457 | 10.58% | 24.19% | 28.29% | 28.73% | 0 of 624 |
| katsura-5 lex | 381 x 249 | 6 069 | 9 285 | 9 190 | 12.85% | 28.92% | 42.57% | 42.97% | 0 of 381 |
| katsura-5 grevlex | 278 x 291 | 2 637 | 7 818 | 7 795 | 4.47% | 27.49% | 32.99% | 36.08% | 0 of 278 |
| katsura-6 lex | 1954 x 945 | 64 756 | 96 126 | 95 735 | 9.10% | 21.48% | 35.98% | 45.61% | 0 of 1954 |
| katsura-6 grlex | 644 x 674 | 15 074 | 17 002 | 16 968 | 3.86% | 7.42% | 17.66% | 22.26% | 0 of 644 |
| katsura-6 grevlex | 1388 x 1410 | 16 770 | 103 314 | 103 204 | 0.50% | 25.96% | 35.18% | 36.45% | 0 of 1388 |
| katsura-7 grevlex | 6810 x 6862 | 112 200 | 704 771 | 704 608 | 0.10% | 1.63% | 23.05% | 29.89% | 0 of 6810 |

And the quantity a *block* policy would read, on the same matrices, over 64 x 64 blocks:

| instance | blocks | densest | p99 | p90 | median | over 10% | over 50% |
|---|---|---|---|---|---|---|---|
| cyclic-5 grevlex | 80 | 13.53% | 9.23% | 7.69% | 1.20% | 1 | 0 |
| katsura-5 lex | 24 | 28.18% | 28.18% | 15.19% | 4.39% | 4 | 0 |
| katsura-5 grevlex | 25 | 19.74% | 19.74% | 8.52% | 1.35% | 1 | 0 |
| katsura-6 lex | 465 | 46.62% | 26.76% | 11.48% | 0.39% | 63 | 0 |
| katsura-6 grlex | 121 | 30.15% | 25.14% | 11.89% | 0.00% | 21 | 0 |
| katsura-6 grevlex | 506 | 19.90% | 9.89% | 2.39% | 0.00% | 5 | 0 |
| katsura-7 grevlex | 11 556 | 24.73% | 5.81% | 0.29% | 0.00% | 39 | 0 |

**Three readings, and all three matter.**

*The fill-in is real, and it is not densification.* katsura-6 grevlex goes from 16 770 live entries
to 103 314 — 6.2x — and katsura-7 grevlex from 112 200 to 704 771, 6.3x. These matrices really do
get much fuller. They also stay below 37% in the densest row of either and below 25% in the densest
64 x 64 block. M15's 13.58x is a ratio of entry counts, and §5.4's warning that it is not evidence
of density is confirmed: it is evidence of growth from a very low base.

*Global density is the wrong quantity, exactly as §5.4 predicted.* katsura-7 grevlex is 0.41% dense
as a matrix and holds rows at 22% as built and 30% at peak — a factor of 70 between the two
numbers. A policy reading the matrix would read 0.41% and conclude "very sparse" about a matrix
whose worst rows are seventy times that.

*But the right quantity does not supply a threshold either.* Over 155 matrices, and over all
12 107 rows of the eight instrumented ones, **not one row ever exceeds 50% occupancy at its own
peak and not one of the 12 777 64 x 64 blocks exceeds 50%.** The maxima are 45.61% (a row of
katsura-6 lex) and 46.62% (a block of katsura-6 lex); only that instance reaches 40% in either.
A density-keyed policy, on whichever density it read, would never fire — and a threshold set low
enough to fire would fire on matrices where `Dense` loses, which §7.4.3 shows is all of them.

**Density-keyed per-row switching, density-aware pivoting, and dense treatment of selected blocks
are therefore rejected on this measurement, before being implemented.** The two numbers that reject
them are "0 of 12 107 rows over 50%" and "0 of 12 777 blocks over 50%". Two rows *as built* do
exceed 50% — a 16-of-28 row of cyclic-4 lex and one row of a small early cyclic-5 grevlex matrix —
and both are on matrices where `Dense` is slower anyway.

#### 7.4.3 Sparse against dense, matched contract, conversion separated

Same run. Every matrix of an instance eliminated once, summed over the instance. `dense (alg)` is
the dense backend's time with its conversions subtracted out; `conv` is densify-plus-sparsify
measured on its own. Milliseconds.

| instance | sparse | dense (alg) | conv | dense (total) | dense/sparse | adaptive | sparse/adaptive |
|---|---|---|---|---|---|---|---|
| cyclic-4 lex | 0.05 | 0.06 | 0.01 | 0.07 | 1.25x | 0.05 | 1.07x |
| katsura-5 grevlex | 0.73 | 0.80 | 0.10 | 0.90 | 1.25x | 0.55 | 1.33x |
| katsura-5 lex | 6.64 | 7.79 | 0.58 | 8.37 | 1.26x | 5.14 | 1.29x |
| katsura-6 grlex | 14.76 | 22.39 | 1.42 | 23.81 | 1.61x | 8.82 | 1.67x |
| cyclic-5 grevlex | 15.80 | 26.55 | 1.25 | 27.80 | 1.76x | 10.67 | 1.48x |
| katsura-6 grevlex | 20.00 | 44.06 | 2.40 | 46.46 | 2.32x | 12.25 | 1.63x |
| katsura-6 lex | 384.85 | 580.99 | 16.77 | 597.76 | 1.55x | 230.41 | 1.67x |
| katsura-7 grevlex | 745.87 | 1299.62 | 486.13 | 1785.75 | 2.39x | 363.15 | **2.05x** |

**There is no crossover.** `Dense` is slower than `Sparse` on every instance — 1.25x to 2.39x on
total time — and it is *still* slower on every instance when conversion is subtracted out
entirely: 1.10x to 2.20x on algorithm alone. Removing the conversion does not change the
conclusion, which is the point of separating it. The dense representation loses on the algorithm,
not on the plumbing.

And the ratio **rises** with size rather than falling toward a crossover: 1.20x on a 28 x 28
matrix, 1.52x at 644 x 674, 2.20x at 1388 x 1410, 1.74x at 6810 x 6862 (algorithm only). The reason
is structural: a dense row operation costs the matrix's whole width whatever the pivot's support
is, and the pivots' support is 0.1% to 20% of the width. Widening the matrix makes that worse, not
better. A crossover would require rows at a large fraction of the width, and §7.4.2 says there are
none.

Conversion is 3% to 14% of the dense total on seven of the eight instances, and **27%** on
katsura-7 grevlex, where zeroing a 46.7-million-cell buffer to hold 112 200 entries is a quarter of
what the backend does. That is the measurement the separation was for: it is large, it is real, and
it is not what decides the comparison.

This closes M15's open question: **no sparse/dense crossover exists in the range F4 produces.**
`Backend::Dense` stays because it is the control the other two are measured against, and because "a
dense backend that loses everywhere" is exactly the deliverable §5.4 asked for.

#### 7.4.4 What does pay: a dense accumulator over sparse pivots

The sparse inner operation is a sorted merge of two rows into a scratch buffer. It allocates
nothing per operation, but it reads and rewrites *every* entry of the row being reduced however few
entries the pivot has, and swaps the result back. With pivot supports at 0.1% to 20% of the width
and rows that grow sixfold during their own reduction, that is the wrong cost in the one place it
is paid most often.

`DenseAccumulator` scatters the row into a dense buffer once, applies every pivot in time
proportional to the *pivot's* support, and gathers the row back once. The matrix stays sparse, so
the cost is one buffer of `num_columns` cells for the whole elimination rather than
`num_rows * num_columns` — 55 KB on katsura-7 grevlex against 374 MB. This is the "dense temporary
row accumulator" of §5.4, and it is the strategy that pays: 1.29x to 2.05x on every instance above
a millisecond, best on the largest.

Two details that are part of the measurement rather than extra:

- **Buffer reuse.** The accumulator is allocated once per elimination, and the gather clears only
  the span it touched, so a row operation allocates nothing and a row costs one clear of its own
  span rather than of the width. The remaining per-elimination allocation is the buffer, one row
  wide.
- **No zero test in the inner loop.** A field has no zero divisors and a sparse row stores no zero
  coefficient, so `factor * coefficient` is never zero and the test for it is dead. Removing it is
  3.4% on katsura-6 grevlex, 7.6% on katsura-6 grlex and 10.2% on katsura-5 lex, as a Criterion
  A/B against the version that kept the test (`p < 0.05` on all three).

It is **not** keyed on a density, and §7.4.2 is why: there is no threshold to key on. "Adaptive"
names a choice of representation per *role* — pivot or work — not per matrix and not per measured
density. That the policy is unconditional is also what makes determinism free: there is no observed
quantity for a choice to depend on.

#### 7.4.5 Effect on the elimination stage, per system and order

From `cargo run --release --example f4_profile -- baseline | d | d-dense`, one session so the three
columns are comparable to each other. Milliseconds.

| system | order | elim sparse | elim adaptive | speedup | elim dense | total sparse | total adaptive |
|---|---|---|---|---|---|---|---|
| cyclic-4 | lex | 0.10 | 0.05 | 2.00x | 0.10 | 0.41 | 0.25 |
| cyclic-4 | grlex | 0.04 | 0.04 | 1.00x | 0.07 | 0.18 | 0.18 |
| cyclic-4 | grevlex | 0.05 | 0.04 | 1.25x | 0.06 | 0.19 | 0.19 |
| cyclic-5 | lex | 14.41 | 8.71 | 1.65x | 23.52 | 29.06 | 23.20 |
| cyclic-5 | grlex | 14.72 | 7.90 | 1.86x | 18.39 | 21.88 | 14.40 |
| cyclic-5 | grevlex | 17.45 | 9.68 | 1.80x | 25.79 | 23.77 | 15.37 |
| katsura-4 | lex | 0.23 | 0.17 | 1.35x | 0.26 | 0.64 | 0.51 |
| katsura-4 | grlex | 0.08 | 0.07 | 1.14x | 0.09 | 0.28 | 0.24 |
| katsura-4 | grevlex | 0.06 | 0.04 | 1.50x | 0.06 | 0.20 | 0.17 |
| katsura-5 | lex | 6.59 | 4.28 | 1.54x | 8.03 | 15.25 | 11.79 |
| katsura-5 | grlex | 0.75 | 0.48 | 1.56x | 0.85 | 1.95 | 1.63 |
| katsura-5 | grevlex | 0.74 | 0.51 | 1.45x | 0.95 | 1.88 | 1.58 |
| katsura-6 | lex | 380.09 | 222.25 | **1.71x** | 673.28 | 3075.79 | 2898.44 |
| katsura-6 | grlex | 13.49 | 8.63 | **1.56x** | 20.63 | 22.50 | 18.36 |
| katsura-6 | grevlex | 19.28 | 12.11 | **1.59x** | 43.33 | 29.02 | 22.14 |
| katsura-7 | grlex | 434.37 | 240.08 | **1.81x** | 787.42 | 536.15 | 340.96 |
| katsura-7 | grevlex | 767.45 | 369.33 | **2.08x** | 1822.17 | 883.47 | 482.71 |
| random-4 | lex | 4.27 | 3.09 | 1.38x | 5.22 | 8.93 | 7.42 |
| random-4 | grlex | 0.31 | 0.21 | 1.48x | 0.30 | 0.85 | 0.71 |
| random-4 | grevlex | 0.39 | 0.29 | 1.34x | 0.38 | 0.99 | 0.88 |

**No instance regresses, under any order, in the elimination stage or in the total.** The whole
computation improves by 1.57x on katsura-7 grlex (536.2 to 341.0 ms) and **1.83x on katsura-7
grevlex** (883.5 to 482.7), which is what §6.2 predicted would happen if elimination got faster:
those two instances are 81% and 87% elimination.

The sub-millisecond rows are reported for completeness and should not be read as ratios: cyclic-4
and katsura-4 measure tens of microseconds per stage, where the clock reads and the first batch's
warm-up are a visible share. Every ratio this workstream claims is from an instance above a
millisecond.

katsura-6 lex barely moves — 3075.8 to 2898.4 — for the reason §6.2 found. Its elimination falls
by 42%, but 84% of that instance is `reduce_grobner_basis` (2579.2 ms of 3075.8), which belongs to
M16-C. That is not a failure of this workstream; it is the stage breakdown doing its job.

#### 7.4.6 Criterion, on the matrices F4 builds

From `cargo bench --bench f4_stages -- 'f4_stages/(elimination|conversion)'`, Criterion medians at
sample size 10, every batch of the instance replayed per iteration. An instrument independent of
the example's own timing loop, run twice.

| instance | run | sparse | dense | adaptive | conversion | dense/sparse | sparse/adaptive |
|---|---|---|---|---|---|---|---|
| katsura-6 grevlex | A | 20.83 | 31.29 | 12.04 | 2.26 | 1.50x | 1.73x |
| katsura-6 grevlex | B | 20.29 | 31.59 | 11.99 | 2.31 | 1.56x | 1.69x |
| katsura-6 grlex | A | 15.07 | 19.36 | 8.52 | 1.03 | 1.29x | 1.77x |
| katsura-6 grlex | B | 14.71 | 18.67 | 8.52 | 1.02 | 1.27x | 1.73x |
| katsura-5 lex | A | 6.60 | 8.55 | 4.86 | 0.59 | 1.30x | 1.36x |
| katsura-5 lex | B | 6.65 | 8.48 | 4.89 | 0.65 | 1.28x | 1.36x |
| cyclic-5 grevlex | A | 16.97 | 24.72 | 10.68 | 0.94 | 1.46x | 1.59x |
| cyclic-5 grevlex | B | 16.83 | 24.16 | 10.07 | 0.90 | 1.44x | 1.67x |

Two independent runs of the same code, taken under the same contention. Every median is within 3%
of its pair and every ratio within 5%, so the ordering — `Adaptive` fastest, `Sparse` next, `Dense`
slowest, on all four instances — is not an artifact of one run. The `dense` column here *includes*
its conversions, which the `conversion` column measures separately: subtracting it leaves `Dense`
ahead of `Sparse` on none of the four.

The ratios are smaller than §7.4.3's because Criterion's `iter_batched` clones the matrices per
iteration while the example's loop clones inside its own untimed section; the direction and the
ordering agree, which is what a second instrument is for.

#### 7.4.7 What was rejected, and the number that rejected it

| strategy | verdict | the measurement |
|---|---|---|
| Dense rows throughout | **rejected as a default, kept as the control** | slower than sparse on all 8 instances: 1.25x to 2.39x total, 1.10x to 2.20x with conversion removed; the ratio rises with size |
| Per-row sparse/dense switching keyed on density | **rejected before implementation** | 0 of 12 107 instrumented rows exceeds 50% peak occupancy; the maximum anywhere is 45.61% |
| Dense treatment of selected blocks | **rejected before implementation** | 0 of 12 777 64 x 64 blocks exceeds 50%; the densest anywhere is 46.62% |
| Density-aware pivot strategies | **rejected before implementation** | the same two distributions, and over a finite field there is no stability to pivot for, so this would trade determinism for a threshold that never fires |
| Any policy keyed on *global* density | **rejected as keyed on the wrong quantity** | katsura-7 grevlex is 0.41% dense and holds rows at 29.89% peak occupancy — a factor of 70 |
| Dense temporary row accumulator | **accepted** | 1.29x to 2.05x over sparse on real matrices, best on the largest; no regression on any instance or order |
| Buffer reuse | **accepted, inside the above** | one buffer per elimination, cleared over the touched span only; a row operation allocates nothing |

#### 7.4.8 Correctness

- Every backend produces the identical matrix and the identical `EliminationStatistics` on
  rectangular, square, singular, rank-one, sparse, dense, fill-in-heavy and degenerate shapes, over
  GF(7), GF(13), GF(541), GF(2^31 - 1) and GF(2^64 - 59)
  (`test_every_backend_agrees_on_every_shape_and_field`).
- Rank agrees with `Matrix::rank`, which is independently checked against Sage. The row space is
  certified per backend by an augmented identity block carrying the combination of original rows
  that produced each reduced row (`test_every_backend_preserves_the_row_space`).
- `reduce_rows_against_pivots_with` honours its contract under every backend at `split = 0`,
  `split = num_rows / 2` and `split = num_rows`, over all five fields: upper rows untouched, lower
  rows reduced and normalized, result equal to a full echelon of the same arrangement
  (`test_every_backend_honours_the_split_contract`). Its preconditions are now validated once in
  the interface instead of once per backend, so there is a single copy of them to keep right, and
  every backend rejects a malformed upper block
  (`test_every_backend_rejects_a_malformed_upper_block`).
- Each backend is deterministic over eight repetitions, and `Adaptive` agrees with both fixed
  backends (`test_every_backend_is_deterministic`).
- The budget refuses work mid-elimination under every backend, reporting a count above the budget,
  and a budget set at the peak behaves exactly as an unbounded run
  (`test_the_budget_is_enforced_mid_elimination`).
- `f4` returns the identical basis under every backend over the whole correctness corpus and all
  three orders, and on katsura-5 and cyclic-4 over all three
  (`test_elimination_backend_does_not_change_the_basis`,
  `test_every_backend_agrees_on_the_benchmark_systems`).
- Every backend reports the identical statistics on the Macaulay matrices of real katsura-5 runs,
  all three orders (`test_every_backend_reports_the_same_elimination_statistics`), which is what
  makes `max_live_nonzeros` mean one thing rather than three.

Both frozen signatures are unchanged and `reduce_rows_against_pivots_with`'s documented contract is
unchanged, so **no interface change is requested**. No file outside `src/linalg/**` was modified
except by appending to `src/grobner/f4/tests.rs`, `benches/**`, `examples/**`, `README.md` and this
section. `F4Options::default()` still names the baseline: making `Adaptive` the default is M16-I's
decision, and the number it needs is in §7.4.5.

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
