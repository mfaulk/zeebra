# Milestone: Quotient-Algebra and FGLM Scalability

**Status:** in progress — M18-0 complete
**Prerequisite:** M17, merged at `7c2fef7`
**Objective:** make quotient-algebra construction faster and FGLM's memory smaller, without
changing a single answer
**Reference implementation:** M17 classical FGLM
**External oracle:** Singular 4.4.1, build 44105

M17 built the pipeline and measured it. The measurement is what this milestone starts from: on
katsura-7, constructing the multiplication operators is **36.2 ms of a 38.1 ms conversion**. The
remaining 1.9 ms is everything else FGLM does. So the cost is not in the linear algebra the
algorithm is named for; it is in computing `N * D` normal forms one at a time.

Separately, the classical algorithm's dependence test is quadratic in the quotient dimension, which
is what stops it from reaching systems whose quotient is large even when their lex basis is cheap.
Those are two different problems and this milestone attacks them separately: optimize the existing
pipeline first, then investigate whether its scaling limit can be surpassed at all.

---

## 1. Sub-milestones

| | deliverable | state |
|---|---|---|
| M18-0 | profiling baseline, and differential testing against Singular | **complete** |
| M18-1 | border indexing, and deduplicated normal forms | not started |
| M18-2 | batched border reduction | not started |
| M18-3 | adaptive sparse/dense multiplication operators | not started |
| M18-4 | incremental-span memory, and a sparse-FGLM feasibility spike | not started |
| M18-5 | integration, ablations, and this document's conclusion | not started |

M18-3 and M18-4 are independent of M18-1 and M18-2 and of each other. All four depend on M18-0,
because none of them may be merged without evidence that it changed no answer.

---

## 2. M18-0: what was built

Two things, neither of which is an optimization.

### 2.1 Stage attribution

M17's `FglmStatistics` had one counter for the operators — `operator_entries` — and no timings at
all. It could say operator construction dominates; it could not say what inside it to attack,
because the monomial lookup, the reduction, and the coordinate-vector assembly were one undivided
block of wall clock.

`FglmStatistics` now carries three structures:

* **`BorderStatistics`** — `N * D` operator columns split into those whose product stays standard
  and those that leave the staircase, and the latter split again into *distinct* monomials and
  repeats. Collected unconditionally: one hash-set insert per nonstandard column is nothing against
  a normal form.
* **`FglmStageTimings`** — five stages that partition the conversion: standard-monomial
  enumeration, border classification, normal forms, coordinate assembly, and the lex walk. Behind
  `FglmOptions::measure_stages`, for the same reason F4's timings are behind
  `F4Options::measure_stages`: the operator loop runs `N * D` times and a clock read inside it is
  not free.
* **`FglmMemory`** — entries, cells, and bytes kept distinct, because they are different numbers.

`cargo run --release --example fglm_profile` reports all of it.

### 2.2 Differential testing against Singular

M17 checked the conversion against 29 Singular lex bases, committed as literals. That established
the conventions and left two gaps: the oracle could not be pointed at a thousand random systems,
and it compared only the *final* basis — so a wrong multiplication-operator column was findable
only if it happened to change the answer.

`cargo run --release --bin zeebra-differential` closes both. See §4.

---

## 3. Baseline

### 3.1 Methodology

AMD Ryzen Threadripper PRO 5995WX, 128 threads, 503 GB. `rustc 1.97.0`, release profile, no
competing build or benchmark. GF(2^31 - 1) throughout, grevlex source, lex target. Each timing is
the fastest of three runs in one process: interference can only make a run slower.

Everything in this section was measured in a single session **after** the M18-0 instrumentation
landed, so the numbers are a baseline for M18-1 onwards rather than M17's numbers quoted back.
Where they differ from M17's report they differ by under 10%, which is run-to-run variance on this
machine and not a change in the code.

### 3.2 The pipeline, unchanged

`cargo run --release --example fglm_conversion`

| system | `D` | grevlex F4 | quotient algebra | conversion | pipeline | direct lex F4 |
|---|---:|---:|---:|---:|---:|---:|
| cyclic-3 | 6 | 0.01 | 0.01 | 0.01 | 0.02 | 0.01 |
| katsura-3 | 4 | 0.02 | 0.01 | 0.01 | 0.03 | 0.02 |
| katsura-4 | 8 | 0.09 | 0.05 | 0.06 | 0.16 | 0.10 |
| katsura-5 | 16 | 0.54 | 0.40 | 0.44 | 0.98 | 0.75 |
| katsura-6 | 32 | 3.22 | 3.02 | 3.21 | 6.43 | 16.20 |
| katsura-7 | 64 | 29.49 | 32.85 | 33.34 | 62.83 | no basis |
| cyclic-5 | 70 | 1.49 | 1.91 | 2.15 | 3.64 | 2.64 |
| cyclic-6 | 156 | 12.72 | 23.54 | 28.14 | 40.85 | 283.51 |
| planted-4 | 16 | 0.02 | 0.03 | 0.05 | 0.07 | 0.02 |
| planted-6 | 64 | 0.03 | 0.25 | 0.37 | 0.40 | 0.03 |
| planted-8 | 256 | 0.04 | 1.59 | 2.80 | 2.84 | 0.04 |

Milliseconds. `quotient algebra` is a part of `conversion`, not an addition to it. `no basis` means
direct lex F4 crossed a limit in `F4Options::default()`.

### 3.3 The border

`cargo run --release --example fglm_profile`

| system | `N` | `D` | `N*D` | standard | border | `|∂B|` | repeated | dup % |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| katsura-5 | 5 | 16 | 80 | 22 | 58 | 44 | 14 | 24.1 |
| katsura-6 | 6 | 32 | 192 | 54 | 138 | 100 | 38 | 27.5 |
| katsura-7 | 7 | 64 | 448 | 125 | 323 | 223 | 100 | 31.0 |
| cyclic-5 | 5 | 70 | 350 | 148 | 202 | 157 | 45 | 22.3 |
| cyclic-6 | 6 | 156 | 936 | 372 | 564 | 386 | 178 | 31.6 |
| planted-6 | 6 | 64 | 384 | 144 | 240 | 192 | 48 | 20.0 |
| planted-8 | 8 | 256 | 2048 | 768 | 1280 | 1024 | 256 | 20.0 |
| planted-10 | 10 | 1024 | 10240 | 3840 | 6400 | 5120 | 1280 | 20.0 |

Three things are worth saying about this table, and a fourth about what it does **not** say.

**The duplication is real and it is modest.** Between a fifth and a third of border columns reduce
a monomial some other column already reduced. Katsura-7 is the highest at 31%, which is convenient
— it is also the instance the milestone targets.

**The planted family is exactly 20% on every size.** That is structure, not coincidence: a planted
system's staircase is a product of intervals, and the arithmetic of its border is the same at every
`n`. It means the planted family will not distinguish a good deduplication from a mediocre one.

**A quarter to three-eighths of all columns need no reduction at all.** That is the property the
sparse column representation was chosen for in M17, measured here per family rather than assumed.

**And the thing this table does not say:** `dup %` is an upper bound on the *reductions*
deduplication removes. It is not an upper bound on the *time*, because border monomials do not cost
the same to reduce. A repeated monomial is one that two different `x_i b_j` products land on, which
correlates with being low in the order, which correlates with being cheap. So 31% of the reductions
could easily be well under 31% of the time. M18-1 must measure this, not infer it.

### 3.4 Where the time goes

| system | total | enumerate `B` | classify | normal forms | assemble | lex walk | nf share |
|---|---:|---:|---:|---:|---:|---:|---:|
| katsura-5 | 0.53 | 0.01 | 0.01 | 0.43 | 0.02 | 0.05 | 81% |
| katsura-6 | 3.68 | 0.03 | 0.02 | 3.31 | 0.13 | 0.18 | 90% |
| katsura-7 | 35.75 | 0.09 | 0.05 | 34.06 | 0.61 | 0.92 | **95%** |
| cyclic-5 | 1.93 | 0.03 | 0.03 | 1.59 | 0.06 | 0.21 | 82% |
| cyclic-6 | 25.44 | 0.10 | 0.08 | 23.21 | 0.54 | 1.49 | 91% |
| planted-6 | 0.39 | 0.03 | 0.03 | 0.18 | 0.02 | 0.12 | 47% |
| planted-8 | 3.35 | 0.13 | 0.18 | 1.29 | 0.13 | 1.53 | 38% |
| planted-10 | 39.22 | 0.71 | 1.06 | 9.32 | 0.71 | 25.74 | **24%** |

Milliseconds, and `nf share` is normal forms over total.

This is the table that sets M18's agenda, and it says the two problems have **different owners**:

* On katsura and cyclic, reduction is 81–95% of the conversion. Classification is under 0.3% and
  assembly under 2%. §5.3 of the proposal asks whether the one-term `MultivariatePolynomial`
  allocated per border monomial is material; on this evidence its cost lies in `assemble` and
  `classify`, which together are 0.66 ms of katsura-7's 35.75 ms. **Deduplicating and batching the
  reductions is the only lever on this family that can matter.**
* On planted-10 the lex walk is 66% and reduction is 24%. Nothing M18-1 or M18-2 does will help
  there. What is large on planted-10 is the **24.6 MB of dense blocks** against 0.6 MB of operators
  — which is M18-4's problem, not M18-2's.

So the milestone's two halves are not two attacks on one bottleneck. They are attacks on two
bottlenecks that happen to belong to different families of input.

### 3.5 Storage

| system | `D` | operator entries | operator kB | dense blocks kB | blocks / operators |
|---|---:|---:|---:|---:|---:|
| katsura-5 | 16 | 751 | 13.6 | 6.0 | 0.4x |
| katsura-6 | 32 | 3,558 | 60.1 | 24.0 | 0.4x |
| katsura-7 | 64 | 16,257 | 264.5 | 96.0 | 0.4x |
| cyclic-5 | 70 | 2,060 | 40.5 | 114.8 | 2.8x |
| cyclic-6 | 156 | 12,850 | 222.7 | 570.4 | 2.6x |
| planted-6 | 64 | 336 | 24.0 | 96.0 | 4.0x |
| planted-8 | 256 | 1,792 | 128.0 | 1,536.0 | 12.0x |
| planted-10 | 1,024 | 8,960 | 640.0 | 24,576.0 | **38.4x** |

`operator kB` is what the columns hold including each `Vec`'s spare capacity and the one-`Column`
per-column spine; `dense blocks kB` is the three dense `D x D` blocks the conversion needs at full
rank. Both are estimates of this crate's representations. The process's own peak, measured
separately through `util::peak_resident_bytes`, was 27 MB for a run covering every system above
plus the F4 computations that produced their inputs — which is a ceiling on all of it, not an
attribution to any one conversion.

**`operator_bytes` is not `entries * 16`, and on the planted family it is not close.** Broken down
(`size_of::<Column<F>>()` is 24, `size_of::<(usize, F)>()` is 16):

| system | total bytes | entries | column spine | spare `Vec` capacity |
|---|---:|---:|---:|---:|
| katsura-7 | 270,864 | 260,112 — 96% | 10,752 — 4% | 0 — 0% |
| planted-10 | 655,360 | 143,360 — 22% | 245,760 — 37% | 266,240 — **41%** |

The spare capacity is not an accounting artefact. `Vec`'s minimum non-zero allocation is four
elements for this element size, and a planted system's typical reduced column holds **one** — 8,960
entries across 6,400 border columns. So four sixteen-byte slots are allocated where one is used.

Two consequences for M18-3. First, choosing between a sparse and a dense representation from entry
*counts* would be choosing from the 22% column and ignoring the other 78%. Second, the obvious
dense alternative is not obviously worse here: a dense column of `D = 1024` elements is 8 kB
against the 64 bytes a one-entry sparse column actually costs, so on this family sparse wins
decisively even at four times the slots it needs — but the comparison has to be made against the
real figure, not against `entries * 16`.

**There are three dense blocks, and M17's accounting counted two.** The span holds a coordinate
vector and a combination vector per echelon row; the conversion *additionally* retains every
accepted quotient vector, so that a candidate's class costs one operator application instead of a
reduction. That third `D x D` block was in no budget. `FglmMemory::accepted_vector_cells` reports
it now.

`max_span_entries` was deliberately **not** redefined to cover it. A budget that counted two blocks
in one release and three in the next would make every recorded measurement ambiguous. Closing the
gap is M18-4's, with a budget of its own.

The ratio column is the scalability story in one number. On katsura the operators dominate and the
dense blocks are a rounding error; on planted-10 the blocks are 38x the operators. Classical FGLM's
limit is not the operators.

---

## 4. The differential harness

`src/grobner/differential/`, driven by `cargo run --release --bin zeebra-differential`.

### 4.1 What is compared

The checks run outwards from the source basis and the first failure stops the comparison. That
order is not cosmetic: a wrong quotient dimension explains every later disagreement, so reporting
it alone is more useful than reporting all of them.

| check | Zeebra | Singular |
|---|---|---|
| source basis | `f4` under grevlex | `std` in a `dp` ring |
| quotient dimension | `QuotientBasis` | `vdim` |
| standard monomials | `QuotientBasis::monomials` | `kbase` |
| border coverage | `∂B` as Zeebra computes it | the monomials the oracle was asked about |
| border normal forms | `normal_form(u)` for each `u` in `∂B` | `reduce(u, G)` |
| operator columns | each column of each `T_i` | the normal form of the monomial it stands for |
| lex basis | `fglm_to_lex` | `std` in an `lp` ring |

**Operator columns are compared one at a time.** This is the point of the whole exercise.
`T_i(b_j) = NF_G(x_i b_j)` has a precise answer for every `(i, j)`, so a wrong column is a finding
in itself rather than something to be deduced from a wrong lex basis. The expected column is
reconstructed from two things the oracle has already been checked on — the standard monomials, and
the normal form of each border monomial — so a column is a unit vector where the product stayed
standard and the oracle's own normal form where it did not.

The border-coverage check exists because the comparison would otherwise have a hole: the oracle is
told which monomials to reduce, and that list comes from *Zeebra's* standard monomials. A fixture
that omitted a border monomial would pass by not being asked about it. So the set Zeebra has and
the set the oracle answered about are required to be equal.

### 4.2 Conventions

Each was verified before being relied on, not assumed:

* `dp` is degree-reverse-lex and matches `GradedReverseLexicographic`; `lp` with variables declared
  `(x1,x2,...)` orders `x1 > x2 > ...` and matches `Lexicographic` with
  `parse(s, ["x1","x2",...])`.
* `short = 0` prints `x1^2` and `2*x1`, which Zeebra's parser accepts; the short forms `x12` and
  `2x1` it does not.
* Coefficients print as the symmetric representative, so `-x2` rather than `6*x2` modulo 7.
* `option(redSB)` is set. `fglm` requires a *reduced* standard basis for its source and `std` does
  not produce one unless asked; it also makes `std`'s output the unique reduced basis, which is
  what lets every comparison be an equality of values rather than a containment test.
* `int` is ring-independent in Singular, so a flag set before `setring` is readable after it. This
  is what lets the lex half of the script know whether the ideal was zero-dimensional.
* Each list element is printed on its own marked line. Printing a whole ideal at once would need
  splitting on a separator, and `printf("%s", ideal)` prints `0` for the *empty* ideal — so a
  reported size is also checked against the number of lines, which makes emptiness unambiguous.
* Singular's prime characteristic must be below `2^31`, so GF(2^31 - 1) is the largest field the
  oracle reaches. §9.1 of `MILESTONE-FGLM-SOLVING.md` sets out why evidence at these primes bears
  on the larger ones; the generator helps that argument by drawing its exponents from a
  characteristic-independent stream, so the same seed gives the *same monomials* over GF(13) and
  over GF(2^31 - 1).

### 4.3 An oracle that did not answer is not agreement

**Singular exits 0 after a script error.** It prints `   ? ...` and carries on, so the exit status
proves nothing. Every run is therefore required to reach an end-of-script marker *and* to have
printed no error line.

Beyond that, each of the following is an `OracleError` and is counted against the sweep rather than
as a pass:

* the binary cannot be started;
* the run exceeded its time limit and was killed — the wait is a poll on a child whose output goes
  to a file, not a read on a pipe, because a child whose pipe fills while the parent is not reading
  blocks forever, which is precisely the case a timeout exists for;
* an expected marker is missing, or a list's length disagrees with the size Singular reported;
* the characteristic is outside Singular's range;
* **Singular contradicts itself** — its `std` under `lp` and its own `fglm` disagree. That is a
  third algorithm cross-checking the second, and a disagreement makes the run unusable rather than
  making Zeebra wrong.

`SweepReport::clean` is false if any of these happened, and the binary exits non-zero.

### 4.4 Results

500 systems, seed 12345, two to five variables, degree at most 3, at most 4 terms per generator,
cycling through GF(2), GF(3), GF(7), GF(13), GF(65537) and GF(2^31 - 1). 34.5 seconds.

| outcome | systems |
|---|---:|
| agreed, zero-dimensional | 195 |
| agreed, unit ideal | 193 |
| agreed, positive-dimensional and rejected by both | 112 |
| disagreed | 0 |
| oracle did not answer | 0 |

The three classes matter. A harness that only ever saw zero-dimensional ideals would not check that
Zeebra rejects a positive-dimensional one for the same reason Singular does, and the unit ideal is
the degenerate case where the quotient is the zero space and the lex basis is `{1}`.

### 4.5 The harness has teeth

A sweep of agreements is evidence only if a disagreement would have been caught. Two
demonstrations:

**An injected fault.** `coordinates_of_normal_form` was changed to drop its last coordinate. The
sweep found it on the fifth system and reported

```text
FAIL [   4] seed-1004-p3-n2  DISAGREED operator-column: column 1 of T_0 stands for x1*x2:
                             Zeebra says 2*x2+2 and the oracle says 2*x2^2+2*x2+2
```

then shrank the two-generator system `1+x1*x2+2*x1^2*x2+x2^2, 2+2*x1^2` to
`x1*x2+x1^2*x2+x2^2, 1+2*x1^2` in three accepted shrinks of twenty candidates tried. The fault was
reverted. Note what the report names: not "the lex basis is wrong", but which column of which
operator, and which monomial it stands for.

**A corrupted fixture.** `test_a_corrupted_fixture_is_detected` perturbs a committed case six ways
— the dimension, the source basis, a standard monomial, the border coverage, a border normal form,
and the lex basis — and requires each to be caught by the check named after it. A seventh asserts
that a case with *no* recorded lex basis for a zero-dimensional ideal is a gap rather than an
agreement.

### 4.6 Minimization

A failing system is shrunk by four reductions, largest first: drop a generator, drop a term, flatten
a coefficient to one, lower an exponent. A candidate is accepted only if it still fails **the same
check** — a candidate that fails a different one is a different bug, and following it would walk the
search away from what the sweep found. The descent is greedy and finds no guaranteed minimum.

It is bounded by an attempt count and a wall clock, because each candidate costs a Singular
invocation and an unbounded search on a large failing system can take longer than the sweep that
found it. **The original system and its seed are always kept beside the shrunk one**, since a shrunk
system is no longer what the seed generates.

### 4.7 CI needs no Singular

A sweep's agreeing cases are emitted as Rust literals into
`src/grobner/differential/fixtures.rs` — the same convention `reference_bases.rs` already uses, for
the same two reasons: the compiler type-checks them, and reading them needs no parser and no new
dependency.

96 cases are committed. An ordinary test replays **the same comparison function** against them,
with a table of constants where the subprocess was, so the checks CI runs cannot drift from the
checks a development machine runs. Three further tests require the table to cover every supported
characteristic, every supported variable count, and all three ideal classes — a table of twenty
large-prime two-variable unit ideals would otherwise pass while checking almost nothing.

The live sweep is additionally an `#[ignore]`d test, so that `cargo test` can exercise the real
oracle path on request without ever depending on it.

### 4.8 What the harness does not reach

* **Characteristics above `2^31`.** Singular's limit, not Zeebra's. Unchanged from M17.
* **Large systems.** The generator makes small random systems, where the interesting thing is
  variety rather than size. The benchmark corpus — katsura, cyclic, planted — is checked by the
  existing tests and by the 29 reference bases, not by the sweep.
* **Monomial orders other than grevlex and lex.** The pipeline's source order and target order are
  what the conversion is about; `quotient_algebra.rs`'s own tests cover graded lex as a source.

---

## 5. Acceptance criteria

### M18-0 — validation infrastructure

- [x] Reproducible M17 baseline captured — §3.2, remeasured after instrumentation.
- [x] Singular differential harness implemented — §4.
- [x] Variable-order and field conventions verified — §4.2.
- [x] Randomized tests over multiple small prime fields — §4.4, six characteristics including 2
      and 3.
- [x] Failing cases can be persisted and reproduced — §4.5, §4.6.
- [x] Representative fixtures committed — §4.7, 96 cases.
- [x] Ordinary CI does not require Singular — §4.7.

### M18-1 — border deduplication

- [ ] Unique border monomials enumerated correctly.
- [ ] Repeated border products deduplicated.
- [ ] Normal forms agree with M17.
- [ ] Operator columns agree exactly.
- [ ] Performance and duplication rate measured.

### M18-2 — batched reduction

- [ ] Symbolic closure invariant tested.
- [ ] Fixed reducer pivots implemented correctly.
- [ ] Independent target normal forms preserved.
- [ ] Batched results equal scalar results.
- [ ] Matrix and resource limits enforced.
- [ ] Batch-size performance measured.
- [ ] Appropriate fallback strategy retained.

### M18-3 — operator storage

- [ ] Standard, sparse, and dense columns supported.
- [ ] Adaptive selection supported where justified.
- [ ] All representations agree exactly.
- [ ] Operator application benchmarked separately.
- [ ] Byte-aware accounting introduced.
- [ ] Resource limits apply across representations.

### M18-4 — FGLM scalability

- [ ] Actual incremental-span storage measured.
- [ ] All substantial coordinate-vector storage accounted for.
- [ ] Compact dependence representation evaluated.
- [ ] Dependence coefficients remain exact.
- [ ] Shape-position detection evaluated.
- [ ] Sparse-FGLM spike documented with go/no-go criteria.
- [ ] No unverified probabilistic result is exposed as certified output.

### M18-5 — integration

- [ ] All default tests pass.
- [ ] Release-mode tests pass.
- [ ] Slow Gröbner and FGLM reference comparisons pass.
- [ ] Expanded Singular fixtures agree.
- [ ] Every optimization has an independent benchmark.
- [ ] Combined performance and memory usage measured.
- [ ] Any regressions documented.
- [ ] Default strategies selected from evidence.
- [ ] README and milestone documentation updated.
- [ ] Next-milestone recommendation based on measured bottlenecks.

---

## 6. Compatibility

`FglmOptions` gained `measure_stages` and `FglmStatistics` gained `border`, `timings` and `memory`.
Both structs have public fields, so a downstream struct literal naming every field stops compiling.
Constructing from `recommended()`, `unbounded()` or `Default` and assigning what matters survives a
new field, which is what this crate's own callers do and what the documentation now says to do.

`FglmStatistics::estimated_bytes` changed meaning. It was `operator_entries * 16 + 2 * D^2 * 8`;
it is now the operators' own reported bytes plus **three** dense blocks. The old figure undercounted
in two directions — the operators have a per-column spine and spare `Vec` capacity, and the accepted
quotient vectors were missing entirely. No resource budget changed.

`QuotientAlgebra::new_with_statistics` is new; `new` delegates to it and is unchanged.

---

## 7. References

1. Faugère, J.-C., Gianni, P., Lazard, D., Mora, T. (1993). *Efficient Computation of
   Zero-dimensional Gröbner Bases by Change of Ordering.* J. Symbolic Computation 16(4), 329–344.
2. Faugère, J.-C., Mou, C. (2017). *Sparse FGLM algorithms.* J. Symbolic Computation 80, 538–569.
3. Singular manual: `std`, `reduce`, `vdim`, `kbase`, `fglm`, `option(redSB)`.
4. *An Algorithm for Splitting Polynomial Systems Based on F4*, PASCO 2017.
5. `docs/MILESTONE-FGLM-SOLVING.md` — M17.
6. `docs/MILESTONE-F4-OPTIMIZATION.md` — M16.
