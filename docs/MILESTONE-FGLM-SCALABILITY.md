# Milestone: Quotient-Algebra and FGLM Scalability

**Status:** complete — M18-0 through M18-5
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
| M18-1 | border indexing, and deduplicated normal forms | **complete** |
| M18-2 | batched border reduction | **complete** |
| M18-3 | adaptive sparse/dense multiplication operators | **complete** |
| M18-4 | incremental-span memory, and a sparse-FGLM feasibility spike | **complete** |
| M18-5 | integration, ablations, and this document's conclusion | **complete** |

M18-3 and M18-4 are independent of M18-1 and M18-2 and of each other. All four depend on M18-0,
because none of them may be merged without evidence that it changed no answer.

**M18-1's result:** katsura-7's conversion from **39.0 ms to 27.7 ms**, cyclic-6's from 27.8 ms to
19.3 ms, nothing regressed, and no answer changed. §5.

**M18-2's result:** katsura-7's operator construction from **34.4 ms to 1.69 ms** and its whole
conversion from **37.3 ms to 2.59 ms** — 14.4x — with nothing in the corpus regressing *at the
recommended batch size*. An unbounded batch is 1.5x slower than the baseline on planted-10, which
is why the size is bounded rather than the strategy abandoned. §6.

**M18-3's result:** katsura-7's operators from **264.5 kB to 163.6 kB** and planted-10's from
640.0 kB to **380.0 kB**, by two unrelated changes — an adaptive per-column representation and an
exact one. §7.

**M18-4's result:** the dependence test's dense blocks 1.20x smaller, and a **no-go** on a full
sparse-FGLM milestone. The decisive measurement: the systems where classical FGLM's memory is the
problem are exactly the systems the shape-position route cannot convert. §8.

**M18-5's result:** the defaults are `BatchedBorder` at a batch of 64 with `Adaptive` storage,
measured at least as fast as M17's on **every** system in the corpus — 14.0x on katsura-7, 1.17x on
planted-10 — and never storing more, 1.41x less on katsura-7. Nothing composed adversely, 240
differential fixtures agree under all nine configurations, and 2,000 live systems agree under the
new defaults. **The bottleneck moved:** operator construction was 95% of katsura-7's conversion and
is 52%; the lex walk is now 69% of planted-10's and is the next milestone. §9.

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
  assembly under 2%, so neither the monomial lookup nor the coordinate-vector construction is worth
  attacking. **Deduplicating and batching the reductions is the only lever on this family that can
  matter.**

  One caveat on reading the `normal forms` column: the one-term `MultivariatePolynomial` built per
  border monomial is *inside* it, not inside `assemble`. So this table does not answer §5.3 of the
  proposal — whether that allocation is material — and M18-1 must measure it separately rather than
  infer it from here.
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
(`size_of::<Column<F>>()` was 24 at the time of this measurement, `size_of::<(usize, F)>()` is 16):

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

**This table is the M17 representation and M18-3 changed it.** The slack is gone — planted-10's
operators are 380 kB rather than 640 — and the operator figures in §3.5 are therefore a record of
what the baseline was, not of what the code does now. §7.1 has the before and after.

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
| oracle input | the system as sent | the ideal echoed back before anything is computed |
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
* An integer literal in a `poly` expression must stand alone: Singular sums bare literals in
  32-bit arithmetic before coercing them into the ring, so two constant terms are a different
  polynomial on the two sides. §4.6.
* A list is iterated by `ncols` and not `size`: those differ for an ideal with a zero generator.
  §4.6.
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

500 systems, two to five variables, degree at most 3, at most 4 terms per generator, cycling
through GF(2), GF(3), GF(7), GF(13), GF(65537) and GF(2^31 - 1). About 34 seconds per sweep.

| outcome | seed 12345 | seed 55555 |
|---|---:|---:|
| agreed, zero-dimensional | 195 | 199 |
| agreed, unit ideal | 193 | 189 |
| agreed, positive-dimensional and rejected by both | 112 | 112 |
| disagreed | 0 | 0 |
| oracle did not answer | 0 | 0 |

Four seeds times both construction strategies — 1,920 system-checks — are clean, as is a sweep
under `--operator-storage adaptive`. Every strategy this milestone adds has been pointed at the
oracle rather than only at the reference implementation.

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

### 4.6 What it found first: two faults in its own oracle interface

Pointed at a fresh seed during M18-3, the harness reported a **source-basis** disagreement — the
one check that would mean a bug in F4, which M18 does not touch. It was not. Both faults were in
the interface between the harness and Singular, and finding them is what the harness is for:
neither would have been visible from a final lex basis.

**Singular sums bare integer literals in 32-bit arithmetic before coercing them into the ring.**
Minimized to one generator over GF(2^31 - 1):

```text
ideal I = 1870573936+1536614746+x1;   // Singular reads  x1-887778614
ideal J = 1259705035+x1;              // Singular reads  x1-887778612
```

The two constants sum to 1259705035 modulo `p`; `-887778614` is the 32-bit signed wrap of their
integer sum, 3407188682. Multiplied by a variable the same coefficients are handled correctly —
`1870573936*x2+1536614746*x2` reads back as `-887778612*x2` — so it is specifically a sum of
*literals* in a `poly` expression. Zeebra's parser merges the terms and gets the ring answer, so an
unmerged polynomial was a **different ideal on the two sides**, through no fault of either
implementation.

The generator now merges terms on a shared monomial, which is what a polynomial should be anyway.

**`size` and `ncols` are different things for a Singular ideal.** `size` counts the *non-zero*
generators and `ncols` counts the slots, so `ideal I = 0, x1^2` has `size` 1, `ncols` 2, and `I[1]`
is the zero — and a loop bounded by `size` prints the zero and **skips `x1^2`**. Every list the
script emits was looped that way. The zero generator that exposed it came from the merge above
cancelling a GF(2) polynomial to nothing.

The loops are now bounded by `ncols`, the reported count is `ncols`, and zeros are dropped *after*
the count has been checked — so a lost line is still an error while a meaningless zero is not an
element.

**And the check that caught the second fault is the one the first fault motivated.** Singular now
echoes the ideal back before computing anything from it, and `Check::OracleInput` compares what it
read against what it was sent — as polynomials, sorted, with zeros dropped, since an oracle is
entitled to print `x1-887778612` for `1259705035+x1`, to list generators in its own order, and to
drop a zero generator. It runs first, because nothing after it means anything if the two sides are
not discussing the same ideal.

A fixture records `oracle_system: None` and inherits the check from the sweep that produced it: a
case only becomes a fixture after agreeing, and agreeing includes having been read correctly.

### 4.7 Minimization

A failing system is shrunk by four reductions, largest first: drop a generator, drop a term, flatten
a coefficient to one, lower an exponent. A candidate is accepted only if it still fails **the same
check** — a candidate that fails a different one is a different bug, and following it would walk the
search away from what the sweep found. The descent is greedy and finds no guaranteed minimum.

It is bounded by an attempt count and a wall clock, because each candidate costs a Singular
invocation and an unbounded search on a large failing system can take longer than the sweep that
found it. **The original system and its seed are always kept beside the shrunk one**, since a shrunk
system is no longer what the seed generates.

### 4.8 CI needs no Singular

A sweep's agreeing cases are emitted as Rust literals into
`src/grobner/differential/fixtures.rs` — the same convention `reference_bases.rs` already uses, for
the same two reasons: the compiler type-checks them, and reading them needs no parser and no new
dependency.

**240 cases are committed** — 96 when the harness landed, expanded at a wider generated shape in
M18-5 (§9.5). An ordinary test replays **the same comparison function** against them,
with a table of constants where the subprocess was, so the checks CI runs cannot drift from the
checks a development machine runs. Three further tests require the table to cover every supported
characteristic, every supported variable count, and all three ideal classes — a table of twenty
large-prime two-variable unit ideals would otherwise pass while checking almost nothing.

The live sweep is additionally an `#[ignore]`d test, so that `cargo test` can exercise the real
oracle path on request without ever depending on it.

### 4.9 What the harness does not reach

* **Characteristics above `2^31`.** Singular's limit, not Zeebra's. Unchanged from M17.
* **Large systems.** The generator makes small random systems, where the interesting thing is
  variety rather than size. The benchmark corpus — katsura, cyclic, planted — is checked by the
  existing tests and by the 29 reference bases, not by the sweep.
* **Monomial orders other than grevlex and lex.** The pipeline's source order and target order are
  what the conversion is about; `quotient_algebra.rs`'s own tests cover graded lex as a source.

---

## 5. M18-1: border indexing and deduplicated normal forms

### 5.1 What was built

Two things that used to be one. `BorderIndex` answers *where does this column point* — a
`ColumnTarget` per `(i, j)`, either a standard monomial's index or an index into the distinct
border monomials — and performs no field arithmetic at all. Reducing a border monomial is then a
separate question, asked once per column or once per monomial according to
`FglmOptions::operator_construction`:

* `OperatorConstruction::PerColumn` — M17's behaviour, kept as the reference and as the default.
* `OperatorConstruction::DeduplicatedBorder` — one normal form per distinct border monomial.

**Both strategies build the index**, so an ablation between them is an ablation of the sharing and
of nothing else: the classification, the reduction routine, and the coordinate assembly are
literally the same code. `FglmOptions::baseline()` names the M17 configuration so that every later
measurement has something fixed to be quoted against.

Each column still owns its own coordinate vector — the shared answers are *cloned* into the
operators, not reference-counted. So this strategy changes the time and leaves the storage exactly
where M17 had it, which is what makes the two comparable. Sharing a column's representation is
M18-3's question.

### 5.2 What it is worth

Criterion, same machine and methodology as §3.1, on a source basis prepared outside the timed
region:

| system | `D` | `\|∂B\|` | dup % | algebra, per-column | algebra, dedup | won | conversion, per-column | conversion, dedup | won |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| katsura-5 | 16 | 44 | 24.1 | 416 µs | 318 µs | 1.31x | 455 µs | 362 µs | 1.26x |
| katsura-6 | 32 | 100 | 27.5 | 3.21 ms | 2.39 ms | 1.34x | 3.53 ms | 2.58 ms | 1.37x |
| katsura-7 | 64 | 223 | 31.0 | **34.43 ms** | **24.34 ms** | **1.41x** | **39.02 ms** | **27.67 ms** | **1.41x** |
| cyclic-5 | 70 | 157 | 22.3 | 1.74 ms | 1.36 ms | 1.28x | 1.94 ms | 1.60 ms | 1.21x |
| cyclic-6 | 156 | 386 | 31.6 | 25.96 ms | 17.68 ms | 1.47x | 27.76 ms | 19.29 ms | 1.44x |
| planted-6 | 64 | 192 | 20.0 | 274 µs | 242 µs | 1.13x | 394 µs | 381 µs | 1.04x |
| planted-8 | 256 | 1,024 | 20.0 | 1.74 ms | 1.56 ms | 1.12x | 3.04 ms | 2.80 ms | 1.08x |

`cargo bench --bench fglm -- fglm_operator_construction`. The same comparison with the border
counters beside it, and with planted-10 included, is
`cargo run --release --example fglm_border`; its fastest-of-three figures agree with these to
within 5%.

**Katsura-7's conversion goes from 39.0 ms to 27.7 ms.** That is the milestone's headline so far,
and it is the whole of M18-1: no new algorithm, no change to any answer, just not reducing the same
monomial twice. Cyclic-6 does slightly better at 1.44x.

**Nothing regressed.** The planted family gains least — 1.04x to 1.08x on the conversion, because
the lex walk is most of what it does — but it does gain, and the construction itself is 1.12x to
1.13x faster there too. There is no instance in the corpus where deduplication is slower.

### 5.3 Two hypotheses, both refuted

The baseline raised two worries. Both were measured and neither held.

**"Repeated border monomials are cheap, so the duplication rate overstates the saving."** The
argument was that a monomial reached from two directions sits low in the order, which correlates
with a short reduction — so removing 31% of the *reductions* might remove much less than 31% of the
*time*. Against the ratio of reductions removed:

| system | reductions, per-column | reductions, dedup | ratio | measured speedup of the reduction stage |
|---|---:|---:|---:|---:|
| katsura-5 | 58 | 44 | 1.32x | 1.37x |
| katsura-6 | 138 | 100 | 1.38x | 1.36x |
| katsura-7 | 323 | 223 | 1.45x | 1.37x |
| cyclic-5 | 202 | 157 | 1.29x | 1.28x |
| cyclic-6 | 564 | 386 | 1.46x | 1.45x |
| planted-8 | 1,280 | 1,024 | 1.25x | 1.24x |

The measured speedup tracks the call-count ratio to within a few percent throughout, and on
katsura-5 slightly exceeds it. **Repeated border monomials cost about what the others do.** The
duplication rate is a usable estimate of the saving after all, which is a cheap counter predicting
an expensive quantity — worth knowing for M18-2.

**"The one-term `MultivariatePolynomial` per reduction is worth a specialized entry point"** —
§5.3 of the proposal. Both loops below walk the same border monomials in the same order; the first
stops at the polynomial, the second reduces it:

| system | construct | construct and reduce | construct's share |
|---|---:|---:|---:|
| katsura-6 | 0.008 ms | 2.077 ms | 0.38% |
| katsura-7 | 0.016 ms | 22.498 ms | **0.07%** |
| cyclic-6 | 0.029 ms | 15.190 ms | 0.19% |
| planted-8 | 0.077 ms | 0.981 ms | 7.83% |
| planted-10 | 0.403 ms | 7.158 ms | 5.63% |

**Rejected.** On the families where reduction dominates a conversion it is 0.07% to 0.38% of the
reduction, so a monomial-accepting entry point would buy nothing worth the second reduction path it
would create. The share is larger on the planted family only because the reductions there are
nearly trivial — and reduction is a quarter of planted-10's conversion, so 5.6% of it is 1.4% of
the whole. `normal_form` remains the only reduction in this module.

### 5.4 The resource budget under the new strategy

The shared vectors are allocated before any column exists, so `max_operator_entries` is checked
**as they fill** rather than only when the columns are pushed. That check is sound in the direction
that matters: every distinct border monomial appears in at least one column, so the shared entries
never exceed the operators' own, and the early check can never reject a system the reference path
would have accepted. Tested at the tight boundary — a budget of exactly what a system needs is
accepted by both strategies, and one entry less is rejected by both.

What does change is the **peak**: under deduplication the construction holds the shared vectors and
the operators at once, so its peak is up to twice the budget where the reference path's is exactly
the budget. The bound is provable rather than measured, and it is the honest cost of the strategy.

### 5.5 Correctness

* `QuotientAlgebra` derives `PartialEq`, so the strategies are compared as **whole values** — every
  column of every operator — rather than through the lex basis they lead to. A wrong column that
  happened not to change the final basis would pass the weaker check and fails this one. Run over
  three monomial orders, eight two-variable systems, two three-variable systems, katsura-5,
  katsura-6, cyclic-5 and planted-6.
* The lex bases are additionally compared end to end, over three orders, GF(7) and GF(2^31 - 1), and
  the benchmark corpus — together with `span_row_operations` and `operator_entries`, so a strategy
  that reached the same answer by doing different linear algebra would be caught.
* **Every committed differential fixture is verified under every strategy**, which is each one
  separately compared against Singular rather than against the other. Two implementations agreeing
  with each other and both being wrong is what an external oracle is for.
* A live sweep of 500 random systems under `--operator-construction deduplicated-border`, over
  GF(2) through GF(2^31 - 1) in two to five variables: 0 disagreements, 0 oracle failures.
* `BorderIndex` has its own tests: every column classified exactly as `QuotientBasis::index_of`
  classifies its product, repeated border monomials carrying one index, the border distinct and
  descending under the order, the border disjoint from the basis, the index reproducible, and the
  unit ideal having no border at all.

### 5.6 The default, and when it changed

**As of M18-1 it had not.** `FglmOptions::default()` was still `PerColumn`: deduplication is
measured faster on every instance in the corpus, agrees everywhere, and stores the same amount, so
this was sequencing rather than doubt — §12 of the proposal asks for defaults to be chosen from the
integration ablation in M18-5, when M18-2's batched reduction and M18-3's representations can be
weighed against it at the same time. §9.3 is where that was done, and the default is now
`BatchedBorder`, which is deduplicated too. A caller who wants plain deduplication writes

```rust
let options = FglmOptions::default()
    .with_operator_construction(OperatorConstruction::DeduplicatedBorder);
```

---

## 6. M18-2: batched border reduction

The principal new algorithm in the milestone, and the only remaining lever on the family where
conversion is the only route to a lex basis.

### 6.1 What the scalar path spends its time on

M18-1 removed the duplicated reductions. What is left is `|∂B|` independent normal forms, and each
one, per step, searches the basis for a divisor of its leading monomial, builds the multiple, and
subtracts it — through `MultivariatePolynomial`, which is a `HashMap<Monomial, F>`. The divisor
search is repeated for every monomial every target happens to pass through, the multiple is rebuilt
each time, and every coefficient touch is a hash lookup.

F4's answer to the same shape of problem is to do the symbolic work for a batch once and the
arithmetic over integer column indices. `OperatorConstruction::BatchedBorder` does that for border
monomials.

### 6.2 The closure, and why the targets cannot be echelonized

Start from the batch's targets. For every monomial `m` seen, if some `LM(g)` divides `m`, add the
reducer multiple `(m / LM(g)) * g` and look at its monomials too; stop when nothing new appears.
Each reducible monomial then has **exactly one** reducer row, which leads at it and whose other
monomials are strictly below it. Columns are the closure's monomials, descending.

**The targets must not reduce one another**, and this is the one way the batch differs from an F4
batch rather than a detail. An F4 matrix is echelonized: any row may become a pivot. Here each
target has its own answer — `NF(u_1)` must not involve `u_2` — so the pivots are **fixed** before
any target is touched, every pivot is a reducer multiple, and no target ever becomes one. That is
also why `linalg::reduce_rows_against_pivots_with` is not what runs: its contract is to echelonize
a lower block against an upper one, which for these targets would be the wrong computation rather
than a slower one. §6.3 of the proposal anticipated exactly this.

Reducing a target is then one descending pass over the columns: at each column with a nonzero,
subtract that column's reducer row if it has one. Nothing can reintroduce a nonzero in a column
already passed, because a reducer row leading at `c` has every other entry below `c`.

**The pass cannot stop at the first standard column.** A standard monomial can be *larger* than a
reducible one — with `G = {x^2, y^2}` under grevlex, `xy` is standard and `y^2 < xy` is not — so the
scan runs to the end. Stopping early would leave reducible monomials in the remainder.

### 6.3 What it is worth

`cargo run --release --example fglm_border`, whole conversion, fastest of three, milliseconds:

| system | `D` | `\|∂B\|` | per-column | dedup | batch 64 | batch ∞ | dedup | **batch 64** |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| katsura-5 | 16 | 44 | 0.51 | 0.40 | 0.14 | 0.13 | 1.27x | **3.78x** |
| katsura-6 | 32 | 100 | 3.56 | 2.70 | 0.52 | 0.50 | 1.32x | **6.85x** |
| katsura-7 | 64 | 223 | 42.92 | 31.58 | **2.69** | 2.39 | 1.36x | **15.97x** |
| cyclic-5 | 70 | 157 | 1.98 | 1.53 | 0.57 | 0.56 | 1.29x | **3.47x** |
| cyclic-6 | 156 | 386 | 29.77 | 19.60 | **2.82** | 2.78 | 1.52x | **10.57x** |
| planted-6 | 64 | 192 | 0.43 | 0.40 | 0.38 | 0.40 | 1.07x | 1.12x |
| planted-8 | 256 | 1,024 | 3.40 | 3.28 | 2.86 | 3.51 | 1.04x | 1.19x |
| planted-10 | 1,024 | 5,120 | 42.71 | 40.47 | 36.33 | 63.24 | 1.06x | 1.18x |

Criterion, `cargo bench --bench fglm -- fglm_operator_construction`, on a prepared source basis:

| system | operator construction, per-column | batched | won | whole conversion, per-column | batched | won |
|---|---:|---:|---:|---:|---:|---:|
| katsura-5 | 427 µs | 80 µs | 5.3x | 456 µs | 123 µs | 3.7x |
| katsura-6 | 3.25 ms | 322 µs | 10.1x | 3.41 ms | 519 µs | 6.6x |
| katsura-7 | **34.43 ms** | **1.69 ms** | **20.3x** | **37.29 ms** | **2.59 ms** | **14.4x** |
| cyclic-5 | 1.80 ms | 308 µs | 5.9x | 2.07 ms | 525 µs | 3.9x |
| cyclic-6 | 25.14 ms | 1.48 ms | 17.0x | 26.57 ms | 2.70 ms | 9.8x |
| planted-6 | 295 µs | 245 µs | 1.20x | 409 µs | 352 µs | 1.16x |
| planted-8 | 1.93 ms | 1.40 ms | 1.38x | 2.85 ms | 2.51 ms | 1.14x |

**Katsura-7's operator construction goes from 34.4 ms to 1.69 ms, and its whole conversion from
37.3 ms to 2.59 ms.** That is the milestone's headline, and it is where it was predicted to be:
§3.4 said 96% of that conversion was reducing border monomials and that nothing else was worth
attacking.

**Nothing regresses** — at the recommended batch size. That qualification is the interesting part.

### 6.4 The batch size matters, and it points opposite ways

| system | size 1 | 4 | 16 | 64 | unbounded |
|---|---:|---:|---:|---:|---:|
| katsura-6 | 1.95 | 0.95 | 0.68 | 0.53 | **0.50** |
| katsura-7 | 14.11 | 5.68 | 3.40 | 2.71 | **2.33** |
| cyclic-6 | 8.29 | 4.39 | 3.09 | 2.81 | **2.76** |
| planted-8 | **2.07** | 2.10 | 2.17 | 2.26 | 3.10 |
| planted-10 | **28.78** | 29.21 | 31.00 | 32.02 | 52.43 |

Monotonic in both directions, and they are opposite directions. On katsura and cyclic, a bigger
batch shares more closure and wins; on the planted family, a reduction is *one step*, so the closure
and the per-target column scan are nearly all of the work and a bigger batch is pure overhead —
unbounded is 1.5x **slower** than the M17 baseline on planted-10.

So §6.6 of the proposal was right to insist a new path not become the default on the strength of
katsura-7 alone. **The answer is not "keep the scalar path for sparse systems" but "bound the batch
size":** 64 targets is within 13% of the best size on katsura and 11% on the planted family, and is
faster than the scalar path on every system in the corpus. `BorderBatch::recommended()` uses it, and
`BorderBatchSize::Unbounded` is kept for measurement and documented as the wrong choice on a sparse
staircase.

Automatic sizing is still deferred, as §6.5 asks. The figures above are what a policy would be keyed
on, and 64 being safe everywhere is a weaker claim than knowing which systems want 1 and which want
unbounded — that needs a predictor of reduction depth, which this milestone does not have.

§6.7 re-measures this table after bounding the reduction buffer by its dirty range. The curve moves
at the unbounded end and **nowhere else**, so the figures above still stand as what a sizing policy
would be keyed on.

### 6.5 Resource limits and the fallback

`BorderBatch` bounds a batch's closure: reducer rows, columns, and reducer entries. All three are
checked **as the closure grows**, because it is discovered a row at a time and a batch that would
need a million multiples must not allocate them all before anyone notices.
`FglmError::BorderBatchExceeded` names which limit was crossed and its value, and deliberately not
the size the closure would have reached — finding that out is the work being refused.

`BatchOverflow` chooses what happens then, and **neither option drops a target**:

* `Fail` returns the error and the caller decides.
* `Scalar` reduces that batch's targets one at a time instead. The scalar path builds no closure, so
  it cannot cross these limits — it is the fallback that always exists.
  `BorderBatchStatistics::fallbacks` counts it, so a run that quietly took it is visible.

Tested both ways: at a column limit of one every batch overflows, `Fail` returns
`BorderBatchExceeded`, and `Scalar` finishes with `fallbacks == batches` and **the same operators as
the reference path**.

### 6.6 Correctness

* **The closure invariant is tested directly**, as §6.4 of the proposal asks, rather than inferred
  from the answers being right: every monomial a closure reaches is reducible exactly when the
  closure has a row leading at it, over three orders and ten systems. A reducible monomial without a
  row is one the reduction would leave in the remainder, which is how an incomplete closure fails.
* **Every batch's remainders equal the scalar `normal_form`s**, target for target, at batch sizes 1,
  4, 16, 64 and unbounded — so the answers are checked to be independent of how the targets were
  grouped, against the reference the milestone names rather than against another batch.
* **A target's answer does not depend on its batch**, which is §6.2's requirement stated as an
  observable property: reducing `u` alone and reducing it beside every other border monomial agree,
  and so does reducing the whole border in the opposite order. An implementation that let targets
  become pivots would fail this.
* Every remainder's monomials are standard, with no zero coefficients.
* The lex basis is compared over the **cross product** of three construction strategies and three
  storage strategies — nine configurations — and every differential fixture is verified under all
  nine.
* 900 live systems across three seeds, over GF(2) through GF(2^31 - 1), under
  `--operator-construction batched-border`: 0 disagreements, 0 oracle failures.

### 6.7 The reduction buffer, bounded by its dirty range

§6.4 named the per-target column scan as nearly all of the work on the planted family, and
`reduce_targets` made two of its three passes over the **whole** closure width per target: the
zeroing before a target and the extraction after it. Only the reduction scan between them was
bounded below by the target's leading column.

Neither unbounded pass had to be. `buffer[start] = one` is the only seed, and §6.2's triangularity
gives every reducer row leading at column `c` its other entries after `c` — so every write for a
target lands at or after `start` and `[0, start)` stays zero. The zeroing is therefore correct over
`[previous start, len)`: if the next `start` is larger that region is a superset of what was
written, and if it is smaller the gap below it was never written. The extraction starts at `start`
for the same reason. No new invariant, and a `debug_assert` that the prefix below the previous
target's column is still zero fails loudly if the column ordering ever changes.

**It did not flatten the curve.** §6.4's table re-measured, both variants built from the same tree
and pinned to one core, each cell the best of three runs of fastest-of-three:

| system | | size 1 | 4 | 16 | 64 | unbounded |
|---|---|---:|---:|---:|---:|---:|
| katsura-6 | before | 1.47 | 0.71 | 0.47 | 0.38 | 0.36 |
| | after | 1.47 | 0.71 | 0.47 | 0.39 | 0.37 |
| katsura-7 | before | 9.95 | 4.28 | 2.49 | 1.97 | 1.76 |
| | after | 9.94 | 4.23 | 2.47 | 1.96 | 1.74 |
| cyclic-6 | before | 6.30 | 3.35 | 2.38 | 2.19 | 2.13 |
| | after | 6.18 | 3.32 | 2.37 | 2.19 | 2.09 |
| planted-8 | before | 1.89 | 1.94 | 2.01 | 2.10 | 2.75 |
| | after | 1.93 | 1.99 | 2.05 | 2.11 | **2.55** |
| planted-10 | before | 27.18 | 27.26 | 27.71 | 28.31 | 46.74 |
| | after | 27.11 | 27.44 | 27.93 | 28.63 | **41.29** |

Every bounded size is inside the ±2% this harness repeats to. The one column that moves is
`unbounded`, by 7.3% on planted-8 and 11.7% on planted-10 — which shrinks the unbounded penalty
over the best size from 1.46x to 1.32x and from 1.72x to 1.52x. **The shape between 1 and 64 is
unchanged**, so §6.5's deferred sizing policy is keyed on the same curve as before and a predictor
of reduction depth has exactly as much to get right. That is the opposite of what filing this
expected, and it is the measurement rather than the expectation.

Why the gain sits where it does, from timing `reduce_targets` alone — the whole border reduced in
batches of each size, fastest of 25 within a process, best of five such runs:

| system | | size 1 | 4 | 16 | 64 | unbounded |
|---|---|---:|---:|---:|---:|---:|
| katsura-7 | before | 0.338 | 0.353 | 0.355 | 0.367 | 0.379 |
| | after | 0.333 | 0.348 | 0.348 | 0.359 | 0.363 |
| | | -1.6% | -1.5% | -2.0% | -2.2% | **-4.1%** |
| cyclic-6 | before | 0.213 | 0.201 | 0.210 | 0.238 | 0.337 |
| | after | 0.211 | 0.200 | 0.203 | 0.224 | 0.269 |
| | | -1.1% | -0.8% | -3.2% | -6.0% | **-20.2%** |
| planted-8 | before | 0.061 | 0.055 | 0.078 | 0.139 | 0.691 |
| | after | 0.060 | 0.055 | 0.071 | 0.133 | 0.539 |
| | | -2.4% | -0.9% | -9.8% | -4.4% | **-21.9%** |
| planted-10 | before | 0.243 | 0.242 | 0.387 | 0.785 | 18.73 |
| | after | 0.240 | 0.237 | 0.359 | 0.759 | 15.39 |
| | | -1.2% | -1.8% | -7.1% | -3.3% | **-17.8%** |

Every cell is faster and the gain grows with the batch, which is what the change predicts: the
saving is half of two passes over the **closure's** width, and the closure tracks the batch. On
planted-10 a batch of 64 reaches 122 columns on average and 192 at its widest, against 6,144 for one
unbounded batch — 50x — so a fifth of the unbounded scan is a few percent of the bounded one. At 64
the whole border's scan is 0.76 ms of a 28.6 ms conversion, so even removing it entirely would be
2.7%. That is why the conversion table cannot see this at the size the default uses.

`BorderBatch::recommended()` is **unchanged** at 64. The ablation, not this, is where that size is
chosen, and nothing above argues for moving it.

---

## 7. M18-3: adaptive operator storage

### 7.1 Two separate changes

**The representation got smaller before it got adaptive.** §3.5 found that 41% of planted-10's
operator bytes was `Vec`'s minimum allocation: a boxed slice is two words where a `Vec` is three,
and a `Vec` built by `collect` from a `HashMap`'s iterator — which is not `TrustedLen` — takes the
growth path, whose minimum non-zero allocation is **four** elements for a 16-byte element type. A
planted column holds one.

So the columns are now built with `Vec::with_capacity(len)` and stored as `Box<[_]>`. Neither is an
algorithmic change and both are pure wins:

| system | `D` | M17 representation | M18-3, still sparse | won |
|---|---:|---:|---:|---:|
| katsura-7 | 64 | 264.5 kB | 264.5 kB | 1.00x |
| cyclic-5 | 70 | 40.5 kB | 40.4 kB | 1.00x |
| cyclic-6 | 156 | 222.7 kB | 222.7 kB | 1.00x |
| planted-6 | 64 | 24.0 kB | 14.2 kB | 1.69x |
| planted-8 | 256 | 128.0 kB | 76.0 kB | 1.68x |
| planted-10 | 1,024 | 640.0 kB | **380.0 kB** | **1.68x** |

Katsura is untouched because its columns hold fifty entries, well past the point where `collect`
allocates exactly. The planted family gains two thirds of its operator storage back. The boxed
slice is also what keeps `Column` at three words after a third variant was added — a four-word
`Column` would have cost planted-10 another 80 kB of spine, which is more than that instance's
entries come to.

**Then the adaptive representation.** `OperatorStorage` chooses per column between
`(index, coefficient)` pairs and `D` bare coefficients, by comparing what the two would allocate.

### 7.2 What it is worth

`cargo run --release --example fglm_storage`. Exact figures, not timings: a boxed slice has no
spare capacity, so these are the bytes allocated.

| system | `D` | reduced columns | fill % | `Sparse` | `Adaptive` | `Dense` | dense of | won |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| katsura-5 | 16 | 58 | 80.9 | 13.6 kB | **9.0 kB** | 9.1 kB | 53 | 1.52x |
| katsura-6 | 32 | 138 | 80.6 | 60.1 kB | **37.7 kB** | 39.0 kB | 123 | 1.59x |
| katsura-7 | 64 | 323 | 78.6 | 264.5 kB | **163.6 kB** | 172.0 kB | 276 | **1.62x** |
| cyclic-5 | 70 | 202 | 14.6 | 40.4 kB | 40.4 kB | 118.7 kB | 0 | 1.00x |
| cyclic-6 | 156 | 564 | 14.6 | 222.7 kB | 222.7 kB | 709.3 kB | 0 | 1.00x |
| planted-6 | 64 | 240 | 2.2 | 14.2 kB | 14.2 kB | 129.0 kB | 0 | 1.00x |
| planted-8 | 256 | 1,280 | 0.5 | 76.0 kB | 76.0 kB | 2,608.0 kB | 0 | 1.00x |
| planted-10 | 1,024 | 6,400 | 0.1 | 380.0 kB | 380.0 kB | 51,440.0 kB | 0 | 1.00x |

Three things this table settles.

**The crossover is inside the corpus.** A reduced column holds 79–81% of `D` on katsura and 0.1–2%
on the planted family. There is no single representation that is right for both, and that is the
justification for the strategy existing at all — not an assumption about what sparse matrices are
usually like.

**`Adaptive` beats *both* extremes on katsura**, at 9.0 kB against sparse's 13.6 and dense's 9.1.
That is only possible because the choice is per column: katsura-5 has 58 reduced columns of which 53
are dense enough to be worth holding densely and five are not. A per-operator or per-crate choice
could not have reached it.

**`Dense` everywhere is ruinous, and the strategy exists to show that rather than to be used.**
planted-10 would need 51 MB where it needs 380 kB — 135x. §7.2 of the proposal asked whether a whole
operator must be one or the other; the answer is a definite no.

### 7.3 What it costs

Storage is exact; application has to be measured, because the conversion applies an operator `O(D)`
times and a representation that halves the memory and slows that down may not be worth having.

`cargo bench --bench fglm -- fglm_operator_application`, in microseconds for all `N` operators
applied once:

| system | `Sparse`, unit | `Adaptive`, unit | `Dense`, unit | `Sparse`, dense | `Adaptive`, dense | `Dense`, dense |
|---|---:|---:|---:|---:|---:|---:|
| katsura-6 | 0.173 | 0.177 | 0.240 | 9.31 | 9.62 | 10.49 |
| katsura-7 | 0.371 | 0.370 | 0.500 | 43.78 | 44.73 | 49.76 |
| cyclic-6 | 0.731 | 0.767 | 1.100 | 33.63 | 32.91 | 203.15 |
| planted-8 | 1.504 | 1.487 | 1.457 | 7.05 | 6.95 | **753.50** |

A unit input is what the lex walk starts with and a dense one what it ends with, and the sparse path
skips a zero input coordinate where the dense path still walks `D` cells — so the two inputs are
genuinely different questions.

**`Adaptive` is slower than `Sparse` on katsura's dense-vector application, and only there.** The
two harnesses disagree about how much: Criterion says 2.2% on katsura-7, and
`examples/fglm_storage.rs`'s fastest-of-three says 10–14% across repeated runs. They agree on the
direction and on the reason — a 79%-full dense column does `D` multiplications where the sparse form
does 0.79 `D`, and an index lookup is cheaper than a multiplication. Where `Adaptive` picks sparse
for every column, it is `Sparse` and the figures are noise around equality.

**At the level a caller pays it makes no difference.** The whole conversion under each storage,
fastest of three:

| system | `Sparse` | `Adaptive` | `Dense` |
|---|---:|---:|---:|
| katsura-6 | 3.59 ms | 3.59 ms | 3.59 ms |
| katsura-7 | 42.52 ms | 42.58 ms | 41.96 ms |
| cyclic-6 | 28.36 ms | 28.38 ms | 27.94 ms |
| planted-8 | 3.26 ms | 3.24 ms | 4.13 ms |

Within 1% throughout except dense planted-8, which is 27% slower. Operator application is simply
not where a conversion's time goes — reduction is on katsura and the span's row operations are on
planted — so a 2% change to it does not survive to the total.

So the trade is: **1.62x less operator memory on katsura for a few percent of a cost that is not on
the critical path.** Worth taking, and not so decisively that it should be taken without the
integration ablation seeing it beside M18-2 and M18-4.

### 7.4 Byte-aware accounting and a second budget

`FglmMemory` now distinguishes three quantities for the operators, because they are three numbers:

* `operator_entries` — mathematical nonzeros. Unchanged in meaning, and **no strategy may change
  it**, which the tests assert.
* `operator_cells` — field-element slots allocated. Equal to the entries while every column is
  sparse, and larger wherever one is dense.
* `operator_bytes` — what the representations actually take, now exact for the heaps since a boxed
  slice has no capacity to diverge from its length.

`max_operator_bytes` is a **new budget beside** `max_operator_entries`, not a redefinition of it.
Under dense storage the same nonzeros occupy `D` cells, so a budget written in entries cannot see
the difference — and changing what the older limit counted would have made every figure recorded
against it ambiguous. `FglmError::OperatorBytesExceeded` is its error, and it is enforced from what
the builder reports having stored rather than from a model of what it should have stored.

Tested where it matters: a budget sized from planted-6's sparse operators rejects the same system
held densely, with the *entry* budget unbounded throughout — so what fires can only be the byte
budget.

### 7.5 Correctness

* Every representation gives the same columns, the same applications on unit, sparse, dense and
  zero inputs, and the same nonzero count. Asserted at the column level in `multiplication.rs` and
  over three orders, ten systems, katsura-5/6, cyclic-5 and planted-6 in `quotient_algebra.rs`.
  **Not** a `QuotientAlgebra` equality — the representations differ, so the values differ, and
  comparing them through what a caller can observe is the point.
* The lex basis is compared over the **cross product** of construction and storage, six
  configurations, because a construction strategy and a storage strategy could each be right alone
  and wrong together.
* Every differential fixture is verified under all six configurations, each against Singular.
* `Adaptive` is asserted no larger than either extreme on every family, strictly smaller than
  `Sparse` on katsura-7, and exactly equal to `Sparse` on planted-8 — the last being the claim that
  it correctly declines to hold a 0.5%-full column densely.
* A zero column allocates nothing under both `Sparse` and `Adaptive`, which is §7.2's requirement
  for a compact zero representation; the sparse form already was one.

### 7.6 The default, and when it changed

**As of M18-3 it had not.** `FglmOptions::default()` was still `OperatorStorage::Sparse`, for the
same reason the construction default was unchanged — see §5.6. §9.3 chose `Adaptive` from the
integration ablation. The two representation changes in §7.1 are *not* behind a strategy flag,
because they are not strategies: they make the sparse representation smaller without changing it.

---

## 8. M18-4: FGLM's memory, and the sparse-FGLM spike

Two deliverables with nothing in common except the quantity they are about. The first is an
optimization; the second is a research question with a verified prototype and a **no-go**.

### 8.1 The combination block is triangular

`IncrementalSpan` carries two blocks per echelon row: the row's `D` coordinates, and its expression
in terms of the accepted vectors. M17 padded the second to `D` as well.

It does not need to be. A row inserted when the accepted rank is `r` is a combination of the `r + 1`
vectors accepted up to and including the one that produced it — it **cannot** involve one accepted
afterwards, so coefficients beyond `r` are structurally zero. Summed over the rows:

| block | M17 | M18-4 |
|---|---:|---:|
| coordinates | `D^2` | `D^2` |
| combinations | `D^2` | `D (D + 1) / 2` |
| accepted vectors | `D^2`, uncounted | `D^2` |
| **total** | `3 D^2` | `2 D^2 + D (D + 1) / 2` |

A quarter off the span, exactly, with nothing traded: the padding was zeros. Measured:

| system | `D` | M17 dense blocks | M18-4 | won |
|---|---:|---:|---:|---:|
| katsura-7 | 64 | 96.0 kB | 80.2 kB | 1.20x |
| cyclic-6 | 156 | 570.4 kB | 475.9 kB | 1.20x |
| planted-8 | 256 | 1,536.0 kB | 1,281.0 kB | 1.20x |
| planted-10 | 1,024 | 24,576.0 kB | **20,484.0 kB** | 1.20x |

**The coordinate rows of both tables changed again after the milestone**, by the same argument
applied to the other block: §8.6.

The coefficients a dependence reports must still be exact over the **original** accepted vectors —
§8.2 of the proposal calls that correctness-critical, and it is the thing a triangular block could
break. Tested on a Vandermonde basis, where there is no structure for an error to hide behind.

### 8.2 `max_span_entries` now counts all three blocks

It counted two of them and priced both as squares, so at `D = 16` it budgeted 512 cells where the
conversion then allocated 648 — and allocates 528 after §8.6. **A budget cannot protect memory it
does not know about**, and §8.1 of the proposal asks for all substantial arrays to be recorded and
budgeted — so the limit's meaning has changed. Loudly: the option's documentation says so, the
error's value changed in a test that states the arithmetic, and `FglmMemory` reports each block
separately so a figure quoted against the old meaning can be recomputed. Checked arithmetic
throughout, since a budget computed from a wrapped product is no budget.

### 8.3 The sparse-FGLM spike: shape position

`fglm::shape` detects shape position and, where it holds, produces the lex basis from one variable's
Krylov sequence. `cargo run --release --example fglm_shape`.

**Which systems are in shape position:**

| system | `N` | `D` | degree of `x_{N-1}` | separating variables | shape basis |
|---|---:|---:|---:|---|---|
| katsura-3 | 3 | 4 | 4 | `x_0, x_2` | yes |
| katsura-4 | 4 | 8 | 8 | `x_0, x_3` | yes |
| katsura-5 | 5 | 16 | 16 | `x_0, x_4` | yes |
| katsura-6 | 6 | 32 | 32 | `x_0, x_5` | yes |
| katsura-7 | 7 | 64 | 64 | `x_0, x_6` | yes |
| cyclic-3 | 3 | 6 | 3 | none | no |
| cyclic-5 | 5 | 70 | 15 | none | no |
| cyclic-6 | 6 | 156 | 48 | none | no |
| planted-4 | 4 | 16 | 4 | none | no |
| planted-6 | 6 | 64 | 4 | none | no |
| planted-8 | 8 | 256 | 4 | none | no |

The whole katsura family, and nothing else. On the random differential corpus, **76 of the 120
zero-dimensional fixtures** are in shape position — 26 of 38 on the corpus as it stood in M18-4,
so 68% then and 63% after M18-5 expanded it. The shape route agrees with Singular on every one of
them, and that check runs in every sweep and on every fixture, not only in the module's own tests.

**Detection is algebraic, not a solution count.** What is tested is whether `1, t, ..., t^{D-1}` are
independent. `<x - 1, (y - 1)^2>` has one point over the base field, quotient dimension two, and
*is* in shape position; `<x^2, y^2>` has one point, dimension four, and is not. A test that counted
points would get both wrong.

**What it costs:**

| system | `D` | lex walk | shape route | route | classical, end to end | shape, end to end | end | classical cells | shape cells | cells |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| katsura-3 | 4 | 0.004 | 0.004 | 1.08x | 0.01 | 0.01 | 1.04x | 42 | 30 | 1.40x |
| katsura-4 | 8 | 0.011 | 0.011 | 1.03x | 0.06 | 0.06 | 0.99x | 164 | 108 | 1.52x |
| katsura-5 | 16 | 0.036 | 0.041 | 0.87x | 0.43 | 0.43 | 1.01x | 648 | 408 | 1.59x |
| katsura-6 | 32 | 0.138 | 0.236 | 0.59x | 3.14 | 3.23 | 0.97x | 2,576 | 1,584 | 1.63x |
| katsura-7 | 64 | 0.749 | 2.018 | **0.37x** | 37.54 | 37.90 | 0.99x | 10,272 | 6,240 | **1.65x** |

Milliseconds. `lex walk` and `shape route` start from a prepared quotient algebra; the end-to-end
columns include building it, which neither route can avoid.

**§8.6 changed both cell columns**, since the span is in both: at `D = 64` they are 8,256 and
4,224, so the ratio is 1.95x rather than 1.65x. Both routes drive the same `IncrementalSpan`, so
both also got faster; the time columns are a ratio between them and were not re-measured.

**The shape route is slower, and the reason is instructive.** It does `D` span reductions where the
walk does about `D + |G|`, which is comparable — but the walk's vectors are the *classes of
monomials*, which are sparse early on, and `reduce` skips a row whose pivot column is zero in the
input. The powers of a single variable densify immediately, so the shape route pays close to the
full `D^3 / 2` where the walk pays much less. At `D = 64` that is 2.7x.

End to end it vanishes into a wash — 0.97x to 1.04x — because the operators are 90–96% of a
conversion on this family. Which is the same observation §3.4 made, from the other side.

### 8.4 Verification, and why it is not `normal_form`

The prototype verifies its own output before returning it, deterministically. Two facts prove the
result is the reduced lex basis:

1. **Every polynomial is in `I`** — checked by evaluating it at the multiplication operators and
   requiring the zero vector.
2. **The leading monomials are `t^D` and `x_0, ..., x_{N-2}`** — true by construction, and the ideal
   they generate has exactly `1, t, ..., t^{D-1}` as standard monomials, `D` of them.

A set of polynomials in `I` whose leading monomials generate a monomial ideal of the same finite
quotient dimension as `LT(I)` generates `LT(I)`, because a monomial ideal contained in another with
equal quotient dimensions equals it. So the set is a Gröbner basis, and each element is monic with no
term divisible by another's leading monomial, so it is the reduced one.

**Reducing modulo the grevlex source basis would have been the obvious check and is the wrong one.**
`p(t)` has degree `D` in one variable, which under grevlex is as far outside the staircase as a
monomial gets. Tried: it did not finish on cyclic-6 in ten minutes. Avoiding exactly that reduction
is why one converts bases at all. Evaluating at the operators is `O(N D)` operator applications,
independent of the echelon form that produced the coefficients — cheaper *and* a real second
opinion. The unit tests additionally reduce modulo the source basis on small systems, where it is
affordable.

Nothing here is probabilistic, so there is no certified-versus-conjectural distinction to expose.

### 8.5 The deliverable: no-go, and why

The M18 proposal asks six questions of the spike — a different document's numbering from this
one's.

**1. Which benchmark systems meet the shape-position criterion?** The katsura family at every size,
and nothing else in the corpus. 68% of the random differential fixtures.

**2. How much work would a specialized converter save?** On time, none: it is 2.7x *slower* on the
route at `D = 64` and a wash end to end. On memory, 1.65x fewer dense cells.

**3. Can it recover the complete ideal, including multiplicities?** Yes, exactly and deterministically
— it produces the reduced lex basis, which determines the ideal. Nonradical ideals in shape position
convert correctly; nonradical ideals that are not are rejected rather than radicalized.

**4. What verification would make a probabilistic approach safe to expose?** The one in §8.4, which
is complete and costs `O(N D)` operator applications. A Wiedemann variant choosing a random linear
form or a random separating element could reuse it unchanged, so such a variant could be exposed as
certified rather than conjectural. This is the one unambiguously reusable result of the spike.

**5. What memory limits would remain?** The echelon form, `D (D + 1)` cells after §8.6. The shape
route removes the accepted-vector block and nothing else, so it is still `O(D^2)`. Only replacing the
echelon form — a scalar Krylov sequence of length `2D` plus Berlekamp–Massey — gets to `O(D)`, and
Zeebra has no Berlekamp–Massey.

**6. Is a full sparse-FGLM milestone justified? No.** Three measurements decide it, and the third is
the one that matters:

* **Where conversion is the only route, the cost is not the conversion.** Katsura-7's lex basis is
  beyond F4's limits, so FGLM is the only way to it — and 96% of that conversion is reducing border
  monomials, which sparse FGLM does not touch. M18-2's batched reduction is the lever there, not a
  new dependence algorithm.
* **Where the dense blocks dominate, the ideal is not in shape position.** planted-10's blocks are
  54x its operators — and planted-10's last variable has a minimal polynomial of degree 4 in a
  1,024-dimensional quotient. **The systems where memory is the problem are exactly the systems the
  shape route cannot convert.** That is the decisive finding and it was not predictable from the
  proposal.
* **And on those systems one should not be converting at all.** planted-8's lex basis takes F4
  **0.04 ms** directly, against a 2.8 ms conversion. M17 already made that the default; the memory
  pressure in classical FGLM on the planted family is pressure on a route no caller should take.

What is justified is what has been built: the shape detector and the verified shape converter, kept
as `fglm::shape` — public, tested, validated against Singular on 26 ideals, and not wired into
`FglmOptions` as a strategy. It is 1.65x less memory at a wash in time on the one family it covers,
and it is the foundation a Berlekamp–Massey route would stand on if a workload with large
shape-position quotients ever appears. Measuring whether the algebraic-hash systems that motivate
this project's architecture are in shape position is the thing to do **before** committing to such a
milestone, not after.

### 8.6 Follow-up (issue #56): the coordinate block is triangular too

Filed and done after the milestone closed, by §8.1's argument applied to the other block. An
echelon row is reduced against every earlier row before it is inserted, so it is **zero below its
own pivot**, and nothing writes to a row afterwards — `reduce` only reads. So a row leading at
`pivot` stores `D - pivot` coordinates and the subtraction loop starts there:

| block | M17 | M18-4 | now |
|---|---:|---:|---:|
| coordinates | `D^2` | `D^2` | `D (D + 1) / 2` |
| combinations | `D^2` | `D (D + 1) / 2` | `D (D + 1) / 2` |
| accepted vectors | `D^2`, uncounted | `D^2` | `D^2` |
| **span** | `2 D^2` | `D^2 + D (D + 1) / 2` | **`D (D + 1)`** |
| **total** | `3 D^2` | `2 D^2 + D (D + 1) / 2` | `D^2 + D (D + 1)` |

Nothing is traded — this padding was zeros as well — and the saving is worth stating as a
percentage rather than as a ratio, because the two are easy to confuse and one of them was
confused in review. The span loses `D^2 - D (D + 1) / 2` cells, which is **a third of it in the
limit and less than that at every finite `D`**: 30.6% at `D = 16`, 32.6% at 64, 33.3% at 1,024.
Against all three blocks the same cells are **a fifth**, not a quarter: 18.5% at `D = 16` and
20.0% at 1,024. The before/after *ratio* is 1.25x, and a 1.25x ratio is a 20% reduction.

| system | `D` | M18-4 dense blocks | now | ratio | cut |
|---|---:|---:|---:|---:|---:|
| katsura-7 | 64 | 80.2 kB | 64.5 kB | 1.24x | 19.6% |
| cyclic-6 | 156 | 475.9 kB | 381.5 kB | 1.25x | 19.8% |
| planted-8 | 256 | 1,281.0 kB | 1,026.0 kB | 1.25x | 19.9% |
| planted-10 | 1,024 | 20,484.0 kB | **16,392.0 kB** | 1.25x | 20.0% |

Measured with `cargo run --release --example fglm_profile`; the percentages are the exact
arithmetic above, which the kB figures reproduce.

The two steps were measured separately, because the time win and the memory win have different
causes and the issue asked for them to be attributed rather than bundled. `prefix skip` is the
subtraction loop starting at the row's pivot with the representation unchanged; `offset` is the
representation change on top of it. Lex-walk milliseconds, the `walk` column of `fglm_profile`,
fastest of three runs of an example that itself reports the fastest of three conversions, each
variant built into its own target directory and identified by the storage table it printed:

| system | `D` | M18-4 walk | prefix skip | offset | won | conversion, M18-4 → now |
|---|---:|---:|---:|---:|---:|---:|
| katsura-7 | 64 | 0.84 | 0.72 | 0.69 | 1.22x | 2.31 → 2.14 ms |
| cyclic-6 | 156 | 1.24 | 0.99 | 0.96 | 1.29x | 2.47 → 2.22 ms |
| planted-8 | 256 | 1.03 | 0.97 | 0.89 | 1.16x | 2.37 → 2.22 ms |
| planted-10 | 1,024 | 23.61 | 20.98 | **12.68** | **1.86x** | 32.50 → 20.47 ms |

**The prefix skip is the smaller half, and that is the interesting part.** The field operations
saved are the same in both columns — the skip already avoids every multiply-and-subtract below the
pivot, and `span_row_operations` is identical across all three variants, because the loop over the
rows and its zero test are untouched. What the representation change adds is a smaller working
set: planted-10's coordinate block goes from 8 MB to 4.2 MB, and only on that instance, where the
block does not fit in cache either way, does it matter. At `D = 64` the two columns differ by
0.03 ms.

**The ceiling, stated as the issue asked.** On katsura-7 the walk is 32% of a conversion and the
dense blocks are 0.4x the operators, so 1.22x on the walk is 1.08x end to end and the memory win is
16 kB. The figure worth quoting is planted-10's — and §8.5's third bullet still stands: F4 gets
planted-8's lex basis directly in 0.04 ms against a 2.2 ms conversion, so **this makes a route
faster that callers are already steered away from.** That bounds the value, and is why this was an
issue and not a milestone.

`max_span_entries` moved with the arithmetic, for the reason §8.2 gives: a budget that prices a
block the conversion no longer allocates is the same bug as one that misses a block it does. At
`D = 16` the three blocks are 528 cells where M18-4 counted 648 and M17 counted 512, and the
default 20 million cells now admits `D = 3,162` rather than 2,828 — **12% on the reachable
dimension, from a 20% saving on a quadratic.** That is the honest shape of this change: it does
not move the asymptotics, and §9.7's reading of where FGLM's memory limit lies is unaffected.

### 8.7 Follow-up (issue #59): the reduction happens in registers the span owns

`linalg` already had the discipline: `DenseAccumulator` is a dense working row the elimination
keeps and reuses, and its buffer lives in the accumulator rather than in its caller.
`IncrementalSpan` is the same object and allocated per call — a `D`-cell residue and an `r`-cell
combination on each of the walk's `D + |G|` reductions. Both now live in the span.
`reduce_in_place` fills them and `insert_scratch` reads them back, so **the dependence test**
allocates nothing per candidate; `reduce` is still there, still returns owned vectors, and hands
the registers' buffers out rather than copying out of them, so it costs exactly what it did
before.

Said precisely, because the looser version of it was corrected in review: the walk still allocates
per candidate — `MultiplicationOperator::apply` returns an owned `Vec<F>` for the candidate's
class, and a dependent candidate still builds a relation polynomial. What this removes is the
span's two, which are the two that were pure overhead: a buffer allocated, filled, read once, and
dropped.

**The measurement protocol is stricter than §8.6's**, because the effect expected here was a few
percent and §8.6's protocol could not have seen it: each variant is a separate target directory,
every run is pinned to one core with `taskset`, and 30 runs of each variant are interleaved so that
machine drift hits all of them equally. The figure quoted is the median of the `walk` column, each
run of the example itself reporting the fastest of three conversions. Unpinned, the same binary
varies by ±15% on planted-10 — which is why the first attempt at this measurement was discarded.

| system | `D` | §8.6 walk | registers | won | conversion |
|---|---:|---:|---:|---:|---:|
| katsura-7 | 64 | 0.70 | 0.68 | 1.03x | 2.14 → 2.13 ms |
| cyclic-6 | 156 | 0.97 | 0.92 | 1.05x | 2.22 → 2.18 ms |
| planted-8 | 256 | 0.98 | 0.87 | 1.13x | 2.30 → 2.19 ms |
| planted-10 | 1,024 | 11.67 | **10.25** | **1.14x** | 18.62 → 17.14 ms |

Slightly better than the issue's own expectation of "a few percent on the lex walk, not a factor",
and for the reason it gave: the per-call term is small but it is multiplied by `D + |G|` calls.

#### Both follow-ups together, under one protocol

§8.6's table and this one were measured under different protocols, so dividing one by the other is
not a controlled comparison. This is: `main` at the commit before §8.6 — which already carries
issue #57's batch-buffer change — against §8.6 and §8.7 integrated, two binaries built from
separate trees into separate target directories, `md5sum`-checked as distinct, identified by the
storage figure they print, pinned to one core, and run 30 times each interleaved.

| system | `D` | walk before | walk after | won | conversion | dense blocks |
|---|---:|---:|---:|---:|---:|---:|
| katsura-7 | 64 | 0.84 | 0.69 | 1.22x | 2.29 → 2.13 ms | 80.2 → 64.5 kB |
| cyclic-6 | 156 | 1.26 | 0.94 | 1.34x | 2.51 → 2.17 ms | 475.9 → 381.5 kB |
| planted-8 | 256 | 1.39 | 0.90 | 1.54x | 2.76 → 2.23 ms | 1,281.0 → 1,026.0 kB |
| planted-10 | 1,024 | 23.16 | **11.07** | **2.09x** | 32.11 → 18.33 ms | 20,484 → 16,392 kB |

Medians. The two steps' separately measured factors multiply to 1.86 x 1.14 = 2.12 on planted-10
against 2.09 measured together, which is the agreement that makes the attribution in §8.6 and §8.7
worth believing. **This is the table to quote**; the per-step tables are there to say which half
came from where.

#### The registers are storage, and no budget counts them

They are `2 D` cells the span now holds for its lifetime where it previously allocated and dropped
the same two vectors per call. `FglmMemory` does not report them and `max_span_entries` does not
price them, which is a deliberate choice and not an oversight:

* **They are `O(D)` against the blocks' `O(D^2)`** — 2,048 cells beside 2,098,176 at `D = 1,024`,
  which is 0.098%, and 16 kB of the 16,392 kB the conversion already reports. At `D = 16` the
  share is 6%, where the absolute figure is 256 bytes.
* **They do not raise the peak.** A residue and a combination were live during every reduction
  before this change as well; what changed is that the buffers persist between reductions instead
  of being freed and reallocated. A budget enforced before allocation, which is what
  `max_span_entries` is, would have had to admit them either way.
* **`max_span_entries` has already changed meaning twice** — §8.2 and §8.6 — and each change made
  every figure recorded against the older meaning ambiguous. Doing it a third time for a term that
  rounds to zero against the budget's own quantity would cost more in comparability than it buys in
  accuracy.

`IncrementalSpan::stored_cells` keeps its meaning too: the echelon rows, which is the storage that
grows. The exclusion is documented where a caller reading a budget would meet it —
`FglmMemory::dense_blocks_for`, `FglmOptions::max_span_entries`, and the module documentation —
rather than left to be inferred from the absence of a field.

#### What was rejected, and measured before being rejected

The issue named three per-call overheads and this takes two of them. The third — the full-`D`
`residue.iter().all(is_zero)` dependence test — was to become a counter maintained by the
subtraction loop, the way `DenseAccumulator::subtract_scaled` maintains `nonzeros`. **Measured on
top of the registers, it does not pay**, and a third design was tried beside it:

| variant | katsura-7 | cyclic-6 | planted-8 | planted-10 |
|---|---:|---:|---:|---:|
| registers | 0.68 | 0.92 | 0.88 | 11.08 |
| + maintained nonzero count | 0.64 | 0.97 | 0.88 | 11.31 |
| + zero test over non-pivot columns only | 0.65 | 0.91 | 0.88 | 10.99 |

Medians, same protocol, 25–30 interleaved runs; this batch was measured before `reduce` was given
its final form, so its register column is not identical to the table above.

**Why the counter loses, which is a difference from `DenseAccumulator` and not a surprise.** There
the subtraction loop runs over a *sparse* row's support and the zero test is consulted repeatedly
per row, so a counter replaces many full-width scans with work proportional to the support. Here
the subtraction loop is the `O(D^3)` part of the algorithm and the scan happens once per call, so
maintaining the count adds two operations to every subtracted cell — `O(D r)` per call — to remove
one `O(D)` scan. It also needs the residue's initial count, which is another full pass over `D`.
Trading a scan at the end for a scan at the start plus work in the dominant loop is a bad trade,
and cyclic-6 shows it as a 5% regression.

The second design is sound and still not worth having. A forward pass clears every pivot column —
that is the invariant the single pass already rests on — so the residue is zero exactly when the
**non-pivot** columns are, and there are `D - r` of those: zero work at full rank, which is where
the walk spends most of its candidates. It measures within 1% of the registers alone on every
system. The issue's own standard applies: "a change that does not move it is not worth the
invariant", and this one would add a `Vec<usize>` to maintain and a second way for the dependence
verdict to be wrong.

So the zero scan stays. Note that it is `all`, not a count: on an independent vector it stops at
the first nonzero, which on the walk is usually immediately.

---

## 9. M18-5: integration

Four changes were measured one at a time against M17. This section measures them **together**,
chooses the defaults from that measurement, and says where the next milestone's cost is.

Two of the four cannot be ablated and that is part of the result. M18-3's compact sparse column —
a `Box<[_]>` of exact capacity where a `Vec` grown by `collect` was — and M18-4's triangular
combination block are not behind options, because neither is a strategy: they make a representation
smaller without changing what it represents. Both are therefore in **every row below, the baseline
included**, and §3.5 and §8.1 hold the M17 figures they were measured against. So `baseline` here
means M17's *strategies* at M18's representations, which is the comparison a caller choosing a
strategy today actually faces.

### 9.1 The ablation

`cargo run --release --example fglm_ablation`, nine configurations per system, whole conversion,
fastest of three, milliseconds. One source basis per system, computed outside the measurement, with
the lex basis and the operators' nonzero count asserted equal to the baseline's on every row. Six
of the nine are below; `-- list` names them all:

| system | `D` | baseline | 1: dedup | 2: batch 64 | **2+3** | 2: batch ∞ | 3: dense | **won** |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| katsura-5 | 16 | 0.52 | 0.41 | 0.14 | **0.13** | 0.13 | 0.51 | **3.96x** |
| katsura-6 | 32 | 3.58 | 2.69 | 0.52 | **0.53** | 0.69 | 3.57 | **6.76x** |
| katsura-7 | 64 | 38.25 | 28.67 | 2.66 | **2.73** | 2.38 | 42.23 | **14.03x** |
| cyclic-5 | 70 | 2.15 | 1.75 | 0.55 | **0.55** | 0.56 | 2.17 | **3.93x** |
| cyclic-6 | 156 | 27.83 | 19.65 | 2.81 | **2.78** | 2.72 | 27.39 | **10.01x** |
| planted-6 | 64 | 0.43 | 0.39 | 0.37 | **0.37** | 0.39 | 0.44 | **1.17x** |
| planted-8 | 256 | 3.16 | 2.90 | 2.59 | **2.59** | 3.57 | 5.06 | **1.22x** |
| planted-10 | 1,024 | 41.49 | 39.24 | 35.83 | **35.51** | 60.47 | 74.40 | **1.17x** |

Under Criterion, `cargo bench --bench fglm -- fglm_recommended`, which times
`FglmOptions::recommended()` against `FglmOptions::baseline()` on a prepared source basis and
asserts the two lex bases equal first: katsura-6 **3.53 ms to 522 µs**, katsura-7 **41.19 ms to
2.76 ms**, cyclic-6 **27.59 ms to 2.78 ms**, planted-8 **3.09 ms to 2.61 ms**. The two harnesses
agree within 1.5% on the recommended configuration; their *baseline* figures differ by up to 8%,
which is the run-to-run spread §9.2 warns about and the reason the ratios are quoted from a single
process.

And the memory, which is exact rather than timed:

| system | `D` | baseline total | **2+3 total** | won | operators | dense blocks | 3: dense total |
|---|---:|---:|---:|---:|---:|---:|---:|
| katsura-5 | 16 | 18.7 kB | **14.0 kB** | **1.33x** | 13.6 → 9.0 kB | 5.1 kB | 14.2 kB |
| katsura-6 | 32 | 80.2 kB | **57.9 kB** | **1.39x** | 60.1 → 37.7 kB | 20.1 kB | 59.1 kB |
| katsura-7 | 64 | 344.8 kB | **243.8 kB** | **1.41x** | 264.5 → 163.6 kB | 80.2 kB | 252.2 kB |
| cyclic-5 | 70 | 136.4 kB | 136.4 kB | 1.00x | 40.4 kB | 96.0 kB | 214.6 kB |
| cyclic-6 | 156 | 698.6 kB | 698.6 kB | 1.00x | 222.7 kB | 475.9 kB | 1,185.2 kB |
| planted-6 | 64 | 94.5 kB | 94.5 kB | 1.00x | 14.2 kB | 80.2 kB | 209.2 kB |
| planted-8 | 256 | 1,357.0 kB | 1,357.0 kB | 1.00x | 76.0 kB | 1,281.0 kB | 3,889.0 kB |
| planted-10 | 1,024 | 20,864.0 kB | 20,864.0 kB | 1.00x | 380.0 kB | 20,484.0 kB | 71,924.0 kB |

**The recommended configuration is faster than M17's on every system in the corpus and never
stores more.** It is not the fastest *possible* configuration everywhere, and that is deliberate:
on katsura-7 an unbounded batch takes 2.38 ms against 2.73 — 13% — and the same configuration takes
60.47 ms on planted-10 where M17's takes 41.49. Giving up 13% of katsura's 14x to avoid a 1.46x
loss elsewhere is the trade §6.4 described, now made as a default.

### 9.2 Nothing composed adversely, and that was not obvious in advance

`2+3` equals `2-batch64` in time to within the noise of the harness and equals `3-adaptive` in
bytes exactly, on every instance. The reason is that the two changes touch disjoint quantities —
how a column's normal form is *computed* against how the result is *stored* — and the one place
they could have met is the coordinate assembly that writes a reduced column into its
representation. §9.4's stage table says that assembly is 2% to 14% of a conversion, so a change to
it does not survive to the total.

The interaction that was predicted to be adverse was M18-1 against M18-2, and it is not visible
because it is not an interaction: `BatchedBorder` *is* deduplicated — a batch's targets are the
distinct border monomials — so `1+3` and `2+3` are two points on one axis rather than two options
that could conflict. The ablation prints both anyway, since "the two cannot conflict" is an
argument and the table is a measurement.

One figure deserves a caveat rather than a claim. Storage alone, on the baseline construction,
moves katsura-7's whole conversion by a few percent with **no stable sign**: this ablation reports
0.92x to 0.98x across three runs, `examples/fglm_storage.rs` reports 0.99x in the same session, and
Criterion's §7.3 figure was 0.1%. The honest statement is that a per-column representation is not
detectable at the level of a whole conversion, which is what §7.3 concluded from the application
benchmark and what makes 1.41x less operator memory worth taking.

### 9.3 The defaults, chosen from the table above

`FglmOptions::recommended()` — and therefore `FglmOptions::default()` — is now
`OperatorConstruction::BatchedBorder` with `BorderBatch::recommended()`'s batch of 64, and
`OperatorStorage::Adaptive`. The two enums' `#[default]` variants moved with it, so
`OperatorConstruction::default()` and `FglmOptions::default().operator_construction` cannot drift
apart.

What did **not** change:

* `FglmOptions::baseline()` still names M17's strategies explicitly, which is why every figure in
  this document quoted against the baseline still means what it said.
* `FglmOptions::unbounded()` still carries the *reference* strategies, not the recommended ones, so
  a measurement that lifts the budgets does not silently also change the strategy. That is now
  documented on the constructor rather than being an accident of its definition.
* Every limit. The baseline and the recommended configuration differ in their strategies and in
  nothing else, which `options.rs` asserts directly — otherwise a speedup measured against the
  baseline could be a budget that fired rather than a strategy that worked.

### 9.4 Where the time goes now

`cargo run --release --example fglm_profile` under each configuration — the example takes a
`baseline` argument for the M17 strategies and profiles the shipped ones otherwise. Stage shares of
the whole conversion, `measure_stages` on:

| system | M17 total | M17 border % | M17 walk | **now** | border % | walk | **walk %** |
|---|---:|---:|---:|---:|---:|---:|---:|
| katsura-5 | 0.53 ms | 80% | 0.05 | **0.14 ms** | 43% | 0.04 | 29% |
| katsura-6 | 3.54 ms | 90% | 0.16 | **0.54 ms** | 46% | 0.16 | 30% |
| katsura-7 | 38.32 ms | 95% | 0.90 | **2.79 ms** | 52% | 0.86 | 31% |
| cyclic-5 | 1.91 ms | 83% | 0.18 | **0.56 ms** | 39% | 0.21 | 38% |
| cyclic-6 | 25.04 ms | 92% | 1.16 | **2.78 ms** | 37% | 1.27 | 46% |
| planted-6 | 0.44 ms | 48% | 0.12 | **0.40 ms** | 38% | 0.13 | 33% |
| planted-8 | 3.24 ms | 47% | 1.16 | **2.88 ms** | 31% | 1.40 | 49% |
| planted-10 | 41.38 ms | 26% | 24.83 | **36.89 ms** | 15% | 25.58 | **69%** |

"Border share" is scalar reduction plus batched closure against the total — the same stage of the
algorithm under two strategies, which is why the profile now prints both columns and takes their
sum. A profile that reported only `normal_forms` would say that 0% of a batched conversion went
into reducing the border.

**The bottleneck moved.** M18 opened with operator construction at 95% of katsura-7's conversion
and §3.4 saying nothing else was worth attacking. It is now 52%, the walk is 31%, and the absolute
figure is 1.44 ms where it was 36.60. On planted-10 the walk was already 60% and is now 69%: the
border work there fell from 10.96 ms to 5.58 while the walk did not move, because nothing in M18
touched it. §8.6 and §8.7 did, after the milestone: planted-10's walk is 10.25 ms and 60% of its
conversion.

Storage says the same thing more sharply. Under the shipped configuration the dependence test's
three dense blocks against the operators' bytes: 0.5x on katsura-7, 2.1x on cyclic-6, 16.9x on
planted-8 and **53.9x on planted-10**, where the blocks are 20.5 MB and the operators 380 kB. The
operators were the whole of M18's storage work and on the systems that scale they are now a
rounding error. §8.6 took planted-10's blocks to 16.4 MB and 43.1x, which does not change that
reading.

### 9.5 What the suite says

* `cargo test`: **963 passed, 0 failed, 9 ignored.** `cargo test --release`: the same.
  `cargo test --doc`: 13 passed, which includes every fenced Rust block in the README.
* The slow `#[ignore]`d comparisons, release, named individually as CI names them —
  `test_optimized_agrees_with_reference_on_slow_systems`, `test_f4_on_larger_systems`, and the live
  Singular sweep: **3 passed in 124 s.**
* The committed differential corpus went from 96 cases to **240**, at a wider generated shape
  (degree ≤ 4, terms ≤ 5 where it was 3 and 4): 120 zero-dimensional ideals with a border, 55 unit
  ideals, 65 positive-dimensional, ten cases per (characteristic, variable count) across six fields
  and two to five variables, the largest quotient `D = 57`. Every one is verified under all
  **nine** construction × storage configurations, each against Singular rather than against another
  configuration. The shape-position route runs and agrees on 76 of the 120.
* The generated fixture module's header now reproduces the sweep that produced it, flag for flag.
  It previously quoted the tool's *defaults*, which regenerate a different table — a fixture corpus
  nobody can reproduce is data of unknown provenance.
* The 29 Singular reference bases are now compared under all nine configurations too. They used to
  run only `fglm_to_lex`, so when the default changed they would have quietly stopped covering the
  other eight.
* Two live sweeps of **1,000 systems each** under the new defaults, seeds 31337 and 90210, over
  GF(2) through GF(2^31 - 1) in two to five variables: 949 zero-dimensional, 572 unit ideals, 479
  positive-dimensional, **0 disagreements and 0 oracle failures**.
* Every optimization has an independent benchmark: `fglm_operator_construction` for M18-1 and
  M18-2, `fglm_operator_application` for M18-3, `fglm_dependence` for M18-4, and `fglm_recommended`
  for the combination. M18-4's is a level rather than a comparison — the triangular block is not
  option-gated and the padded one no longer exists — so what it does is keep the quantity under
  measurement: filling a span to full rank is 444 µs at `D = 64`, 5.99 ms at 156 and 26.4 ms at
  256 — the `O(D^3)` the walk's cost is — and sixteen dependent probes against a full-rank span are
  227 µs, 1.38 ms and 3.62 ms.

### 9.6 Regressions, stated

* **An unbounded batch is 1.46x slower than M17 on planted-10** (60.47 ms against 41.49) and 1.38x
  slower on planted-8. It is not the default, it is documented as the wrong choice on a sparse
  staircase, and it is kept because it is the fastest size on katsura and because a bound chosen
  without knowing what it costs would be a guess.
* **Dense storage everywhere is 0.56x on planted-10 and 3.4x its memory** — 71.9 MB against 20.9.
  It exists to show that, which §7.2 argued and this table confirms at the level of a whole
  conversion.
* **Storage alone is a few percent either way on katsura**, with no stable sign across harnesses or
  runs. §9.2 has the three measurements that disagree about it.
* **The debug test suite went from 10 s to 41 s**, because the fixture table quadrupled and every
  case is verified nine times. The release suite is 2.6 s. Both are well inside what CI tolerates,
  and the alternative — verifying 240 cases under one configuration — is the weaker check.
* **Peak memory during construction is unchanged and still up to twice the budget** under the
  deduplicated and batched strategies, which now includes the default. §5.4 proves the bound rather
  than measuring it; making the default faster did not make that cost go away, and a caller for
  whom it matters has `OperatorConstruction::PerColumn`.

### 9.7 The next milestone, from the measurements above

**The dependence test is now the whole of the remaining problem on the systems that scale, in both
time and memory.** The evidence is §9.4: on planted-10 the lex walk is 69% of a conversion and the
three dense blocks are 20.5 MB against the operators' 380 kB. The walk's row operations are
`O(D^3)` and its storage was `2 D^2 + D (D + 1) / 2` cells, so at `D = 2,828` the default
`max_span_entries` of 20 million bound — and that is the limit M18 did not move. §8.6 took the
storage to `D^2 + D (D + 1)` and the crossing to `D = 3,162`: a fifth off the storage and 12% on
the reachable dimension, not an order of magnitude, so the recommendations below stand.

Three things are worth doing, in this order:

1. **Stop retaining the accepted quotient vectors, or store them as the operators are stored.**
   They are `D^2` of the `2 D^2 + D` cells — half of them, after §8.6 — and M17 added them to make
   a candidate's class cost one operator application instead of a reduction. That trade was never
   measured against recomputing them, and M18-3's per-column accounting is exactly the machinery
   for measuring it.
2. **Put the span's row operations through `linalg`.** The dependence test is a hand-written dense
   echelon update over `Vec<F>`, and it uses none of the elimination machinery M16 built — neither
   the backends nor `reduce_rows_against_pivots_with`. The reduction is one scaled subtraction per
   accepted row, so the question is whether that machinery beats it at `D` in the hundreds, and
   that is a benchmark rather than an argument: `fglm_dependence` is already the benchmark. §8.7
   took the *bookkeeping* from `linalg`'s `DenseAccumulator` and found that one of its three
   devices does not transfer, which is evidence about this recommendation and not against it: what
   transfers has to be measured one piece at a time.
3. **Reuse closures across batches.** katsura-7's remaining 52% is the batch closure, and a closure
   is currently discarded at the end of its batch. Border monomials are processed in descending
   order, so consecutive batches' closures overlap heavily; §6.4 measured what a *bigger* batch is
   worth and never measured what a *shared* one would be.

What is explicitly **not** recommended is a sparse-FGLM milestone. §8.5 is the no-go and the
measurement behind it has not changed: the systems whose memory is the problem are exactly the
systems the shape-position route cannot convert. If a workload with large shape-position quotients
appears, `fglm::shape` is the foundation and the first thing to do is measure whether the
algebraic-hash systems that motivate this project are in shape position at all.

---

## 10. Acceptance criteria

### M18-0 — validation infrastructure

- [x] Reproducible M17 baseline captured — §3.2, remeasured after instrumentation.
- [x] Singular differential harness implemented — §4.
- [x] Variable-order and field conventions verified — §4.2.
- [x] Randomized tests over multiple small prime fields — §4.4, six characteristics including 2
      and 3.
- [x] Failing cases can be persisted and reproduced — §4.5, §4.6.
- [x] Representative fixtures committed — §4.7, 96 cases, expanded to 240 in M18-5 (§9.5).
- [x] Ordinary CI does not require Singular — §4.7.

### M18-1 — border deduplication

- [x] Unique border monomials enumerated correctly — `BorderIndex`, §5.1, with its own tests.
- [x] Repeated border products deduplicated — `OperatorConstruction::DeduplicatedBorder`.
- [x] Normal forms agree with M17 — §5.5, and every fixture under both strategies.
- [x] Operator columns agree exactly — whole-`QuotientAlgebra` equality, §5.5.
- [x] Performance and duplication rate measured — §5.2, and the two refuted hypotheses in §5.3.

### M18-2 — batched reduction

- [x] Symbolic closure invariant tested — directly, not inferred, §6.6.
- [x] Fixed reducer pivots implemented correctly — one row per reducible monomial, §6.2.
- [x] Independent target normal forms preserved — and asserted as an observable property: a
      target's answer is the same alone, beside the whole border, and in reverse order, §6.6.
- [x] Batched results equal scalar results — at every batch size the proposal names, §6.6.
- [x] Matrix and resource limits enforced — checked as the closure grows, §6.5.
- [x] Batch-size performance measured — §6.4, and it decides the recommended size.
- [x] Appropriate fallback strategy retained — `BatchOverflow`, and neither option drops a
      target, §6.5.

### M18-3 — operator storage

- [x] Standard, sparse, and dense columns supported — `Column`, §7.1.
- [x] Adaptive selection supported where justified — per column, from bytes, §7.1.
- [x] All representations agree exactly — §7.5, including the cross product with M18-1.
- [x] Operator application benchmarked separately — §7.3, on unit and dense inputs.
- [x] Byte-aware accounting introduced — `operator_cells` and exact `operator_bytes`, §7.4.
- [x] Resource limits apply across representations — `max_operator_bytes` beside the entry
      budget, §7.4.

### M18-4 — FGLM scalability

- [x] Actual incremental-span storage measured — `IncrementalSpan::stored_cells`, §8.1, and
      benchmarked in M18-5's `fglm_dependence` group, §9.5.
- [x] All substantial coordinate-vector storage accounted for — all three blocks, and
      `max_span_entries` now budgets them, §8.2.
- [x] Compact dependence representation evaluated — implemented, not merely evaluated: the
      combination block is triangular, §8.1.
- [x] Dependence coefficients remain exact — over the *original* accepted vectors, tested on a
      Vandermonde basis, §8.1.
- [x] Shape-position detection evaluated — `fglm::shape`, algebraic rather than from a solution
      count, §8.3.
- [x] Sparse-FGLM spike documented with go/no-go criteria — **no-go**, §8.5.
- [x] No unverified probabilistic result is exposed as certified output — nothing in the prototype
      is probabilistic, and its output is verified before it is returned, §8.4.

### M18-5 — integration

- [x] All default tests pass — 963 passed, 9 ignored, §9.5.
- [x] Release-mode tests pass — the same suite and the 13 doc tests, §9.5.
- [x] Slow Gröbner and FGLM reference comparisons pass — the three `#[ignore]`d comparisons in
      release, and the 29 Singular reference bases now under all nine configurations, §9.5.
- [x] Expanded Singular fixtures agree — 96 cases to **240** at a wider shape, each against
      Singular under nine configurations, §9.5.
- [x] Every optimization has an independent benchmark — four Criterion groups, one per
      sub-milestone, plus `fglm_recommended` for the combination, §9.5.
- [x] Combined performance and memory usage measured — §9.1, with
      `examples/fglm_ablation.rs` as the harness.
- [x] Any regressions documented — §9.6, including the two rejected strategies and the figure
      whose sign is not stable.
- [x] Default strategies selected from evidence — §9.3, from §9.1's table rather than from
      katsura-7 alone.
- [x] README and milestone documentation updated — the defaults, the fixture count, the new
      example, and the benchmark groups.
- [x] Next-milestone recommendation based on measured bottlenecks — §9.7: the dependence test, with
      three ordered proposals and one explicit non-recommendation.

---

## 11. Compatibility

`FglmOptions` gained `measure_stages` and `FglmStatistics` gained `border`, `timings` and `memory`.
Both structs have public fields, so a downstream struct literal naming every field stops compiling.
Constructing from `recommended()`, `unbounded()` or `Default` and assigning what matters survives a
new field, which is what this crate's own callers do and what the documentation now says to do.

`FglmStatistics::estimated_bytes` changed meaning. It was `operator_entries * 16 + 2 * D^2 * 8`;
it is now the operators' own reported bytes plus **three** dense blocks. The old figure undercounted
in two directions — the operators have a per-column spine and spare `Vec` capacity, and the accepted
quotient vectors were missing entirely. No resource budget changed.

`QuotientAlgebra::new_with_statistics` is new; `new` delegates to it and is unchanged.

M18-1 added `FglmOptions::operator_construction`, the same source-compatibility note applying. It
also added `FglmOptions::baseline()` and `FglmOptions::with_operator_construction`, and the public
`BorderIndex` and `ColumnTarget`. `FglmOptions::default()` was unchanged then and changed in M18-5
— see below.

M18-2 added `OperatorConstruction::BatchedBorder`, `FglmOptions::border_batch` and
`FglmOptions::with_border_batch`, the public `BorderBatch`, `BorderBatchSize`, `BatchOverflow` and
`BorderBatchStatistics`, the `FglmError::BorderBatchExceeded` variant, `FglmStatistics::batches`,
and `FglmStageTimings::border_symbolic`. The same note about exhaustive `match` on `FglmError`
applies.

M18-4 changed what `FglmOptions::max_span_entries` counts — see §8.2 — and added
`IncrementalSpan::stored_cells` and `cells_at_full_rank`, and the `fglm::shape` module. The
`Dependence` variants' `combination` and `coefficients` now have one entry per *accepted vector*
rather than per dimension, which is a behaviour change for a downstream caller using
`IncrementalSpan` directly; the conversion is the only caller in this crate.

**M18-5 changed `FglmOptions::default()`**, which is the one behaviour change in this milestone a
caller can observe without asking for it. `recommended()` and therefore `Default` now name
`OperatorConstruction::BatchedBorder` and `OperatorStorage::Adaptive`, and the two enums'
`#[default]` variants moved to match. Every strategy produces the same lex basis — that is what the
nine-configuration tests are for — so what changes is time, memory, and which counters in
`FglmStatistics` are nonzero:

* `FglmStageTimings::normal_forms` is **zero** under the new default and
  `FglmStageTimings::border_symbolic` is not. They are the same stage of the algorithm under two
  strategies, so a caller reporting a reduction share must add them; `examples/fglm_profile.rs`
  does, and §9.4 says what that share now is.
* `FglmStatistics::batches` is nonzero where it used to be zeros.
* `FglmMemory::operator_cells` now exceeds `operator_entries` wherever a column is held densely,
  and `dense_columns` is nonzero on katsura. `operator_entries` itself is unchanged under every
  strategy, which the tests assert.
* `FglmOptions::baseline()` is the M17 configuration and is the way to get the old behaviour
  exactly. `FglmOptions::unbounded()` also still carries the reference strategies.

`emit_fixture_module` took a third argument, the flags that reproduce the sweep, so that a
generated fixture module's header names the sweep that produced it rather than the tool's defaults.
`examples/fglm_profile.rs` takes a `baseline` argument and otherwise profiles the shipped
strategies; its stage table gained a `symbolic` column for the reason above.

M18-3 added `FglmOptions::operator_storage` and `FglmOptions::max_operator_bytes`, the public
`OperatorStorage` and `FglmOptions::with_operator_storage`, the `FglmError::OperatorBytesExceeded`
variant, `FglmMemory::operator_cells` and `FglmMemory::dense_columns`, and
`MultiplicationOperator::stored_cells` and `dense_columns`. **`FglmError` is a public enum**, so a
downstream exhaustive `match` on it stops compiling when a variant is added; the type has carried
that property since M17 and its documentation says variants are added as the implementation becomes
able to produce them. No existing variant changed meaning, and `FglmOptions::default()` is
unchanged — see §7.6.

---

## 12. References

1. Faugère, J.-C., Gianni, P., Lazard, D., Mora, T. (1993). *Efficient Computation of
   Zero-dimensional Gröbner Bases by Change of Ordering.* J. Symbolic Computation 16(4), 329–344.
2. Faugère, J.-C., Mou, C. (2017). *Sparse FGLM algorithms.* J. Symbolic Computation 80, 538–569.
3. Singular manual: `std`, `reduce`, `vdim`, `kbase`, `fglm`, `option(redSB)`.
4. *An Algorithm for Splitting Polynomial Systems Based on F4*, PASCO 2017.
5. `docs/MILESTONE-FGLM-SOLVING.md` — M17.
6. `docs/MILESTONE-F4-OPTIMIZATION.md` — M16.
