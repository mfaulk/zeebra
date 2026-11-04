# Milestone: Quotient-Algebra and FGLM Scalability

**Status:** in progress — M18-0, M18-1, M18-3 and M18-4 complete
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
| M18-2 | batched border reduction | not started |
| M18-3 | adaptive sparse/dense multiplication operators | **complete** |
| M18-4 | incremental-span memory, and a sparse-FGLM feasibility spike | **complete** |
| M18-5 | integration, ablations, and this document's conclusion | not started |

M18-3 and M18-4 are independent of M18-1 and M18-2 and of each other. All four depend on M18-0,
because none of them may be merged without evidence that it changed no answer.

**M18-1's result:** katsura-7's conversion from **39.0 ms to 27.7 ms**, cyclic-6's from 27.8 ms to
19.3 ms, nothing regressed, and no answer changed. §5.

**M18-3's result:** katsura-7's operators from **264.5 kB to 163.6 kB** and planted-10's from
640.0 kB to **380.0 kB**, by two unrelated changes — an adaptive per-column representation and an
exact one. §6.

**M18-4's result:** the dependence test's dense blocks 1.20x smaller, and a **no-go** on a full
sparse-FGLM milestone. The decisive measurement: the systems where classical FGLM's memory is the
problem are exactly the systems the shape-position route cannot convert. §7.

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
what the baseline was, not of what the code does now. §6.1 has the before and after.

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

96 cases are committed. An ordinary test replays **the same comparison function** against them,
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
* **All 96 committed differential fixtures are verified under every strategy**, which is each one
  separately compared against Singular rather than against the other. Two implementations agreeing
  with each other and both being wrong is what an external oracle is for.
* A live sweep of 500 random systems under `--operator-construction deduplicated-border`, over
  GF(2) through GF(2^31 - 1) in two to five variables: 0 disagreements, 0 oracle failures.
* `BorderIndex` has its own tests: every column classified exactly as `QuotientBasis::index_of`
  classifies its product, repeated border monomials carrying one index, the border distinct and
  descending under the order, the border disjoint from the basis, the index reproducible, and the
  unit ideal having no border at all.

### 5.6 The default has not changed

`FglmOptions::default()` is still `PerColumn`. Deduplication is measured faster on every instance in
the corpus, agrees everywhere, and stores the same amount — so this is sequencing, not doubt: §12 of
the proposal asks for defaults to be chosen from the integration ablation in M18-5, when M18-2's
batched reduction and M18-3's representations can be weighed against it at the same time. A caller
who wants it now writes

```rust
let options = FglmOptions::default()
    .with_operator_construction(OperatorConstruction::DeduplicatedBorder);
```

---

## 6. M18-3: adaptive operator storage

### 6.1 Two separate changes

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

### 6.2 What it is worth

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

### 6.3 What it costs

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

### 6.4 Byte-aware accounting and a second budget

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

### 6.5 Correctness

* Every representation gives the same columns, the same applications on unit, sparse, dense and
  zero inputs, and the same nonzero count. Asserted at the column level in `multiplication.rs` and
  over three orders, ten systems, katsura-5/6, cyclic-5 and planted-6 in `quotient_algebra.rs`.
  **Not** a `QuotientAlgebra` equality — the representations differ, so the values differ, and
  comparing them through what a caller can observe is the point.
* The lex basis is compared over the **cross product** of construction and storage, six
  configurations, because a construction strategy and a storage strategy could each be right alone
  and wrong together.
* All 96 differential fixtures are verified under all six configurations, each against Singular.
* `Adaptive` is asserted no larger than either extreme on every family, strictly smaller than
  `Sparse` on katsura-7, and exactly equal to `Sparse` on planted-8 — the last being the claim that
  it correctly declines to hold a 0.5%-full column densely.
* A zero column allocates nothing under both `Sparse` and `Adaptive`, which is §7.2's requirement
  for a compact zero representation; the sparse form already was one.

### 6.6 The default has not changed

`FglmOptions::default()` is still `OperatorStorage::Sparse`, for the same reason the construction
default is unchanged — see §5.6. The two representation changes in §6.1 are *not* behind a strategy
flag, because they are not strategies: they make the sparse representation smaller without changing
it.

---

## 7. M18-4: FGLM's memory, and the sparse-FGLM spike

Two deliverables with nothing in common except the quantity they are about. The first is an
optimization; the second is a research question with a verified prototype and a **no-go**.

### 7.1 The combination block is triangular

`IncrementalSpan` carries two blocks per echelon row: the row's `D` coordinates, and its expression
in terms of the accepted vectors. M17 padded the second to `D` as well.

It does not need to be. A row inserted when the accepted rank is `r` is a combination of the `r + 1`
vectors accepted up to and including the one that produced it — it **cannot** involve one accepted
afterwards, so coefficients beyond `r` are structurally zero. Summed over the rows:

| block | M17 | now |
|---|---:|---:|
| coordinates | `D^2` | `D^2` |
| combinations | `D^2` | `D (D + 1) / 2` |
| accepted vectors | `D^2`, uncounted | `D^2` |
| **total** | `3 D^2` | `2 D^2 + D (D + 1) / 2` |

A quarter off the span, exactly, with nothing traded: the padding was zeros. Measured:

| system | `D` | M17 dense blocks | now | won |
|---|---:|---:|---:|---:|
| katsura-7 | 64 | 96.0 kB | 80.2 kB | 1.20x |
| cyclic-6 | 156 | 570.4 kB | 475.9 kB | 1.20x |
| planted-8 | 256 | 1,536.0 kB | 1,281.0 kB | 1.20x |
| planted-10 | 1,024 | 24,576.0 kB | **20,484.0 kB** | 1.20x |

The coefficients a dependence reports must still be exact over the **original** accepted vectors —
§8.2 of the proposal calls that correctness-critical, and it is the thing a triangular block could
break. Tested on a Vandermonde basis, where there is no structure for an error to hide behind.

### 7.2 `max_span_entries` now counts all three blocks

It counted two of them and priced both as squares, so at `D = 16` it budgeted 512 cells where the
conversion allocates 648. **A budget cannot protect memory it does not know about**, and §8.1 of the
proposal asks for all substantial arrays to be recorded and budgeted — so the limit's meaning has
changed. Loudly: the option's documentation says so, the error's value changed in a test that
states the arithmetic, and `FglmMemory` reports each block separately so a figure quoted against the
old meaning can be recomputed. Checked arithmetic throughout, since a budget computed from a
wrapped product is no budget.

### 7.3 The sparse-FGLM spike: shape position

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

The whole katsura family, and nothing else. On the random differential corpus, **26 of the 38
zero-dimensional fixtures** are in shape position and the shape route agrees with Singular on every
one of them — that check runs in every sweep and on every fixture, not only in the module's own
tests.

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

**The shape route is slower, and the reason is instructive.** It does `D` span reductions where the
walk does about `D + |G|`, which is comparable — but the walk's vectors are the *classes of
monomials*, which are sparse early on, and `reduce` skips a row whose pivot column is zero in the
input. The powers of a single variable densify immediately, so the shape route pays close to the
full `D^3 / 2` where the walk pays much less. At `D = 64` that is 2.7x.

End to end it vanishes into a wash — 0.97x to 1.04x — because the operators are 90–96% of a
conversion on this family. Which is the same observation §3.4 made, from the other side.

### 7.4 Verification, and why it is not `normal_form`

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

### 7.5 The deliverable: no-go, and why

§8.6 of the proposal asks six questions.

**1. Which benchmark systems meet the shape-position criterion?** The katsura family at every size,
and nothing else in the corpus. 68% of the random differential fixtures.

**2. How much work would a specialized converter save?** On time, none: it is 2.7x *slower* on the
route at `D = 64` and a wash end to end. On memory, 1.65x fewer dense cells.

**3. Can it recover the complete ideal, including multiplicities?** Yes, exactly and deterministically
— it produces the reduced lex basis, which determines the ideal. Nonradical ideals in shape position
convert correctly; nonradical ideals that are not are rejected rather than radicalized.

**4. What verification would make a probabilistic approach safe to expose?** The one in §7.4, which
is complete and costs `O(N D)` operator applications. A Wiedemann variant choosing a random linear
form or a random separating element could reuse it unchanged, so such a variant could be exposed as
certified rather than conjectural. This is the one unambiguously reusable result of the spike.

**5. What memory limits would remain?** The echelon form, `D^2 + D (D + 1) / 2` cells. The shape
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

---

## 8. Acceptance criteria

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

- [x] Unique border monomials enumerated correctly — `BorderIndex`, §5.1, with its own tests.
- [x] Repeated border products deduplicated — `OperatorConstruction::DeduplicatedBorder`.
- [x] Normal forms agree with M17 — §5.5, and all 96 fixtures under both strategies.
- [x] Operator columns agree exactly — whole-`QuotientAlgebra` equality, §5.5.
- [x] Performance and duplication rate measured — §5.2, and the two refuted hypotheses in §5.3.

### M18-2 — batched reduction

- [ ] Symbolic closure invariant tested.
- [ ] Fixed reducer pivots implemented correctly.
- [ ] Independent target normal forms preserved.
- [ ] Batched results equal scalar results.
- [ ] Matrix and resource limits enforced.
- [ ] Batch-size performance measured.
- [ ] Appropriate fallback strategy retained.

### M18-3 — operator storage

- [x] Standard, sparse, and dense columns supported — `Column`, §6.1.
- [x] Adaptive selection supported where justified — per column, from bytes, §6.2.
- [x] All representations agree exactly — §6.5, including the cross product with M18-1.
- [x] Operator application benchmarked separately — §6.3, on unit and dense inputs.
- [x] Byte-aware accounting introduced — `operator_cells` and exact `operator_bytes`, §6.4.
- [x] Resource limits apply across representations — `max_operator_bytes` beside the entry
      budget, §6.4.

### M18-4 — FGLM scalability

- [x] Actual incremental-span storage measured — `IncrementalSpan::stored_cells`, §7.1.
- [x] All substantial coordinate-vector storage accounted for — all three blocks, and
      `max_span_entries` now budgets them, §7.2.
- [x] Compact dependence representation evaluated — implemented, not merely evaluated: the
      combination block is triangular, §7.1.
- [x] Dependence coefficients remain exact — over the *original* accepted vectors, tested on a
      Vandermonde basis, §7.1.
- [x] Shape-position detection evaluated — `fglm::shape`, algebraic rather than from a solution
      count, §7.3.
- [x] Sparse-FGLM spike documented with go/no-go criteria — **no-go**, §7.5.
- [x] No unverified probabilistic result is exposed as certified output — nothing in the prototype
      is probabilistic, and its output is verified before it is returned, §7.4.

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

## 9. Compatibility

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
`BorderIndex` and `ColumnTarget`. `FglmOptions::default()` is unchanged — see §5.6.

M18-4 changed what `FglmOptions::max_span_entries` counts — see §7.2 — and added
`IncrementalSpan::stored_cells` and `cells_at_full_rank`, and the `fglm::shape` module. The
`Dependence` variants' `combination` and `coefficients` now have one entry per *accepted vector*
rather than per dimension, which is a behaviour change for a downstream caller using
`IncrementalSpan` directly; the conversion is the only caller in this crate.

M18-3 added `FglmOptions::operator_storage` and `FglmOptions::max_operator_bytes`, the public
`OperatorStorage` and `FglmOptions::with_operator_storage`, the `FglmError::OperatorBytesExceeded`
variant, `FglmMemory::operator_cells` and `FglmMemory::dense_columns`, and
`MultiplicationOperator::stored_cells` and `dense_columns`. **`FglmError` is a public enum**, so a
downstream exhaustive `match` on it stops compiling when a variant is added; the type has carried
that property since M17 and its documentation says variants are added as the implementation becomes
able to produce them. No existing variant changed meaning, and `FglmOptions::default()` is
unchanged — see §6.6.

---

## 10. References

1. Faugère, J.-C., Gianni, P., Lazard, D., Mora, T. (1993). *Efficient Computation of
   Zero-dimensional Gröbner Bases by Change of Ordering.* J. Symbolic Computation 16(4), 329–344.
2. Faugère, J.-C., Mou, C. (2017). *Sparse FGLM algorithms.* J. Symbolic Computation 80, 538–569.
3. Singular manual: `std`, `reduce`, `vdim`, `kbase`, `fglm`, `option(redSB)`.
4. *An Algorithm for Splitting Polynomial Systems Based on F4*, PASCO 2017.
5. `docs/MILESTONE-FGLM-SOLVING.md` — M17.
6. `docs/MILESTONE-F4-OPTIMIZATION.md` — M16.
