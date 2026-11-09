# Classical benchmarks: the invariants are externally anchored, the timings are not

**Measured at:** publication bound `f94b3df0` for Zeebra's own figures in §5; every external timing
is quoted from its source — §2.1 and §2.2 from Steel's 2004 page, §2.3 from Magma's V2.27 topic page
([the protocol's §10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).
**§10's `GF(2)` values are invariants rather than timings** — Krull dimensions, quotient dimensions
and basis sizes, none of which depends on the machine or the clock — measured at `590eee15` across
Zeebra, msolve 0.11.0, Singular, Groebner.jl and Sagebrush. §10 publishes **no** wall-clock figure,
which §4 forbids against the 2004 column and §7 reaffirms.

Deliverable for A7 (#199), a child of the benchmark-corpus epic #65. The question: do Zeebra's three
synthetic generators — `cyclic`, `katsura`, `planted` — have external reference points, and if so
what may honestly be compared against them?

**The answer is split, and the split is the result.** The *invariants* of two of the three families
match published values exactly, which is a real anchor and a stronger one than a stopwatch. The
*timings* on the one page that publishes them are not comparable to Zeebra's, for three independent
reasons. §5 states the correction this forces on #65, including on a claim I made there myself.

> **Updated after #424.** Two of this document's recommendations have since been carried out and the
> text says so where they were made. The invariants are now **asserted** rather than reported
> (`corpus::CorpusEntry::quotient_dimension`, §6), and the ladder reaches Steel's three Katsura rows
> and `cyclic-7` — so "the rows that match are out of reach" in §4 is now true of the Cyclic rows
> only. **§4's prohibition on comparing wall clocks against the 2004 figures is untouched and
> stands.** What reaching those rungs bought is an instance list and a set of checkable invariants,
> not a comparison.

## 1. What #65 says, and how far it is wrong

#65's motivation:

> Zeebra's benchmark corpus is synthetic… they share a weakness: **nobody outside this repository has
> published a result on any of them.** There is no external number to be right or wrong against.

This document was opened because that looked false. Allan Steel's Magma Gröbner-basis timings page
(<http://magma.maths.usyd.edu.au/users/allan/gb/>) publishes Cyclic-`n` and Katsura-`n` timings
across five implementations, so there *are* external numbers.

Having read the page in place and measured Zeebra's own invariants, **#65's premise is substantially
right in practice and wrong only in letter.** External numbers exist for these families. Almost none
of them is a number Zeebra can be right or wrong against. What *is* usable turns out to be a
different kind of datum entirely.

## 2. The external source, read in place

`curl`, not a summary — #198 records that two `WebFetch` retrievals of this same page disagreed on a
memory figure, and the conclusion there was that the page must be read directly. Read 2026-11-06.

Provenance, verbatim from the page: timings "gathered in May and August 2004", on an **AMD Athlon XP
2800+ PC (2.087 GHz)**, L1 64K, D 64K, L2 512K, **1.5 GB main memory**, Redhat Linux 9.0 (kernel
2.4.20-8), with noted exceptions on a 750 MHz Sunfire v880 for the runs needing more memory. Software:
Magma V2.11-8 (F4), V2.11-1 (F4), V2.10 (Buchberger), Singular 2-0-5 (Buchberger), Macaulay 2 0.9.2
(Buchberger). "Last updated: October 22, 2004."

And one line that matters more than any timing:

> All Gröbner bases are computed with respect to the **grevlex** (graded reverse lexicographical)
> order

which is Zeebra's default order, so the formulation is at least nominally comparable.

### 2.1 GF(32003), the field closest to Zeebra's small primes

| | Magma 2.11-8 | Magma 2.11-1 | Magma 2.10 | Singular 2-0-5 | Macaulay 2 0.9.2 |
|---|---:|---:|---:|---:|---:|
| Katsura 8 | 0.3 | 0.6 | 9.3 | 2.4 | 11.8 |
| Katsura 9 | 1.7 | 5.8 | 100.9 | 22.5 | 123.9 |
| Katsura 10 | 13.1 | 51.8 | 1259.3 | 186.2 | 1347.1 |
| Cyclic 7 (Hom) | 0.4 | 0.5 | 13.7 | 3.7 | 12.3 |
| Cyclic 8 (Hom) | 10.4 | 24.7 | 628.4 | 132.8 | 643.9 |
| Cyclic 9 | 1453.6 | 5177.9 | >>3 days | 38298.8 | ? |
| Cyclic 10 | 17.6 days* | | | | |

`*` verbatim: "the computation was done in 17.6 days in August 2004 on a 750MHz Sunfire v880. Only one
sequential processor was used, and 30.7GB of memory was needed. The ideal is zero-dimensional, and
the quotient of the polynomial ring by the ideal has **dimension 34940** as a vector space. The
largest step took 6.4 days and involved partially triangularizing a **544684 by 582742** matrix with
**density 1.3%**."

### 2.2 GF(2) — relevant to #196 and #218

| | Magma 2.11-8 | Magma 2.11-1 | Magma 2.10 | Singular 2-0-5 |
|---|---:|---:|---:|---:|
| Cyclic 8 | 1.0 | 1.4 | 141.8 | 10.3 |
| Cyclic 9 | 222.6 | 341.4 | ? | 15673.3 |
| Cyclic 10 | 12.3 hours* | | | |

`*` "12.3 hours on a 750MHz Sunfire v880, using 9.3GB of memory. The ideal has dimension 4."

**Read that last phrase carefully.** Over GF(32003) the page says "The ideal is zero-dimensional, and
the quotient … has dimension 34940 **as a vector space**"; over GF(2) it says only "The ideal has
dimension **4**". Those are different quantities — the second is a Krull dimension, i.e. Cyclic-10
mod 2 is **positive-dimensional**. Conflating the two would turn a statement about geometry into a
wrong solution count, so the distinction is recorded rather than normalized away.

The page's HFE rows are A6's and are reported in #198, not here. The rationals rows are out of scope
— Zeebra has no rational arithmetic and this document does not propose adding any.

### 2.3 The subscriber-side topic page, which is twenty-two years newer

`https://magma.maths.usyd.edu.au/magma/info/topic_gb` returns **HTTP 401** to this machine and still
does; it is behind Magma's subscriber login, which is why #430 was filed as an owner action. The
owner supplied it as a PDF on **2026-11-08**: sha256
`39b69365d58dc0e71fd54f5218941433af6a89638f4f883bedd891005f240886`, 115 897 B, 3 pp., printed from
the live page. It is Magma's own copyrighted page — quoted here, not committed.

**#430's first question is answered, and the answer is better than expected: it carries maintained
timings, not just documentation.** The machine line, verbatim:

> All the timings given below are for runs on a 64-bit Dell workstation with a 4-core Intel Core
> i7-7700 CPU (3.60 GHz); timings are given for runs in both the default single core case and the
> parallel 4-core case.

An i7-7700 is a 2017 part and the figures are Magma **V2.27**, against §2's Athlon XP and V2.11-8
from 2004. Every figure is given twice, 1 core and 4:

| system | field | 1 core | 4 cores | 4-core speedup | memory |
|---|---|---:|---:|---:|---:|
| Cyclic-9 | GF(32003) | 29.3 s | 10.2 s | 2.87x | — |
| Cyclic-10 | GF(32003) | 1 957.1 s | 601.2 s | 3.26x | — |
| Cyclic-9 | `ℚ` | 286.1 s | 144.3 s | 1.98x | 750 MB |
| Cyclic-10 | `ℚ` | 16.1 h | 5.2 h | 3.10x | 46 GB |
| HFE Challenge 1 (80 quadratics, 80 variables) | GF(2) | 85.1 s | 28.2 s | 3.02x | — |

**What is and is not usable here.** There are **no Katsura rows**, no per-version columns, no
repetition count, no memory figures for the finite-field rows, no input files and no build
description beyond the CPU — so §4's three reasons still forbid a timing comparison, and this page
does not change the verdict of §4 or §7 for Zeebra's own numbers. What it does change is the *era*
of the only Magma anchor on record: Cyclic-9 over GF(32003) went from 1 453.6 s on a 2.087 GHz
Athlon under V2.11-8 to **29.3 s on one core** under V2.27, a factor of 49.6 that is twenty-two
years, two machines and sixteen versions wide and is attributable to none of them individually.

**Two things on it are worth more than the timings.** The first is the parallel pair: Magma's F4
gets **2.9x–3.3x from four cores** on the finite-field rows, and 2.0x on Cyclic-9 over `ℚ`. That is
a published scaling figure for a competitor's F4 at a worker count Zeebra measures itself at, and it
is the kind of quantity #412 and `resultant-elimination.md` §6.6 are about. The second is the dense
variant, which the page dates and scopes:

> A major new variant of the F4 algorithm was developed by A. Steel in 2013 and is applicable to
> polynomial systems with rather dense inputs; this is a common case for attacking certain types of
> cryptosystem and includes the HFE and MQQ cryptosystems and also Minrank systems.

That is the "dense F4" of `minrank.md` §5.4 named and dated by its vendor, and it is #441's subject.
The page also gives the HFE-80 matrix shape — "the largest matrix is 293,287×1,666,981 and many rows
have hundreds of thousands of non-zero entries" — which is a structural datum of the kind #225 and
#218 want, on the system #198 tracks.

**#430's other two questions are owner decisions, and are now answered.**

- **Magma is not available as a comparand.** The owner has no Magma access (2026-11-08). So no
  adapter can be written, `tools/external/provision.sh` is unaffected, and every Magma figure in
  this repository stays what it already is: read at source and quoted, never measured here. #441 and
  #439 are documentary studies for the same reason.
- **Macaulay 2 is not a priority** (owner, 2026-11-08). The roster stays the four provisioned
  engines — Singular, msolve, Groebner.jl, Sagebrush. §2.1's Macaulay 2 0.9.2 column is a
  Buchberger-era 2004 figure and nothing here depends on refreshing it.

## 3. Zeebra's invariants, measured

`cargo run --release --example fglm_baseline`, over GF(2^31 − 1), `F4Options::default()`. No new code:
this example already classifies each system from the leading monomials of its grevlex basis and
reports `D = dim_F(R/I)`.

| system | vars | ideal | `D` | grevlex ms |
|---|---:|---|---:|---:|
| cyclic-3 | 3 | zero-dim | 6 | 0.01 |
| cyclic-4 | 4 | **positive** | — | 0.06 |
| cyclic-5 | 5 | zero-dim | **70** | 1.43 |
| cyclic-6 | 6 | zero-dim | **156** | 13.16 |
| katsura-3 | 3 | zero-dim | 4 | 0.02 |
| katsura-4 | 4 | zero-dim | 8 | 0.09 |
| katsura-5 | 5 | zero-dim | 16 | 0.52 |
| katsura-6 | 6 | zero-dim | 32 | 3.41 |
| katsura-7 | 7 | zero-dim | **64** | 32.45 |
| katsura-8 | 8 | zero-dim | **128** | 216 |
| katsura-9 | 9 | zero-dim | **256** | 2 128 |
| katsura-10 | 10 | zero-dim | **512** | 21 781 |
| katsura-11 | 11 | zero-dim | **1024** | 277 129 |
| cyclic-7 | 7 | zero-dim | **924** | 1 366 |
| cyclic-8 | 8 | **positive** | — | 21 344 |
| cyclic-9 | 9 | **positive** (Backelin; unverified here) | — | refuses after 10 600 |
| cyclic-10 | 10 | zero-dim (Steel) | **34940** published, unverified here | refuses after 24 300 |
| planted-4 / 6 / 8 | 4 / 6 / 8 | zero-dim | 16 / 64 / 256 | 0.02–0.04 |

### 3.1 Cyclic agrees with the published solution counts

The cyclic-`n` roots system's solution count is a classical result (Björck and Fröberg found all
cyclic `n`-roots for `5 ≤ n ≤ 8` in 1991–92; Backelin and Fröberg proved cyclic-7 has exactly 924).
The published counts for the first few `n` are 70 for `n = 5`, 156 for `n = 6` and 924 for `n = 7`.

**Zeebra measures 70, 156 and — since #424 — 924.** `cyclic-7` is now on the ladder and reaches a
grevlex basis in 1.4 s, and its quotient dimension is **exactly the 924 Backelin and Fröberg
proved**. That is a third published count confirmed, and the first one this document listed as
reachable-in-principle rather than reached.

And the dimension class agrees for the right reason. Backelin's theorem: if `n` has a square divisor
— `d² | n` for some `d ≥ 2` — there are **infinitely many** cyclic `n`-roots. `4 = 2²`, so cyclic-4
must be positive-dimensional, and Zeebra reports it as such. `benchmark_systems`' own documentation
already flagged cyclic-4 as the exception ("A square system is not zero-dimensional merely for being
square"); what is new here is that the flag is **externally correct and for the published reason**,
not a local observation.

And the dimension class now agrees at **three** rungs rather than one. Backelin's theorem predicts
`cyclic-8` and `cyclic-9` positive-dimensional too — `4 | 8` and `9 = 3²` — and `cyclic-8`'s basis
confirms it (`classify_ideal` reports `PositiveDimensional` after 21.3 s). `cyclic-9` is beyond
Zeebra's reach, so there the theorem is the record and the corpus says so. Asserted as arithmetic
rather than per rung, in `corpus::test_a_cyclic_rung_is_zero_dimensional_exactly_where_n_is_squarefree`.

Steel's page supplies a further, independent agreement in kind: Cyclic-10 over GF(32003) at dimension
**34940**. Still out of reach — Zeebra's F4 crosses its live-entry budget after 24.3 s — so it is
recorded in the ladder as the published value that rung exists to one day be checked against.

### 3.2 Katsura's dimensions are exactly `2^n`, which pins a naming offset

The measured dimensions are 4, 8, 16, 32, 64 for `katsura::<3>` through `katsura::<7>` — exactly
`2^(N-1)` across five consecutive rungs, and since #424 across **eight**: `katsura-8` through
`katsura-11` measure 128, 256, 512 and 1024. `benchmark_systems::katsura` sets `n = N - 1`, so that is
`D = 2^n`.

**This resolves a naming trap, and it is the main practical finding of §3.** The literature's
"Katsura-`n`" has `n + 1` variables. Zeebra's `katsura::<N>` has `N` variables with `n = N - 1`. So:

> **Zeebra's `katsura-N` is the literature's Katsura-(N − 1).**

Zeebra's largest rung was `katsura-7`, the literature's **Katsura-6**. Steel's smallest row is
**Katsura 8** = `katsura::<9>`, which was then two rungs above anything Zeebra had computed.
**#424 closed that gap and two more**: `katsura-9`, `katsura-10` and `katsura-11` are on the ladder
and all three complete, so Steel's Katsura 8, 9 and 10 rows now name instances Zeebra computes. What
that buys is the *instance list*, not a comparison — §4 still forbids the wall-clock one, and these
rungs were reached so that this machine's own run of the comparands has somewhere decisive to stand.
Note that `katsura-7` already fails **direct-lex** F4 here (`TooManyNonzeros { nonzeros: 20003295,
limit: 20000000 }`); the rungs above it are reached by grevlex F4 and FGLM, never by direct lex.

A comparison drawn without noticing the offset would have matched Zeebra's `katsura-7` against
Steel's `Katsura 8` — two different systems, a factor of four in quotient dimension apart — and
reported a 19× "speedup" that is entirely the offset. That is the whole reason this issue demanded
invariants before timings.

I did **not** locate a primary citation for `D = 2^n` as a closed form. Five exact powers of two is
strong evidence and it is consistent across the family, but it is recorded here as **measured**, not
as a quoted theorem.

## 4. Why the timings are not comparable, in three independent ways

1. **The reachable Cyclic rows are a different ideal.** Steel's Cyclic 7 and Cyclic 8 carry "**(Hom)**"
   — the homogenized systems. `benchmark_systems::cyclic` generates the **affine** system: `n - 1`
   cyclic elementary symmetric polynomials plus `x_0 ⋯ x_{n-1} - 1`, an inhomogeneous last generator.
   Different ideal, different Hilbert function, not comparable. Cyclic 9 and Cyclic 10 carry no
   "(Hom)" suffix and so match Zeebra's formulation — and Cyclic 9 is **the rung Zeebra's ceiling
   falls at**: its grevlex F4 crosses the live-entry budget after 10.6 s (#424), and Cyclic 10 after
   24.3 s. **So for Cyclic the rows that match are still out of reach, and the rows in reach still do
   not match.** For Katsura that sentence no longer holds: Steel's Katsura 8, 9 and 10 are
   `katsura-9`, `katsura-10` and `katsura-11`, and all three are on the ladder and complete.
2. **The Katsura rows were two to four rungs above Zeebra's ceiling**, per §3.2. No longer true
   after #424 — all three are reachable — which removes this reason for the Katsura rows and leaves
   reason 3, which is sufficient on its own.
3. **The hardware is twenty-two years old and the comparison is unnormalizable.** A 2.087 GHz
   single-core Athlon XP with 1.5 GB, against a 2026 workstation, spans orders of magnitude in clock,
   width, cache and memory before any algorithmic difference. Even where an instance matched, a
   wall-clock ratio would measure the machines.

**No wall-clock speedup against a 2004 figure may be reported anywhere in this repository.** What may
be reported: the invariants of §3, and *ratios between systems under one implementation* — Steel's own
Katsura 9/Katsura 8 ratio of 5.7× against Zeebra's katsura-6/katsura-5 of 6.6×, for instance, which
is a statement about how the family scales and not about whose code is faster.

That last licence is now exercisable on matching instances, which is the one thing #424's rungs
change here. Steel's Katsura 9/Katsura 8 is 5.7x (1.7 s / 0.3 s, Magma 2.11-8); Zeebra's
`katsura-10`/`katsura-9` — the same two problems — is **10.2x** (21.78 s / 2.13 s), and
`katsura-11`/`katsura-10` is 12.7x. Both operands of each ratio are one implementation on one
machine, so these are statements about how the family scales under each engine and **not** about
whose code is faster. The two scaling factors differ by about 2x; nothing here attributes that to
anything, because doing so would need the two engines on one machine, which is what the competitive
board is for.

## 5. The correction to #65, and to a claim of mine in it

#65's premise is left in place in the issue, and this is the correction.

**What is wrong with it:** external numbers do exist for `cyclic` and `katsura`, and more importantly
**external *invariants* exist and Zeebra agrees with them** — cyclic-5 at 70, cyclic-6 at 156,
cyclic-4 positive-dimensional for Backelin's reason, Katsura at `2^n`. That is a genuine external
check, it costs nothing, and it is stronger than a timing because `dim R/I` does not depend on the
machine, the library or the clock. Four of Zeebra's benchmark systems are externally anchored and
nobody had said so.

**What is right about it:** none of those is an external number about *performance*, which is what the
epic wanted. On that reading the premise holds: for every published timing, either the ideal differs
(Cyclic 7/8 Hom), the instance is far out of reach (Cyclic 9/10, Katsura 8/9/10), or the hardware
makes the comparison meaningless — usually two of the three.

**And a correction to my own comment on #65.** I wrote there that the page's figures mean the premise
is "partly false", and quoted Cyclic-10 at 17.6 days and Cyclic-9 over `Q` at 4.6 days as anchors.
Those are real figures and they are **not anchors for anything Zeebra computes**: the first is 1200×
beyond its largest cyclic instance and the second is over the rationals, which Zeebra does not
support. The usable anchor is the invariant table, which that comment did not identify. It overstated
the finding in the direction of making the epic look unnecessary, and the epic is not unnecessary.

## 6. Recommendations

- **Record the invariants in the milestone documents.** `D = 70` for cyclic-5, `156` for cyclic-6,
  `2^n` for Katsura, and cyclic-4's dimension class, each with the published comparand. This is the
  external column the milestone documents have lacked, and it already exists as output.
- **Add a regression test asserting them.** `examples/fglm_baseline.rs` reports `D`; nothing asserts
  it. A generator that drifted — an off-by-one in the cyclic window, a sign in Katsura — would change
  `D` and currently nothing would notice. This is the cheapest external-correctness check available
  to the crate and it is the one concrete follow-up this document recommends.
  **Done (#424):** `CorpusEntry::quotient_dimension` records it per rung and four tests assert it —
  `2^(N−1)` for Katsura across eight consecutive rungs, the published cyclic counts including 924 and
  34940, Backelin's squarefree criterion for the cyclic dimension class, and `2^N` for planted MQ.
  Two further tests compare the record against a computed basis rather than against a formula, so a
  transcription error cannot hide. `docs/research/cross-library-corpus.md` §9 is the table.
- **Rename, or document, the Katsura offset.** `katsura-7` meaning the literature's Katsura-6 is a
  trap that will be fallen into again. Renaming touches every milestone document; a prominent note in
  `benchmark_systems` is the cheap option. Either way it should not stay implicit.
  **Done (#261):** resolved empirically against msolve's own `kat6-31.ms` and documented in
  `cross-library-corpus.md` §2, with a test asserting every generated rung is named by its variable
  count — so a future rung cannot reintroduce the ambiguity by being named carelessly.
- **Do not add a homogenized Cyclic generator for comparability.** It would make Cyclic 7/8 (Hom)
  comparable in kind, and both are still 2004 Athlon figures on a different machine — §4 item 3
  applies regardless. Not worth it for that reason alone.
- **`GF(32003)` is a one-line `PrimeFieldElement32<32003>`** if the `GF(2)` and `GF(32003)` columns
  are ever wanted; nothing here needs it. **Done (#426):** `fields::Zp32003` is that line, and the
  field is now the corpus's *second reference characteristic* rather than a sweep parameter — the
  identity digest is computed per published characteristic, so a `GF(32003)` row is a row about a
  different ideal and needs its own frozen digest. `docs/research/cross-library-corpus.md` §4b is
  the decision and the argument. The engines are re-run here over that field rather than compared
  against §2.1's figures, which §4 still forbids.
- **Rationals are out of scope**, stated so the `Q` rows are not mistaken for a gap.
- **Quote §2.3's V2.27 figures rather than §2.1's 2004 column** wherever a Magma number is used as a
  difficulty scale, and say which machine and core count it is. The 2004 column stays for the
  invariants it carries (Cyclic-10's 34940, the GF(2) dimension) and for nothing else. Magma cannot
  be measured here at all — no licence (§2.3) — so this is the whole of what is available.

## 7. Other collections, assessed against #65's bar

#65's bar: a specific instance, a trustworthy reference result, and a path to verification.

| collection | verdict |
|---|---|
| **Steel's Magma GB timings page** | **accept, for invariants only.** Cyclic-10's dimension 34940 and the GF(2) Cyclic rows are checkable values; the HFE rows go to #198, where they are much more valuable. |
| **Magma's `info/topic_gb` page** (subscriber-side, §2.3) | **accept as a modern difficulty scale, reject as a comparand.** Its V2.27 figures on an i7-7700 are the only post-2004 Magma timings on record here and they come in 1-core and 4-core pairs, which is a usable published scaling figure. No instances, no repetitions, no build description, and no Katsura rows, so §4 still forbids a ratio against Zeebra. |
| **Steel's *Dense Variant of the F4 Algorithm* page** (`/users/allan/densef4/`) | **defer to #218 and #225.** It is about representation, which is #218's open question, and the HFE-80 matrices it discusses are "moderately dense" over GF(2) — the datum #225 wants at 64×64 block granularity. Not a benchmark source. |
| **SymbolicData** | **not assessed.** Deliberately: §3 found that the anchor Zeebra needs is an invariant, and a fourth catalogue of systems does not supply one. Reopen only if a specific instance with a published `dim R/I` is wanted. |
| **msolve's published benchmarks** | **the right follow-up if a *modern* timing comparand is ever wanted**, which §4 argues is the only way to get one. Not pursued here; it would be its own issue, and it should be measured on one machine rather than quoted. |

## 8. Reproducing

```sh
cargo run --release --example fglm_baseline
cargo run --release --example fglm_baseline -- cyclic-6   # one system per process
```

The external table in §2 must be re-read from the page rather than from this document if a figure is
to be quoted; see #198 for why that rule exists.

## 9. What this did not do

- **No timing comparison was drawn**, by design. §4 is the argument for why none is available.
- **No regression test was added.** §6 recommends one; it is a change to the test suite and belongs in
  its own commit. **Added in #424**, in `corpus.rs` rather than here, because the corpus is where a
  rung's identity is frozen and an invariant belongs beside it.
- **`D = 2^n` for Katsura is measured, not cited.** No primary source was located for the closed
  form. Still true after #424, which extended the evidence from five consecutive rungs to **eight**
  — strong, and still not a citation.
- **The cyclic solution counts were confirmed from the secondary literature**, not from
  Björck–Fröberg or Backelin–Fröberg directly. The agreement is exact at all three rungs Zeebra now
  reaches — 70, 156 and, since #424, **924** — and Steel's independent Cyclic-10 figure is
  consistent, but the primary papers were not read.
- **Nothing was measured over GF(2) or GF(32003)**, so the GF(2) Cyclic rows of §2.2 have no Zeebra
  comparand yet. #218 has since made characteristic two work, so that is now possible.
  **`GF(32003)` has since been measured (#426)**: it is a published corpus characteristic, and
  `research/competitive/` carries Zeebra, Singular, msolve, Groebner.jl and Sagebrush over it on the
  whole Katsura/Cyclic/MQ ladder. **`GF(2)` has since been measured too (#427)** — §10.

---

## 10. GF(2): the Cyclic invariants, measured (#427)

**No wall-clock comparison against §2.2's figures is drawn here, and none may be.** §4's three
reasons stand and §7 graded Steel's page "accept, for invariants only". What §2.2 is good for is the
one checkable claim on it — "The ideal has dimension 4" at Cyclic 10 — and that is a *Krull*
dimension, not the vector-space dimension the `GF(32003)` note reports. §2.2 already drew that
distinction; this section acts on it.

### 10.1 Zeebra gained a Krull dimension, because it did not have one

Checking Steel's 4 needed a quantity the crate could not compute. `IdealClass` is three-valued —
`Unit`, `ZeroDimensional`, `PositiveDimensional` — and `PositiveDimensional` carries no integer, so
"positive-dimensional" was the most that could be said about any of the degenerate rungs below.
`fglm::krull_dimension` is the addition: for a monomial ideal, `dim R/J` is the size of the largest
set of variables containing no leading monomial's support, which is a branch-and-bound over subsets
that collapses after `N` checks whenever the ideal is zero-dimensional. It agrees with Singular's
`dim` and Groebner.jl's `Groebner.dimension` wherever both were run.

### 10.2 The invariants, four ways

All values measured on this machine, none cited. Controls at `GF(32003)` reproduce the published
70, 156 and 924 exactly, which is what licenses the `GF(2)` column beside them.

| rung | `GF(32003)` control | `GF(2)` Krull dim | `GF(2)` `D` | `GF(2)` grevlex basis | agreeing engines |
|---|---|---:|---:|---:|---|
| `cyclic-4` | positive-dim, Krull 1 | 1 | — | 7 | Zeebra, Singular |
| `cyclic-5` | zero-dim, `D = 70` | 0 | 70 | 20 | Zeebra, msolve, Singular, Groebner.jl, Sagebrush |
| `cyclic-6` | zero-dim, `D = 156` | **2** | — | 19 | Zeebra, msolve, Singular, Groebner.jl |
| `cyclic-7` | zero-dim, `D = 924` | 0 | **728** | 173 | Zeebra, msolve, Singular, Groebner.jl |
| `cyclic-8` | positive-dim, Krull 1 | **3** | — | 191 | msolve, Groebner.jl |
| `cyclic-9` | positive-dim (Backelin) | **2** | — | 1228 | msolve, Groebner.jl |

**Two findings here are worth more than the rows.**

The first is that **Backelin's squarefree criterion is a characteristic-zero statement.** It says
cyclic-`n` has finitely many roots exactly when `n` is squarefree, and §3.1 records Zeebra agreeing
with it at three rungs. Mod 2 it fails: `6 = 2 · 3` is squarefree and `cyclic-6` over `GF(2)` has
Krull dimension 2. `corpus::test_backelins_criterion_does_not_survive_the_reduction_mod_two` is the
assertion, and the criterion's test in `corpus.rs` is now scoped to the characteristics where it
holds rather than asserted universally.

The second is that **the reduction is not uniformly destructive, and that is why a blanket
characteristic would have been wrong.** `cyclic-4` and `cyclic-5` are completely unmoved — Krull 1
and `D = 70`, the same instances' invariants at `2^31 − 1`. `cyclic-7` stays zero-dimensional and
changes its count. `cyclic-6` changes class. `cyclic-8` stays positive-dimensional and changes its
dimension, from 1 to 3 — which is the case a `zero_dimensional: bool` cannot express and the reason
`corpus::Degeneracy` records a Krull dimension instead.

### 10.3 Whether the field equations are included: **no, in every published row**

Over `GF(2)` the field equations `x^2 − x` are available, and an ideal with them adjoined is **a
different ideal**. The README's phrasing is that they "make a quotient dimension count base-field
points"; `src/grobner/field_equations.rs` implements them and
`field_equations::the_quotient_dimension_counts_gf2_points_only_with_field_equations` is the
demonstration that the count changes.

**Steel's rows do not adjoin them, so no row in §10.2 does either.** Consequences, stated rather
than left to be inferred:

- `D = 728` at `cyclic-7` counts zeros over the algebraic closure of `GF(2)` **with multiplicity**.
  It is *not* the number of `GF(2)`-rational points, and it must not be read as one.
- A row that did adjoin them would be recorded by `Instance::transformation`, which is inside the
  identity digest (`Instance::canonical`). So the two ideals can never collide on a digest and a
  figure cannot migrate between them silently.
  `corpus::test_no_published_row_carries_a_field_equation_transformation` is the guard on the whole
  published corpus, not only the `GF(2)` part.

This is the same silent-wrongness class as the `0x11D`/`0x11B` modulus #197 settled: a plausible
number for an ideal nobody named.

### 10.4 Which engines accept characteristic two

Task 2's question, answered by running each engine rather than by reading its bounds. The field
logic in `src/grobner/external/` reasoned about **upper** bounds only, so before this `GF(2)` was
reported as the widest band on the board — the maximum corroboration at every task. One engine makes
that false.

| engine | basis at `GF(2)` | eliminant at `GF(2)` | conversion at `GF(2)` |
|---|---|---|---|
| Zeebra | yes — now compiled, Cyclic widths 4–10 | yes | yes |
| msolve 0.11.0 | **yes**, verified to `cyclic-9` | **no — does not terminate** | n/a (no lex order at any field) |
| Singular | yes, `dim`/`vdim` correct | yes | yes |
| Groebner.jl | yes, and reports the Krull dimension | n/a (no FGLM in 0.10.11) | n/a |
| Sagebrush | yes, both the `f4` and `fglm` routes | n/a (no eliminant) | yes |

Every "yes" above was run, not inferred. The basis column is **five-way** at `cyclic-5` — Zeebra,
msolve, Singular, Groebner.jl and Sagebrush all return a 20-element grevlex basis and all four that
report a quotient dimension give 70. The conversion column is **two-way**: Singular's `fglm` and
Sagebrush's `fglm` route each produce an **11-element lex basis** over `GF(2)`, with Singular
confirming `dim 0` and `vdim 70` after the conversion. So
`corroboration_for(LexBasisByConversion, 2)` is `TwoWay` and that is a measured statement rather
than an arithmetic consequence of the ceilings.

**msolve's eliminant is the one restriction, and it is a non-termination rather than a refusal.**
Its sparse-FGLM needs the ideal in shape position; when the staircase is not generic enough its
default remedy (`-c 2`) permutes the variables and then adjoins a *random* linear form. Over `GF(2)`
there is no randomness to draw on — every nonzero coefficient is 1 — so the retry redraws from
candidates that have already failed, and the loop has no exit. Measured on `cyclic-5` over `GF(2)`:
74 140 `TIMINGS` blocks and 156 MB of verbose output in one minute, with the F4 basis itself
complete almost immediately. The same input under `-c 0` quits at once with "Computation failed",
which is the honest answer the default mode never reaches.

This is the mirror image of msolve's *upper* eliminant bound, where above `1515531529` the
sparse-FGLM failure is likewise laundered into an unbounded retry. So `msolve.rs` now declares
`MIN_CHARACTERISTIC_ELIMINANT` beside `MAX_CHARACTERISTIC_ELIMINANT`, and `supports` refuses the
task at `GF(2)` with a reason before any subprocess starts. Without that the sweep's wall limit
would have recorded a **timing lower bound** for a computation that was never going to finish —
`Unsupported`, not `StoppedByLimit`, is the difference.

**The floor is declared as a necessary and not a sufficient condition, and the evidence for that is
recorded rather than smoothed over.** At `p ≥ 3` the retry is probabilistic in both the prime and
the instance: on `cyclic-5` the eliminant returns at `p = 7, 13, 17, 251` and `32003`, and **does
not return at `p = 3, 5` or `11`**. A prime above the floor is therefore no promise of termination
and the wall limit remains the backstop there; a prime below it is a promise of non-termination,
which is the only part that may be declared as a bound. Inventing a clean "small primes fail" cutoff
would have been wrong at `p = 11`.

### 10.5 `cyclic-10` against Steel's Krull dimension 4

Steel's Cyclic 10 over `GF(2)` is the rung this section exists for, and it is **the hardest rung on
the whole corpus** — his own run took 12.3 hours and 9.3 GB of a 750 MHz Sunfire, and that was
Magma's F4, the fastest engine in his table by an order of magnitude.

**Not resolved at hand-off; the attempt and its stage are recorded, which is what #427 asks for.**
`corpus::test_where_zeebras_cyclic_ladder_stops_over_gf2` is the attempt as a runnable test,
printing a basis size and a Krull dimension per rung and refusing where it must. What is settled is
everything up to it: the ladder is externally corroborated through `cyclic-9`, where two independent
modern engines agree on both a 1228-element basis and Krull dimension 2.

What that buys for Steel's 4 is a **consistency check rather than a confirmation**. His figure is
the one rung above a sequence this document can now vouch for, and the sequence makes a dimension of
4 at `cyclic-10` unremarkable where it would have looked anomalous against §2.1's zero-dimensional
`GF(32003)` row: at `GF(2)` the Cyclic ladder is positive-dimensional at 6, 8 and 9 and
zero-dimensional only at 5 and 7. **It is not yet checked, and it is not reported as checked.**
