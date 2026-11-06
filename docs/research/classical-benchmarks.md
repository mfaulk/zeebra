# Classical benchmarks: the invariants are externally anchored, the timings are not

Deliverable for A7 (#199), a child of the benchmark-corpus epic #65. The question: do Zeebra's three
synthetic generators — `cyclic`, `katsura`, `planted` — have external reference points, and if so
what may honestly be compared against them?

**The answer is split, and the split is the result.** The *invariants* of two of the three families
match published values exactly, which is a real anchor and a stronger one than a stopwatch. The
*timings* on the one page that publishes them are not comparable to Zeebra's, for three independent
reasons. §5 states the correction this forces on #65, including on a claim I made there myself.

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
| planted-4 / 6 / 8 | 4 / 6 / 8 | zero-dim | 16 / 64 / 256 | 0.02–0.04 |

### 3.1 Cyclic agrees with the published solution counts

The cyclic-`n` roots system's solution count is a classical result (Björck and Fröberg found all
cyclic `n`-roots for `5 ≤ n ≤ 8` in 1991–92; Backelin and Fröberg proved cyclic-7 has exactly 924).
The published counts for the first few `n` are 70 for `n = 5`, 156 for `n = 6` and 924 for `n = 7`.

**Zeebra measures 70 and 156.** Those are the two rungs it reaches, and both agree exactly.

And the dimension class agrees for the right reason. Backelin's theorem: if `n` has a square divisor
— `d² | n` for some `d ≥ 2` — there are **infinitely many** cyclic `n`-roots. `4 = 2²`, so cyclic-4
must be positive-dimensional, and Zeebra reports it as such. `benchmark_systems`' own documentation
already flagged cyclic-4 as the exception ("A square system is not zero-dimensional merely for being
square"); what is new here is that the flag is **externally correct and for the published reason**,
not a local observation.

Steel's page supplies a third, independent agreement in kind: Cyclic-10 over GF(32003) at dimension
**34940**. Out of reach, but it is a value Zeebra could one day be checked against.

### 3.2 Katsura's dimensions are exactly `2^n`, which pins a naming offset

The measured dimensions are 4, 8, 16, 32, 64 for `katsura::<3>` through `katsura::<7>` — exactly
`2^(N-1)` across five consecutive rungs. `benchmark_systems::katsura` sets `n = N - 1`, so that is
`D = 2^n`.

**This resolves a naming trap, and it is the main practical finding of §3.** The literature's
"Katsura-`n`" has `n + 1` variables. Zeebra's `katsura::<N>` has `N` variables with `n = N - 1`. So:

> **Zeebra's `katsura-N` is the literature's Katsura-(N − 1).**

Zeebra's largest rung, `katsura-7`, is therefore the literature's **Katsura-6**. Steel's smallest row
is **Katsura 8** = `katsura::<9>` — **two rungs above anything Zeebra has ever computed**, and
`katsura-7` already fails direct-lex F4 here (`TooManyNonzeros { nonzeros: 20003295, limit:
20000000 }`).

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
   "(Hom)" suffix and so match Zeebra's formulation — and they cost 1453.6 s and 17.6 days against
   Zeebra's cyclic-6 at 13.16 ms. **So the rows that match are out of reach, and the rows in reach do
   not match.**
2. **The Katsura rows are two to four rungs above Zeebra's ceiling**, per §3.2.
3. **The hardware is twenty-two years old and the comparison is unnormalizable.** A 2.087 GHz
   single-core Athlon XP with 1.5 GB, against a 2026 workstation, spans orders of magnitude in clock,
   width, cache and memory before any algorithmic difference. Even where an instance matched, a
   wall-clock ratio would measure the machines.

**No wall-clock speedup against a 2004 figure may be reported anywhere in this repository.** What may
be reported: the invariants of §3, and *ratios between systems under one implementation* — Steel's own
Katsura 9/Katsura 8 ratio of 5.7× against Zeebra's katsura-6/katsura-5 of 6.6×, for instance, which
is a statement about how the family scales and not about whose code is faster.

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
- **Rename, or document, the Katsura offset.** `katsura-7` meaning the literature's Katsura-6 is a
  trap that will be fallen into again. Renaming touches every milestone document; a prominent note in
  `benchmark_systems` is the cheap option. Either way it should not stay implicit.
- **Do not add a homogenized Cyclic generator for comparability.** It would make Cyclic 7/8 (Hom)
  comparable in kind, and both are still 2004 Athlon figures on a different machine — §4 item 3
  applies regardless. Not worth it for that reason alone.
- **`GF(32003)` is a one-line `PrimeFieldElement32<32003>`** if the `GF(2)` and `GF(32003)` columns
  are ever wanted; nothing here needs it.
- **Rationals are out of scope**, stated so the `Q` rows are not mistaken for a gap.

## 7. Other collections, assessed against #65's bar

#65's bar: a specific instance, a trustworthy reference result, and a path to verification.

| collection | verdict |
|---|---|
| **Steel's Magma GB timings page** | **accept, for invariants only.** Cyclic-10's dimension 34940 and the GF(2) Cyclic rows are checkable values; the HFE rows go to #198, where they are much more valuable. |
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
  its own commit.
- **`D = 2^n` for Katsura is measured, not cited.** No primary source was located for the closed form.
- **The cyclic solution counts were confirmed from the secondary literature**, not from
  Björck–Fröberg or Backelin–Fröberg directly. The agreement is exact at both rungs Zeebra reaches
  and Steel's independent Cyclic-10 figure is consistent, but the primary papers were not read.
- **Nothing was measured over GF(2) or GF(32003)**, so the GF(2) Cyclic rows of §2.2 have no Zeebra
  comparand yet. #218 has since made characteristic two work, so that is now possible.
