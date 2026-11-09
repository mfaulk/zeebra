# The cross-library corpus: the same ideal in every engine, and the two ways that silently fails

**Measured at:** publication bound `f94b3df0` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).

Policy and status for #261. The corpus itself is `src/grobner/external/corpus.rs`; its digest
manifest is produced by `corpus::manifest()` and frozen by `test_the_manifest_is_frozen`.

A cross-library comparison measures nothing unless every engine was given **the same ideal**. The
two families everyone benchmarks on each have a naming convention that produces a *different* ideal
without producing an error — the run succeeds, the timings look comparable, and the numbers are of
two different problems. Both are resolved below against another engine's own distributed input
files rather than by argument, because a convention asserted is a convention that drifts.

**The governing rule: publish no timing for a family whose ideal equivalence has not been
verified.** The status table in §5 is what that rule is enforced against.

---

## 1. Identity is the digest, and the name is for humans

Every instance is an
[`Instance`](../../src/grobner/external/contract.rs) whose `digest()` is SHA-256 over its canonical
form: field, extension degree and defining polynomial, monomial order, variable names **in order**,
any transformation, then every generator one per line. Two runs whose digests differ are not runs
on the same problem, whatever their names say, and `RunReport::speedup_over` refuses them.

This matters more than usual here, because the hazards below are precisely cases where the *name*
agrees and the problem does not. The digest is the arbiter either way; the naming rules exist so
that a human reading a table is not misled before anyone checks a digest.

---

## 2. Hazard 1: Katsura indexing, resolved

The literature's **Katsura-n has n + 1 variables** `u_0 … u_n`. So the family index and the variable
count differ by one, and a benchmark table saying "katsura 6" can mean six variables or seven.
Zeebra's `benchmark_systems::katsura` is const-generic in the **variable count**: `katsura::<6>` is
six variables, which the literature calls Katsura-5. Its doc comment says so, and the `N >= 2`
assertion is on the variable count.

**Resolved empirically.** msolve 0.11.0 ships `input_files/kat6-31.ms`, which declares

```
x1,x2,x3,x4,x5,x6
1073741827
x1+2*x2+2*x3+2*x4+2*x5+2*x6-1,
x1^2+2*x2^2+2*x3^2+2*x4^2+2*x5^2+2*x6^2-x1,
2*x1*x2+2*x2*x3+2*x3*x4+2*x4*x5+2*x5*x6-x2,
...
```

Six variables and six equations — one linear and five quadratic — and it is `katsura::<6>`
generator for generator. `test_katsura_6_is_msolves_kat6` pins it against that verbatim literal,
comparing **sets** because the two engines order their generators differently (msolve puts the
linear equation first, Zeebra last) and a generating set is a set.

**The translation, therefore:**

| | name | variables |
|---|---|---|
| Literature | Katsura-5 | 6 |
| Zeebra | `katsura::<6>` | 6 |
| msolve | `kat6` | 6 |
| This corpus | `katsura-6` | 6 |

So msolve names by variable count and agrees with Zeebra's type parameter. **Every family this
module generates is named by variable count, and the literature's `n` appears nowhere in it.** A
test asserts that each such entry's trailing number equals its built variable count, so a future
entry cannot reintroduce the ambiguity by being named carelessly.

The two families taken from the cryptanalysis registry — Poseidon and Anemoi — keep their
**registry id** instead. That id is their identity everywhere else in the crate, and renaming it to
suit a convention local to the corpus would be the worse trade; their variable count is a
consequence of the round count and is carried in the manifest.

Groebner.jl exposes no `katsuran` in the provisioned version (checked: `names(Groebner, all=true)`
contains no Katsura or Cyclic generator), so its adapter must be given the system as text from this
corpus rather than asked for its own. That is the better arrangement anyway — a corpus of systems
each engine generates for itself is a corpus of several ideals.

---

## 3. Hazard 2: affine versus homogenized Cyclic, resolved

The cyclic-n roots system has two circulating forms:

- **Affine.** `e_1 … e_{n-1}` the cyclic elementary symmetric polynomials, closed with
  `x_1 ⋯ x_n − 1`. Inhomogeneous; zero-dimensional for squarefree n.
- **Homogenized.** The constant replaced by `h^n` in one extra variable, or dropped entirely.
  Positive-dimensional; a different basis, a different quotient, and a cost that is not comparable
  with the affine one.

Benchmark tables rarely say which they used, and both are called "cyclic-n".

**Resolved empirically.** msolve's `input_files/cyclic5-16.ms` closes with `x1*x2*x3*x4*x5-1`, so
it is the affine form, and it is `cyclic::<5>` generator for generator —
`test_cyclic_5_is_msolves_cyclic5_and_is_affine` pins it. **The corpus is affine throughout.** A
homogenized instance would be a different problem, would get a different digest, and would record
the homogenization in `Instance::transformation`, which is the field that exists for exactly this.

### A square system is not zero-dimensional for being square

`cyclic::<4>` is **positive-dimensional**: its grevlex leading-term ideal contains no power of the
last variable. It is in the corpus deliberately, as the easy rung that exercises that path, and its
ladder entry records `zero_dimensional: false`. Consequences, which are facts about the ideal and
not failures of any engine:

- `Task::LexBasisByConversion` does not apply to it. FGLM needs a finite quotient algebra.
- Its quotient dimension invariant is absent, not zero. `Invariants::agree` compares only fields
  both sides carry, so an engine reporting no dimension and an engine reporting none agree without
  either claiming anything.

---

## 4. The two reference fields, and why neither is wider

`REFERENCE_CHARACTERISTIC = 2^31 − 1` and `SMALL_PRIME_CHARACTERISTIC = 32003`.

msolve caps at `p ≤ 2^31 − 1` and Singular is identical (`MAX_CHARACTERISTIC = 1 << 31`, checked
`>=`). So `2^31 − 1` is the **largest prime every engine in the comparison accepts**, and a corpus
keyed on anything wider would render most of the table `Unsupported` and measure nothing.

This is a constraint on the comparison, not on Zeebra, and the protocol document's §3 records what
it costs: Zeebra's 32–64-bit fields have only Groebner.jl and Sagebrush as comparands, and its
254/255-bit fields have none at any size. Those rows say so rather than being omitted.

`GF(32003)` is the **second** reference field, and §4b is the decision and the argument for it.

### 4a. The declared field is the generated field

A third hazard of the same shape as §2 and §3, and the one that was live rather than hypothetical.
An `Instance` carries a `FieldSpec` and a system, and **nothing in the text ties them together**:
coefficients render as residues, so `−1` over `2^31 − 1` is the numeral `2147483646`, which is a
perfectly well-formed element of some smaller prime field — a *different* element of a *different*
ring. So a `characteristic` argument that reached only the `FieldSpec` produced a valid input file
describing a different ideal from the one named, with the digest and the name both claiming
otherwise. That was #425, and `msolve.rs`'s eliminant tests were its live victims: they ask the
corpus for rungs at `2^30 + 3`, below msolve's eliminant ceiling, and were handed systems reduced
mod `2^31 − 1`.

The const-generic families — Katsura, Cyclic, planted MQ — are now generated over the field they
declare. They are const-generic in the field as well as the size, so a prime known only at run time
cannot be turned into a type: `corpus::GENERATED_CHARACTERISTICS` is the list of compiled fields and
`corpus::instance` returns `None` outside it, which is the same idiom it already used for a size
nobody wrote down.

| family | at a prime outside the compiled set | why |
|---|---|---|
| Katsura, Cyclic, planted MQ | `None` | const-generic in the field; a prime nobody compiled is a field nobody has |
| random MQ | builds | its generator reduces at run time through `CaseField`, so every prime is available |
| Poseidon, Anemoi | builds, at the **registry's** field | round constants are keyed on the prime, so the argument is ignored by design (§5) |

`test_an_uncompiled_characteristic_is_refused_rather_than_mislabeled` pins all three dispositions,
and `test_every_rendered_coefficient_is_a_residue_of_the_declared_characteristic` asserts the
property on the **rendered text** rather than on the polynomials in memory — which is the bytes
every engine is handed.

**The alternative was rejected for a stated reason.** Coefficients could be rendered from signed
integers instead, making these families' text identical at every prime. That would also change
every frozen digest in `ladder()`, retroactively re-identifying every published figure. Generating
over the declared field leaves the reference-prime text byte-identical, which
`test_the_manifest_is_frozen` confirms.

`ALTERNATE_CHARACTERISTIC = 2^30 + 3 = 1073741827` is a compiled prime that is **not** a corpus
identity: no frozen digest, no published row. It is that prime rather than an arbitrary one because
it is the characteristic msolve's own `input_files/kat6-31.ms` declares, so it is the field the
Katsura equivalence evidence was shipped over, and because it sits below
`ceilings::MSOLVE_ELIMINANT` where the reference prime does not — which is what `msolve.rs`'s
eliminant tests need.

### 4b. `GF(32003)` is a second corpus identity, not a sweep axis

**The decision, and why it could not have gone the other way.** §1 says identity is the digest and
the name is for humans. A rung at `GF(32003)` and the same rung at `GF(2^31 − 1)` have **different
digests**, and `RunReport::speedup_over` refuses to compare rows whose digests differ. So varying
the characteristic does not produce another measurement of one problem; it produces another problem.
"Sweep axis" is the wrong word for what happens — a parameter is something a figure is taken *at*,
and this is something a figure is taken *of*.

That settles it, because of what makes a corpus row publishable at all: its generated system is
**pinned**. `test_the_manifest_is_frozen` is the test that catches a generator drifting out from
under the figures, and it can only do that where a digest was frozen. A `GF(32003)` row with no
frozen digest would be a published figure whose problem nothing pins — the exact hole the `digest`
field exists to close, and in the exact place #426 wanted a *regenerable* record rather than a
number carried in prose.

So the corpus has **three tiers**, and `CorpusEntry::digest_at` is the boundary:

| tier | constant | frozen digest | may a figure be published? |
|---|---|---|---|
| published | `PUBLISHED_CHARACTERISTICS` = `[32003, 2^31 − 1]` | yes, one per rung | **yes** |
| generated | `GENERATED_CHARACTERISTICS`, which adds `2^30 + 3` | no | no — the instance is honest, its identity is not pinned |
| neither | — | n/a | `corpus::instance` returns `None` |

`CorpusEntry::digests` is therefore `&[(characteristic, digest)]`, keyed on the characteristic the
built instance **declares**. Two consequences fall out instead of needing special cases:

- A family whose field varies carries **two** digests.
- A registry row carries **one**. Poseidon's and Anemoi's round constants are derived from the
  prime, so asking for another one does not produce another instance (§5) — keying on the declared
  rather than the requested characteristic is what makes that automatic.
  `test_a_registry_rung_has_one_identity_at_both_published_characteristics` asserts both halves,
  and the sweep skips such a rung at the small prime rather than appending a duplicate row.

**Why `32003` and not some other small prime.** Three reasons.

1. **It is the field the published record is written in.** Steel's entire modular column — Magma
   2.11-8/2.11-1/2.10, Singular 2-0-5, Macaulay 2 — runs over `GF(32003)`, and his own note says
   why: the comparands "handle small primes only up to 16 bits". msolve ships a 16-bit
   `cyclic5-16.ms` for the same reason. `classical-benchmarks.md` §6 scoped the field itself and
   this implements it.
2. **It makes the eliminant a two-engine task where it was one.** msolve's eliminant stops below
   `1515531529` and the reference prime is above it, so at `2^31 − 1` `UnivariateEliminant` has
   exactly **one** external engine, Singular. At `32003` msolve joins.
   `test_the_small_prime_adds_msolve_to_the_eliminant_task` is that, as arithmetic over the engine
   ceilings rather than as prose.
3. **It measures a different arithmetic regime, and Zeebra's 32-bit path at all.** Zeebra reaches it
   through `Zp32003 = PrimeFieldElement32<32003>`, a 32-bit Montgomery field, where the reference
   prime uses the 64-bit one. The *rendered text* is identical either way — a residue is a residue —
   so the representation is invisible to the digest and visible only in Zeebra's own timing.

### 4b-i. Measured: no engine on the board is faster at 15 bits than at 31

#426 expected "Zeebra's 32-bit field path to differ from its 64-bit one by more than noise; if it
does not, that is itself worth recording." **It does not, and neither does any other engine's.**

130 measured rows at `GF(32003)` — 13 rungs × 2 tasks × 5 engines, one row per process under
`tools/benchlock.sh`, 60 s wall, `taskset -c 0-7` — in `research/competitive/`. Against the existing
`GF(2^31 − 1)` rows, basis task, both measured the same way:

| rung | Zeebra | Singular | msolve | Groebner.jl | Sagebrush |
|---|---:|---:|---:|---:|---:|
| katsura-7 | 1.04 | 1.00 | 1.00 | 0.97 | 1.00 |
| cyclic-6 | 1.02 | 1.11 | 1.00 | 1.01 | 0.99 |
| mq-random-10 | 1.01 | 0.99 | 1.09 | 0.98 | 1.04 |
| mq-planted-14 | 1.00 | 0.88 | 1.00 | 0.80 | 1.00 |

Each cell is `GF(2^31 − 1)` wall over `GF(32003)` wall, **and it is not a speedup**: the two are
different ideals with different digests, and the two sets of rows carry different commits, so
`CompetitiveRecord::comparable_with` refuses the pair and the board computes no ratio. They are
printed side by side as an observation about an arithmetic regime, which is what #426 asked for, and
nothing stronger may be read off them.

Read carefully, almost every row above is a floor rather than a measurement: msolve and Sagebrush sit
at their ~10.4 ms process startup on every classical rung and Singular at ~36–51 ms, so their `1.00`s
say "startup did not change" and nothing else. The one rung clear of every floor is
**`mq-random-10`**, where all five engines are within 1.09 — Zeebra 28.69 s vs 29.01 s, Singular
7.07 s vs 7.00 s, msolve 222.78 ms vs 243.14 ms, Groebner.jl 84.82 ms vs 83.41 ms, Sagebrush
323.49 ms vs 334.88 ms, `GF(32003)` first — with **no consistent direction**. If a 15-bit prime were
cheaper to reduce in, this is the row where it would show.

**Why, for Zeebra, and it is mechanical rather than mysterious.** `Zp32003` stores a `u32` where the
reference field stores a `u64`, but the quantity F4 allocates and streams is a
`SparseRow` entry, `(usize, F)` — and `(usize, u32)` is **16 bytes**, exactly what `(usize, u64)` is,
because the `usize` forces 8-byte alignment and the narrower field is spent entirely on padding.
`test_a_narrow_field_does_not_narrow_a_sparse_entry` asserts it. So the entry budget admits the same
number of entries, the elimination moves the same bytes, and the only thing that got cheaper is a
multiply that was never the bottleneck at these sizes. `F4Options::max_live_bytes` makes the same
point in the other direction for BN254, where an entry is 40 bytes.

This does not retire the field. Reasons 1 and 2 above — it is the field the published record is
written in, and it is what makes the eliminant a two-engine task — are the reasons that survive, and
they were never speed claims. What it retires is reason 3's *expectation*.

**The machine was shared, and that is disclosed rather than assumed away.** Two other agents were
working on this workstation throughout, and a `benchlock` run excludes other *benchmarks* under the
lock — not other builds. All rows above were taken under the lock with nothing of this agent's own
running; **an earlier complete set of 130 rows, taken while this agent was itself compiling, was
discarded rather than published.** The `stopped-by-limit` rows on `mq-random-14` rest on a 60 s wall
and should be read as "did not finish in 60 s on a shared box", not as a ceiling — except Zeebra's,
which crossed `max_live_nonzeros` at 20 005 445 entries, a bound reproducible on any machine.

### 4c. What `GF(32003)` does not buy, against the expectation it was filed on

#426's strongest stated argument was that msolve answers no `lex-basis-by-conversion` row at the
corpus characteristic *because* `2^31 − 1` is above its eliminant non-termination bound, and that
`32003` would therefore hand the conversion task its most informative comparand. **That is not why
msolve refuses, and `GF(32003)` does not change it.**

`msolve.rs`'s `supports` refuses `LexBasisByConversion` with `Unsupported::Task` before any field is
looked at, because msolve has **no lex order at all**: `-g` is grevlex only, `-e` builds a two-block
degrevlex elimination order, and the rational parametrization is not a basis. So msolve is not a
conversion comparand at **any** field, and the ~30x deficit `competitive-baseline.md` §1 reports —
measured against msolve on Anemoi at `p = 65537` — cannot become a `lex-basis-by-conversion` board
row for that reason rather than for a field reason. What `GF(32003)` gives that task is nothing; what
it gives the *eliminant* task is a second engine, which is reason 2 above and is the narrower true
claim.

Checking that turned up two more errors in `corpus::ceiling_for`, each the opposite of the other and
each now fixed against the adapter that implements it:

| arm | was | is | source |
|---|---|---|---|
| msolve, conversion | `MSOLVE` (`2^31`) | **absent** | `msolve.rs` refuses the task by name |
| Sagebrush, conversion | **absent** | `FGLM_MAX_CHARACTERISTIC` (`2^31`) | `fglm.rs:329`; the board holds 14 completed Sagebrush conversion rows |
| Groebner.jl, eliminant | `GROEBNER_JL` | **absent** | `names(Groebner)` at 0.10.11 has no eliminant |

The first two **cancelled in the count** — three engines either way at the reference prime — which is
why no corroboration assertion caught them, and why
`test_the_conversion_comparands_are_singular_and_sagebrush` now asserts the *roster* and not only
the tally. The corrected numbers are in §5a.

---

## 5. How equivalence is established, and what each family may claim

A family's ideal equivalence is established by **one** of four kinds of evidence, recorded as
`Equivalence` on every ladder entry. The kind is a property of the *construction*, so every rung of
a family shares it.

| Evidence | What it is | Licenses a timing? | Corroborated? |
|---|---|---|---|
| `ComparandFile { tool, file }` | agrees with a comparand's **own distributed input file**, generator for generator | **yes** — the strongest: it compares against bytes somebody else shipped, not against this crate's reading of a paper | yes |
| `KnownSolution` | a **known solution must satisfy the system as handed to every engine** | **yes** — and in one respect stronger than a digest: an engine whose parser read the text differently will not vanish at the point, which is detectable without that engine computing anything | yes |
| `LiveOracle { tool }` | checked against live Singular's invariants | **yes**, weakest of the three | yes |
| `SoleComparand { tool, reason }` | exactly **one** external engine reaches the field | **yes, with the fact stated** — the ratio is valid and invariants are checkable against the one engine | **no** — agreement is two-way and cannot be triangulated |
| `NoComparand { reason }` | **no** external engine reaches the field | **no** | no |

Two methods, two questions. `Equivalence::licenses_timing` asks whether a figure may be published;
`Equivalence::is_corroborated` asks whether a **third** opinion exists, so that a disagreement
could name the odd engine out. `test_every_family_licenses_a_timing_and_only_some_are_corroborated`
asserts both for every rung.

**Both are read by the renderer**, which is what makes them a gate rather than a note to whoever
opens `corpus.rs` (#518). `CompetitiveBoard::to_markdown`'s speedup table carries a **provenance**
column per ratio and `Speedup::is_publishable` is the conjunction of all three gates, so:

* a problem the corpus has no recorded equivalence for — anything that is not a ladder rung — is
  **refused in the cell**, `NOT PUBLISHABLE: ... is not a corpus rung`, and counted in the summary;
* `NoComparand` is refused the same way, carrying the variant's own `reason`;
* a `SoleComparand` ratio renders with `NOT CORROBORATED` and the one engine's name beside it,
  which is the "with the fact stated" half of the rule above.

The refusals print the ratio and keep the row, as the startup-floor guard does: a dropped row is a
gap a reader cannot see. Absent evidence is read the opposite way from an unknown startup floor,
though — fail-closed, because here the refusal is visible.

> **The distinction is the whole point of the field, because the two limits have different fixes.**
> Representability needs a **new** tool. Corroboration needs a **second** tool at the same field.
> A reader deciding whether to trust a row has to be told which one applies.

### Family status

| Family | Rungs | Evidence | Timing publishable? |
|---|---|---|---|
| Katsura | `katsura-4 … 11` | msolve 0.11.0 `input_files/kat6-31.ms`, generator for generator | **yes** |
| Cyclic (affine) | `cyclic-4 … 10` | msolve 0.11.0 `input_files/cyclic5-16.ms`, generator for generator | **yes** |
| Random MQ | `mq-random-6,10,14` | live Singular invariants; seeded, reproducible from the name | **yes** |
| Planted MQ | `mq-planted-6,10,14` | the planted point satisfies the **rendered text** | **yes** |
| Poseidon | `poseidon-t2-rf2-rp0/rp2-planted`, `poseidon-t2-rf4-rp0-planted` | planted target, from the cryptanalysis registry | **yes** |
| Anemoi | `anemoi64-cico-n1/n2-fcico` | **Groebner.jl only** — see below | **yes, uncorroborated** |
| Zero-dimensional FGLM workloads | Katsura, Cyclic, both MQ families | as above | **yes**, as `lex-basis-by-conversion` |
| Fukuoka MQ Type III | — | **excluded by licence**, not by effort — see below | n/a |
| Characteristic two | — | **blocked on a convention** — see §6 | no |

The upper rungs' evidence needs a word, because msolve ships `kat6-31.ms` and `cyclic5-16.ms` only
and there is no distributed file at eight variables or above. The `ComparandFile` evidence is
nonetheless the right record and not a stretch: it is evidence about the **construction**, which
every rung of a family shares (§5's opening), and the construction is one const-generic function
pinned against msolve's own bytes at `N = 6` and `N = 5`. What the upper rungs add on top is the
**invariant** check of §9 — `D = 2^(N−1)` exact at eight consecutive Katsura rungs, `924` at
`cyclic-7` against Backelin–Fröberg, and the dimension class at `cyclic-8` and `cyclic-9` against
Backelin's theorem. That is a second, independent anchor, and it is the one the upper rungs rest on.

**Six families**, which is the milestone's minimum, and
`test_the_corpus_covers_six_families_each_with_recorded_evidence` asserts both the count and that
each of the four kinds of evidence is actually used — so none of the vocabulary is dead.

### Anemoi's limit is corroboration, not representability

**Groebner.jl reaches Anemoi's field.** Its ceiling is `typemax(UInt64)` and it was measured
computing correctly at `2^31 − 1`, `2^32 − 5`, Goldilocks, `2^64 − 353` and `2^64 − 59`. Anemoi's
published parameters are over `2^64 − 353`, so the family **is** representable and a timing against
Groebner.jl **is** publishable.

What is missing is a *second* external engine. Sagebrush stops at `2^62` (its own gate,
`lib.rs:1552`) and msolve and Singular at `2^31`, so at Anemoi's field there is exactly one
external engine and nothing to check it against. Agreement is two-way — Zeebra against
Groebner.jl — and **cannot be triangulated**: a disagreement says one of the two is wrong without
saying which, where a three-way disagreement usually names the odd one out.

That is recorded as `Equivalence::SoleComparand`, and it is **derived** from §5a's bands rather
than asserted about this family, so the row is a consequence of a general fact.

An earlier draft of this document said no engine could represent the field. That was wrong, and
wrong in the direction that matters: it would have told a reader to wait for a new tool when what
is actually needed is a second one at the same field.

The Poseidon contrast still holds and is still luck. Poseidon's rows are over KoalaBear,
`2^31 − 2^24 + 1 = 2130706433`, which happens to sit **below every** comparand's ceiling, so those
rows are four-way corroborated. Nothing was designed for that and it does not generalize.

Note that for both, the corpus uses the **registry's** field and ignores the `characteristic`
argument. Poseidon's round constants come out of a seeded LFSR keyed on the prime and Anemoi's
depend on the smallest primitive root, so the same row over another prime is **another problem** —
the characteristic cannot be varied the way it can for Katsura.
`test_a_poseidon_rung_keeps_the_registrys_field_whatever_is_asked_for` pins that.

## 5a. The corroboration bands

The capability boundary, derived from four engine ceilings rather than written down per family.
`corpus::ceilings` holds the constants and `corpus::corroboration` is the function;
`test_the_corroboration_bands_follow_from_the_engine_ceilings` checks each band at a real field.

| band | engines that reach it | corroboration |
|---|---|---|
| `p < 2^31` | msolve, Singular, Groebner.jl, Sagebrush | **four-way** |
| `2^31 ≤ p < 2^62` | Groebner.jl, Sagebrush | **two-way**, neither checkable against a third |
| `2^62 ≤ p < 2^64` | Groebner.jl only | **none** |
| 254/255-bit | none | none |

**That table is the _basis_ table, and the other two tasks are narrower for reasons that are missing
tasks rather than field ceilings.** `corroboration_for(task, p)` is the task-aware form and
`corroboration(p)` is the basis shorthand; reading the second as the first overstates what can check
a conversion row by four engines to zero.

| task | engines that have it at all | why the others do not | `p = 32003` | `p < 2^31` | `p ≥ 2^31` |
|---|---|---|---|---|---|
| basis | all four | — | four-way | four-way | two-way |
| **conversion** | Singular, Sagebrush | msolve has no lex order; Groebner.jl 0.10.11 has no FGLM | **two-way** | **two-way** | **none** |
| eliminant | msolve, Singular | neither Sagebrush nor Groebner.jl has the task | **two-way** | sole engine above `1515531529` | none |

Two notes a reader needs before using the eliminant row. msolve's eliminant bound is `1515531529`,
below a tenth of its basis bound, which is what makes `32003` and `2^31 − 1` land in different cells.
And Zeebra's own adapter **used to refuse** `UnivariateEliminant`, on the stated ground that "no
comparand offers the task at all" — which was false, since msolve and Singular both do. #465 fixed
it: the eliminant is now served as a projection of an already-computed lex basis, adding no algorithm
and no strategy choice. So the two-way cell above is now a cell a Zeebra row can be ranked in, where
when this section was first written it could only corroborate an invariant between two external
engines.

The ceilings, each from the engine's own gate:

| engine | ceiling | source |
|---|---|---|
| msolve | `2^31` | `iofiles.c:564` |
| Singular | `2^31` | identical to msolve's |
| Sagebrush | `2^62` | `lib.rs:1552` |
| Groebner.jl | `typemax(UInt64)` | measured correct at `2^31 − 1`, `2^32 − 5`, Goldilocks, `2^64 − 353`, `2^64 − 59` |

Deriving this means a corrected ceiling corrects every statement that depends on it. The alternative
— a sentence per family — is how the Anemoi error got in.

Note where Zeebra's own fields fall: the corpus reference prime is four-way, KoalaBear is four-way,
**Goldilocks and Anemoi's `2^64 − 353` are both sole-engine**, and the 254/255-bit scalar fields
have nothing.

### Fukuoka MQ Type III is excluded by licence, and that is a justified variant

The instances are **"All Rights Reserved, no stated licence"** and must never be redistributed
(`docs/research/external-provenance-policy.md`). They are fetched locally by
`tools/fetch-mq-challenge.sh` into `ZEEBRA_MQ_DIR` and referenced by digest.

That is not a scheduling problem, it is structural: **a corpus entry cannot carry their system
text**, which is what every other entry here is. An entry would have to name the file and its
digest and build the instance at run time, so it would be a different shape from the generated
families and would not be reproducible for anyone who has not fetched the files. The two MQ
families in the corpus — random and planted — cover the same shape of problem with instances that
are freely reproducible from a seed, which is why they are the substitute and not a consolation.

Fukuoka III remains covered by the **cryptanalysis** scoreboard, where instances are referenced by
digest rather than carried, and that is the right home for it.

---

## 6. Characteristic two: `GF(2)` is a published identity, `GF(2^k)` is still blocked

### 6a. `GF(2)` is the corpus's third published characteristic, for Cyclic only (#427)

`corpus::BINARY_CHARACTERISTIC` is `2`, and the Cyclic rungs `cyclic-4` … `cyclic-10` each carry a
frozen digest there alongside their `GF(32003)` and `2^31 − 1` ones. It is the **cheapest reachable
external anchor** on Steel's page: his `GF(32003)` Cyclic 7 and Cyclic 8 carry `(Hom)` and are the
homogenized system, a different ideal, while the `GF(2)` block carries no such mark and so names the
affine system `benchmark_systems::cyclic` generates (`classical-benchmarks.md` §4).

**Publication is now per rung, not per characteristic**, and that change is #427's finding rather
than its convenience. A characteristic may only be published at where the rung's *invariants* are
true, and characteristic two is the first one where they are not simply the generic ones:

| rung | `2^31 − 1` / `32003` | `GF(2)` |
|---|---|---|
| `cyclic-4` | positive-dimensional, Krull 1 | **same** — Krull 1 |
| `cyclic-5` | zero-dim, `D = 70` | **same** — zero-dim, `D = 70` |
| `cyclic-6` | zero-dim, `D = 156` | **Krull dimension 2** |
| `cyclic-7` | zero-dim, `D = 924` (proved) | zero-dim, **`D = 728`** |
| `cyclic-8` | positive-dimensional, Krull 1 | **Krull dimension 3** |
| `cyclic-9` | positive-dimensional (Backelin) | **Krull dimension 2** |

So **Backelin's squarefree criterion is a characteristic-zero statement**: it predicts `cyclic-6`
zero-dimensional, and mod 2 it is not. `test_backelins_criterion_does_not_survive_the_reduction_mod_two`
is that assertion, and `corpus::DEGENERACIES` is where the per-characteristic invariants live —
sparse, because characteristic two and Cyclic are the whole of it. `CorpusEntry::zero_dimensional_at`
and `quotient_dimension_at` are the accessors a row must go through.

Katsura, random MQ and planted MQ are therefore **generated** at `GF(2)` and **not published**
there — the middle tier of §4's table, honest instances whose identity is not frozen and from which
no figure may be quoted. Katsura's generators carry coefficient 2, and `planted_point`'s `3 + 2i`
collapses to all-ones mod 2, which destroys the coordinate distinctness the planted family's oracle
depends on. `test_characteristic_two_is_published_for_cyclic_alone` pins the split.

**No published row adjoins the field equations.** `x^2 − x` is available over `GF(2)` and *changes
the ideal* — the README's phrasing is that field equations "make a quotient dimension count
base-field points" — and Steel's rows do not have them, so neither do these. A row that did would
carry `Instance::transformation`, which is inside the digest, so the two could never be confused for
one another; `test_no_published_row_carries_a_field_equation_transformation` is the guard. The
`D = 728` above is therefore a count over the algebraic closure with multiplicity, **not** a count of
`GF(2)`-points.

### 6b. `GF(2^k)` for `k > 1` is still blocked on a convention, not on effort

The reason is the one `FieldSpec` already encodes: two engines' default `GF(2^8)` need not be the
same ring. Different Conway or defining polynomials give isomorphic but not identical
representations, so a basis compared element by element across them disagrees for no mathematical
reason, and an invariant like the leading monomials can genuinely differ. #197 settled Zeebra's own
side of this by test — `Gf256` is the AES modulus and `Gf256Mq` the Fukuoka one, isomorphic and
explicitly not interchangeable — but that settles one engine, not a convention.

So an entry needs, for each engine: the defining polynomial it uses by default, how to override it,
and a verified statement that the override took. `FieldSpec::extension` requires the defining
polynomial for exactly this reason, and `SingularSolver::supports` returns
`Unsupported::ExtensionField` rather than guessing — which is the right behaviour until the
convention is established the way `tools/reference_bases.sing` establishes Singular's ordering and
printing conventions.

One concrete hazard is already on record from #262: a digest taken over Macaulay-matrix **entries
alone** could not tell `GF(2)` from `GF(2^8)` on Cyclic, because Cyclic's `±1` coefficients make
those matrices equal entry for entry. The corpus is not exposed to it — `Instance::canonical`
includes `FieldSpec::canonical`, so the characteristic and extension degree are inside the identity
digest, and `test_two_fields_with_identical_entries_digest_differently` pins the matrix-corpus side.

---

## 7. The ladder, and why rungs beat sizes

Rungs are `Easy`, `Intermediate`, `Challenging`. The reason to record the intent is that a table
whose every row is one difficulty says less than its row count suggests:

- a family represented only by instances every engine finishes in a millisecond measures process
  startup, and Julia's startup will dominate it;
- a family represented only by instances every engine times out on measures nothing at all, and
  produces a table of `StoppedByLimit` with no ratios in it.

`test_the_ladder_spans_its_difficulties` asserts each family carries at least an easy and an
intermediate rung, and that the ladder as a whole carries a challenging one — without which nothing
exercises `StoppedByLimit`, the outcome the protocol spends the most care on.

**#424 made `Challenging` mean something again, and reclassified `katsura-7` on the way.** The label
is defined as "expected to exhaust at least one engine's limits", and `katsura-7` exhausts none: all
five engines complete it, msolve and Sagebrush at their process floors. It was the top rung when it
was labelled, which is how the label came to mean "the largest one here" instead. It is now
`Intermediate`, and `Challenging` is `katsura-10`, `katsura-11`, `cyclic-8`, `cyclic-9` and
`cyclic-10` — the four that need minutes or refuse, plus the positive-dimensional one. Nothing about
any rung's *identity* changed: the `rung` field is a judgement about the ladder's shape and is not
part of the digest, so no frozen value moved.

---

## 8. The manifest

`corpus::manifest()` emits line-oriented ASCII, sorted, one row per rung **per identity** — so a
rung whose field varies appears twice and a registry rung once (§4b):

```
# zeebra cross-library corpus, characteristics [32003, 2147483647] order grevlex
# name family rung equivalence dimension variables characteristic digest
anemoi64-cico-n1-fcico anemoi easy sole-comparand zero-dimensional 2 18446744073709551263 c053c6ff0186e3b4…
anemoi64-cico-n2-fcico anemoi intermediate sole-comparand zero-dimensional 4 18446744073709551263 e3a6312e85c486b0…
cyclic-10 cyclic challenging comparand-file zero-dimensional 10 2147483647 df450bfc1886aa26…
cyclic-10 cyclic challenging comparand-file zero-dimensional 10 32003 538964ac3a891da6…
cyclic-4 cyclic easy comparand-file positive-dimensional 4 2147483647 e1d8d59448b3d648…
cyclic-4 cyclic easy comparand-file positive-dimensional 4 32003 e5a49df27c74d4d7…
cyclic-5 cyclic easy comparand-file zero-dimensional 5 2147483647 3274d14b224664ae…
cyclic-5 cyclic easy comparand-file zero-dimensional 5 32003 e80b7d8a6432b7d3…
cyclic-6 cyclic intermediate comparand-file zero-dimensional 6 2147483647 ed89afe173d16024…
cyclic-6 cyclic intermediate comparand-file zero-dimensional 6 32003 bf3bb57af08fcc94…
cyclic-7 cyclic intermediate comparand-file zero-dimensional 7 2147483647 30ce3b4f54c7b30e…
cyclic-7 cyclic intermediate comparand-file zero-dimensional 7 32003 18746449c45766c3…
cyclic-8 cyclic challenging comparand-file positive-dimensional 8 2147483647 a5eda0f9e2642ffe…
cyclic-8 cyclic challenging comparand-file positive-dimensional 8 32003 e2f6be738bd1f215…
cyclic-9 cyclic challenging comparand-file positive-dimensional 9 2147483647 ff4c2030a8f74d29…
cyclic-9 cyclic challenging comparand-file positive-dimensional 9 32003 ccffb9b3e5ca7b82…
katsura-10 katsura challenging comparand-file zero-dimensional 10 2147483647 67d6a96fadd21cc7…
katsura-10 katsura challenging comparand-file zero-dimensional 10 32003 c55e1bb74cf3e35c…
katsura-11 katsura challenging comparand-file zero-dimensional 11 2147483647 03bf44d5d614a21c…
katsura-11 katsura challenging comparand-file zero-dimensional 11 32003 c6802b0391f8394f…
katsura-4 katsura easy comparand-file zero-dimensional 4 2147483647 825a3aa54e152da5…
katsura-4 katsura easy comparand-file zero-dimensional 4 32003 c5fb073f5c9aceaa…
katsura-5 katsura easy comparand-file zero-dimensional 5 2147483647 6f305e37b2cc4ade…
katsura-5 katsura easy comparand-file zero-dimensional 5 32003 8be0a39d2d8c64ff…
katsura-6 katsura intermediate comparand-file zero-dimensional 6 2147483647 aa992992dfe29a23…
katsura-6 katsura intermediate comparand-file zero-dimensional 6 32003 a7bd9edf654af9e9…
katsura-7 katsura intermediate comparand-file zero-dimensional 7 2147483647 545cef6185ed10e4…
katsura-7 katsura intermediate comparand-file zero-dimensional 7 32003 c56bf75048b0fbae…
katsura-8 katsura intermediate comparand-file zero-dimensional 8 2147483647 b389774a0934503b…
katsura-8 katsura intermediate comparand-file zero-dimensional 8 32003 94d8b158719bdb10…
katsura-9 katsura intermediate comparand-file zero-dimensional 9 2147483647 9373c952e86d4a72…
katsura-9 katsura intermediate comparand-file zero-dimensional 9 32003 4010a392ecf953ea…
mq-planted-10 mq-planted intermediate known-solution zero-dimensional 10 2147483647 0eef4b55bce6fdc6…
mq-planted-10 mq-planted intermediate known-solution zero-dimensional 10 32003 74fc86970c3e5658…
mq-planted-14 mq-planted challenging known-solution zero-dimensional 14 2147483647 063f5b1ddbab6ef1…
mq-planted-14 mq-planted challenging known-solution zero-dimensional 14 32003 132bc0b85ac22d67…
mq-planted-6 mq-planted easy known-solution zero-dimensional 6 2147483647 55fb9b0622b6217a…
mq-planted-6 mq-planted easy known-solution zero-dimensional 6 32003 26932613e8ca565c…
mq-random-10 mq-random intermediate live-oracle zero-dimensional 10 2147483647 72d0ad315fc25409…
mq-random-10 mq-random intermediate live-oracle zero-dimensional 10 32003 16422dafcdb6487e…
mq-random-14 mq-random challenging live-oracle zero-dimensional 14 2147483647 029def705543e29b…
mq-random-14 mq-random challenging live-oracle zero-dimensional 14 32003 4e440cfac8426226…
mq-random-6 mq-random easy live-oracle zero-dimensional 6 2147483647 d98e5e5bf82b4618…
mq-random-6 mq-random easy live-oracle zero-dimensional 6 32003 bbfecd7f5522e203…
poseidon-t2-rf2-rp0-planted poseidon easy known-solution zero-dimensional 5 2130706433 f4cf6699cee835a6…
poseidon-t2-rf2-rp2-planted poseidon intermediate known-solution zero-dimensional 7 2130706433 3b3bfb037ceb32de…
poseidon-t2-rf4-rp0-planted poseidon challenging known-solution zero-dimensional 9 2130706433 95cec79371a8751a…
```

**Twenty-six rungs across six families, forty-seven identities.** Twenty-one rungs carry two (the
two published characteristics) and five carry one (the registry rows, whose field is their own). `test_the_manifest_lists_every_rung_with_its_digest` checks the row count against
`digests.len()` summed over the ladder, so the manifest and the frozen table cannot disagree about
how many problems the corpus holds, and asserts every digest in it is distinct. Digests are
abbreviated above; the manifest carries all 64 hex digits.

The characteristic is a **column** rather than a document per field, so one sorted table carries the
whole corpus and a reader can see at a glance which rungs have two identities and which have one.

Line-oriented and ASCII so another language's harness can read it and a digest can be reproduced by
hand — the same property that makes `Instance::canonical` reproducible outside Rust.

The digests are also frozen as constants in `corpus::ladder()`, and
`test_the_manifest_is_frozen` compares the two. **A failure there is the point of the field**: it
means the generated system changed, which means every figure ever taken against the old digest is a
figure about a different problem. The fix is to decide whether the change was intended before
touching the constant, not after.

---

## 9. The invariants, and where the ceiling is

`classical-benchmarks.md` §6's one concrete follow-up was "add a regression test asserting them",
and §9 recorded that it had not been done: "nothing asserts it. A generator that drifted — an
off-by-one in the cyclic window, a sign in Katsura — would change `D` and currently nothing would
notice." `CorpusEntry::quotient_dimension` is that assertion, and `dim_F(R/I)` is the cheapest
external-correctness check the crate has: machine-independent, library-independent and
clock-independent, which is why it is a stronger anchor than any timing.

| family | `D` | source | asserted by |
|---|---|---|---|
| Katsura `N = 4 … 11` | `2^(N−1)` = 8 … 1024 | **measured** exact at eight consecutive rungs; no primary source for the closed form was located (§3.2, §9 of `classical-benchmarks.md`) | `test_katsuras_quotient_dimension_is_two_to_the_n_minus_one` |
| Cyclic `n = 5, 6` | 70, 156 | Björck–Fröberg | `test_the_cyclic_quotient_dimensions_are_the_published_counts` |
| Cyclic `n = 7` | **924** | Backelin–Fröberg, proved exactly | same |
| Cyclic `n = 10` | **34940** | Steel's page, verbatim: "the quotient … has dimension 34940 as a vector space" | same |
| Cyclic `n = 4, 8, 9` | absent | **Backelin's theorem**: `d² \| n` for `d ≥ 2` gives infinitely many cyclic `n`-roots | `test_a_cyclic_rung_is_zero_dimensional_exactly_where_n_is_squarefree` |
| Planted MQ | `2^N` | by construction, two roots per coordinate pair | `test_planted_mqs_quotient_dimension_is_two_to_the_n` |
| Random MQ, Poseidon, Anemoi | 57, 354; 9, 81, 81; 5, 25 | the board, all five engines agreeing | the frozen record |

`None` means **absent, not zero**. A positive-dimensional ideal has no finite quotient, and
`Invariants::agree` compares only fields both sides carry — so an engine reporting no dimension and
an engine reporting none agree without either claiming anything.

**Backelin's theorem is the cyclic family's dimension class, as arithmetic.** It is what makes
`cyclic-4`, `cyclic-8` and `cyclic-9` positive-dimensional *for a published reason* rather than as
three local observations, and it is checkable **without computing a basis** — which matters, because
`cyclic-9` is precisely the rung Zeebra cannot reach.

Two sides are checked, deliberately. The tests above compare the record against the **literature**;
`test_every_cheap_rungs_recorded_quotient_dimension_is_computed` and its `#[ignore]`d companion
`test_the_upper_rungs_quotient_dimensions_are_computed` compare it against the **code**, by parsing
each rung's own rendered text, computing a grevlex basis and enumerating standard monomials. A
transcription error in the table therefore cannot hide behind a formula written from the same table.
All eight upper rungs verify in 334 s under `--release`.

### Where the ceiling is, and which stage sets it

Measured at the reference prime under grevlex at `F4Options::default()`. The answer is **not** where
the family index is largest:

| rung | basis, pre-#575 default | basis, post-#575 default | `D` | conversion |
|---|---:|---:|---:|---:|
| `katsura-8` | 0.22 s | **53 ms** | 128 | 13 ms |
| `katsura-9` | 2.1 s | **419 ms** | 256 | 84 ms |
| `katsura-10` | 21.8 s | **3.53 s** | 512 | 0.62 s |
| `katsura-11` | 277 s | **33.6 s** | 1024 | 5.2 s |
| `cyclic-7` | 1.4 s | **666 ms** | 924 | 0.16 s |
| `cyclic-8` | 21.3 s | 25.9 s | — (positive-dimensional) | n/a |
| `cyclic-9` | **refuses** | **refuses** | — | — |
| `cyclic-10` | **refuses** | **refuses** | — | — |

**The second column is an upper bound and not a figure.** #575 moved both interreduction defaults,
so the first column no longer describes `F4Options::default()` and the ladder had to be re-walked.
The re-walk ran at a **one-minute load average of 983** on this 128-thread box — other agents'
linkers, which `tools/benchlock.sh` does not serialize because they are builds and not measurements.
Load inflates a wall time and cannot deflate one, which is the only reason these numbers are usable:
every one of them is an **upper** bound, so a rung that fits a budget here fits it on a quiet box.
No ratio is taken from them and none should be.

The two refusals are not upper bounds but exact: `cyclic-9` at 20 001 315 live nonzero entries and
`cyclic-10` at 20 000 254, against the 20 000 000 limit. An entry count crosses at the same counter
whatever the box is doing, which is the property §9 is built on, and it is why the ceiling survived a
default change that moved every reachable rung by 4x to 8x.

**The ceiling is `cyclic-9`, and the stage that sets it is the F4 basis**, crossing the live-entry
budget: `TooManyNonzeros { nonzeros: 20000001, limit: 20000000 }`. The whole Katsura ladder is
reachable to `katsura-11` — four rungs above the old ceiling, at roughly 10x per rung — so the
expectation in #424 that "this issue may well resolve as the ceiling is here" was right about the
*shape* and wrong about the *place*: Katsura did not run out, Cyclic did.

That the refusal is a **resource** stop and not a wall-clock one is the point rather than a detail.
An entry count crosses at the same counter on any machine, so the ceiling can be written down; a
time stop would make it a fact about how busy the box was. `F4Options`' own `StopKind` draws exactly
that distinction, and `test_the_ceiling_is_cyclic_9_and_the_basis_stage_sets_it` asserts the kind and
not only the fact. It also asserts that `katsura-11` still completes — so a regression that moved the
ceiling down is a failure, and one that moved it *up* is a failure too, with a message saying the
result needs writing up rather than the assertion relaxing.

The timings in the table are from the development workstation with other agents at work on it.
**They bound reachability and nothing else**: no cross-engine ratio is taken from them, and
`classical-benchmarks.md` §4's prohibition on comparing against Steel's 2004 figures stands
untouched — Steel's page is used here for the instance list and the checkable invariants only.

A refusal is a **result**, which is why `cyclic-9` and `cyclic-10` are on the ladder rather than left
off. `cyclic-10`'s `D = 34940` is the published value the rung exists to one day be checked against,
and both rungs' dimension class comes from Backelin rather than from a computation — the record says
so in each entry.

---

### 9a. #489: the budget for sweeping the upper rungs onto the board

#489 asked for three decisions **before** the run, on the grounds that the rows would otherwise not
be worth their cost. Here they are, with what decides each.

**1. The budget: the board's standard 60 s wall, unchanged, for all eight rungs.**

#489's premise was that this would not do — "a 60 s wall makes `katsura-10` and up uninformative" —
and that premise was true of the default it was written against. It is **false now**. Under #575's
defaults the slowest reachable upper rung is `katsura-11` at **33.6 s** and the slowest of all is
`cyclic-8` at 25.9 s, both measured as upper bounds at load 983 (§9). A budget that the slowest rung
clears by 1.8x with the box under a 1 000-fold load clears it on a quiet one.

So no per-rung budget is needed, and the sweep does not need the 600 s wall #489 feared would cost
"most of a day". That is a consequence of #575 rather than a discovery about the budget: the rungs
got 4x to 8x cheaper and walked under the existing wall.

**2. Deterministic limits where the answer is a refusal: already satisfied, and not by the wall.**

#489 wanted a resource limit rather than a wall wherever the result is a refusal, because an entry
count crosses at the same counter on any machine. Both refusing rungs already do exactly that:
`cyclic-9` and `cyclic-10` stop on `max_live_nonzeros` at 20 001 315 and 20 000 254 entries, and
would stop there at **any** wall. The board's `Limits` being wall-shaped — which #489 names as "the
thing in the way" — turns out not to be in the way for these eight rungs, because the wall never
binds: it is never reached by the rungs that complete, and never consulted by the rungs that refuse.

It would be in the way for a rung that is merely *slow*, and none of the eight is. Changing
`Limits` is therefore not this sweep's prerequisite, and the issue that wants it should be filed
from a rung that needs it.

**3. The reference prime only, and this is a decision rather than an omission.**

`GF(32003)` is not swept for the upper rungs. The lower ladder measured the two published
characteristics as differing by less than noise (§4b-i), and the upper rungs double the most
expensive part of the sweep to re-establish that. The reference prime `2^31 − 1` is the one every
retained upper-rung figure in §9 was taken at, so sweeping it keeps the board and this document on
one identity.

What that forgoes: `cyclic-9`'s and `cyclic-10`'s refusals are **entry-count** refusals, and an
entry count is a function of the field's representation width. At a 16-bit prime the same ideal might
fit the same 20 000 000-entry budget. That is a real and unmeasured question, and it is the one
reason to revisit this decision — not a suspicion that the timings would differ.

### 9b. What #489 still needs, and why it is not here

**The sweep itself.** The three decisions above are what #489 asked to settle first; the rows are not
taken, because this box could not produce an honest one. Over the hour the sweep was attempted the
one-minute load average ran **592 → 1 261 and rising**, from other agents' `ld.mold` linkers, and
`benchlock` serializes measurements rather than builds — so the lock gives a sweep no protection
against it.

Under that load a 60 s wall stops producing a measurement and starts producing an artefact: an
engine that needs 20 s reports a `StoppedByLimit` it would never hit on a quiet box, and a
wall-clock stop written onto the board is the weakest row the protocol defines. Two attempts were
killed for this rather than committed.

So the sweep is a quiet-box task and the budget above is what it should use. Nothing about it is
uncertain any more except when the machine is free.

## 10. Adding a family

1. Generate it from an existing `benchmark_systems` or `research` generator — never a second
   definition, which would drift. `corpus::text_instance` renders through
   `differential::polynomial_to_string`, the renderer whose output Zeebra's own parser and
   Singular both accept.
2. Name it by **variable count** — unless it comes from the cryptanalysis registry, in which case
   it keeps its **registry id**, which is its identity everywhere else in the crate and must not be
   renamed to suit a convention local to the corpus. `test_every_ladder_entry_builds_and_the_
   generated_families_are_named_by_variable_count` enforces both halves.
3. Add a match arm to `corpus::instance` and an entry to `corpus::ladder`. The arm is deliberate
   friction: a size nobody wrote down is a size nobody checked the equivalence of. If the family is
   const-generic in the field, generate it through `over_prime!` so the declared characteristic is
   the generated one (§4a) — never over a fixed field with the characteristic passed only to the
   `FieldSpec`.
4. Write an equivalence test against a second engine's own literal, as §2 and §3 do. If no second
   engine ships that family, verify against Singular live and record the invariants.
5. Record its dimension. If it is positive-dimensional, say which tasks do not apply.
6. Freeze its digest, and only then publish a timing.
