# The cross-library corpus: the same ideal in every engine, and the two ways that silently fails

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

## 4. The reference field, and why it is not wider

`REFERENCE_CHARACTERISTIC = 2^31 − 1`.

msolve caps at `p ≤ 2^31 − 1` and Singular is identical (`MAX_CHARACTERISTIC = 1 << 31`, checked
`>=`). So `2^31 − 1` is the **largest prime every engine in the comparison accepts**, and a corpus
keyed on anything wider would render most of the table `Unsupported` and measure nothing.

This is a constraint on the comparison, not on Zeebra, and the protocol document's §3 records what
it costs: Zeebra's 32–64-bit fields have only Groebner.jl and Sagebrush as comparands, and its
254/255-bit fields have none at any size. Those rows say so rather than being omitted.

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

> **The distinction is the whole point of the field, because the two limits have different fixes.**
> Representability needs a **new** tool. Corroboration needs a **second** tool at the same field.
> A reader deciding whether to trust a row has to be told which one applies.

### Family status

| Family | Rungs | Evidence | Timing publishable? |
|---|---|---|---|
| Katsura | `katsura-4,5,6,7` | msolve 0.11.0 `input_files/kat6-31.ms`, generator for generator | **yes** |
| Cyclic (affine) | `cyclic-4,5,6` | msolve 0.11.0 `input_files/cyclic5-16.ms`, generator for generator | **yes** |
| Random MQ | `mq-random-6,10,14` | live Singular invariants; seeded, reproducible from the name | **yes** |
| Planted MQ | `mq-planted-6,10,14` | the planted point satisfies the **rendered text** | **yes** |
| Poseidon | `poseidon-t2-rf2-rp0/rp2-planted`, `poseidon-t2-rf4-rp0-planted` | planted target, from the cryptanalysis registry | **yes** |
| Anemoi | `anemoi64-cico-n1/n2-fcico` | **Groebner.jl only** — see below | **yes, uncorroborated** |
| Zero-dimensional FGLM workloads | Katsura, Cyclic, both MQ families | as above | **yes**, as `lex-basis-by-conversion` |
| Fukuoka MQ Type III | — | **excluded by licence**, not by effort — see below | n/a |
| Characteristic two | — | **blocked on a convention** — see §6 | no |

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

## 6. Characteristic two is blocked on a convention, not on effort

`GF(2^k)` for `k > 1` is **not** in the corpus, and the reason is the one `FieldSpec` already
encodes: two engines' default `GF(2^8)` need not be the same ring. Different Conway or defining
polynomials give isomorphic but not identical representations, so a basis compared element by
element across them disagrees for no mathematical reason, and an invariant like the leading
monomials can genuinely differ.

So an entry needs, for each engine: the defining polynomial it uses by default, how to override it,
and a verified statement that the override took. `FieldSpec::extension` requires the defining
polynomial for exactly this reason, and `SingularSolver::supports` currently returns
`Unsupported::ExtensionField` rather than guessing — which is the right behaviour until the
convention is established the way `tools/reference_bases.sing` establishes Singular's ordering and
printing conventions.

`GF(2)` itself is not affected: it is a prime field and `Zp2` already exercises it.

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

---

## 8. The manifest

`corpus::manifest()` emits line-oriented ASCII, sorted, one row per rung:

```
# zeebra cross-library corpus, characteristic 2147483647 order grevlex
# name family rung equivalence dimension variables digest
anemoi64-cico-n1-fcico anemoi easy sole-comparand zero-dimensional 2 c053c6ff0186e3b4…
anemoi64-cico-n2-fcico anemoi intermediate sole-comparand zero-dimensional 4 e3a6312e85c486b0…
cyclic-4 cyclic easy comparand-file positive-dimensional 4 e1d8d59448b3d648…
cyclic-5 cyclic easy comparand-file zero-dimensional 5 3274d14b224664ae…
cyclic-6 cyclic intermediate comparand-file zero-dimensional 6 ed89afe173d16024…
katsura-4 katsura easy comparand-file zero-dimensional 4 825a3aa54e152da5…
katsura-5 katsura easy comparand-file zero-dimensional 5 6f305e37b2cc4ade…
katsura-6 katsura intermediate comparand-file zero-dimensional 6 aa992992dfe29a23…
katsura-7 katsura challenging comparand-file zero-dimensional 7 545cef6185ed10e4…
mq-planted-10 mq-planted intermediate known-solution zero-dimensional 10 0eef4b55bce6fdc6…
mq-planted-14 mq-planted challenging known-solution zero-dimensional 14 063f5b1ddbab6ef1…
mq-planted-6 mq-planted easy known-solution zero-dimensional 6 55fb9b0622b6217a…
mq-random-10 mq-random intermediate live-oracle zero-dimensional 10 72d0ad315fc25409…
mq-random-14 mq-random challenging live-oracle zero-dimensional 14 029def705543e29b…
mq-random-6 mq-random easy live-oracle zero-dimensional 6 d98e5e5bf82b4618…
poseidon-t2-rf2-rp0-planted poseidon easy known-solution zero-dimensional 5 f4cf6699cee835a6…
poseidon-t2-rf2-rp2-planted poseidon intermediate known-solution zero-dimensional 7 3b3bfb037ceb32de…
poseidon-t2-rf4-rp0-planted poseidon challenging known-solution zero-dimensional 9 95cec79371a8751a…
```

Nineteen rungs across six families. Digests are abbreviated above; the manifest carries all 64
hex digits.

Line-oriented and ASCII so another language's harness can read it and a digest can be reproduced by
hand — the same property that makes `Instance::canonical` reproducible outside Rust.

The digests are also frozen as constants in `corpus::ladder()`, and
`test_the_manifest_is_frozen` compares the two. **A failure there is the point of the field**: it
means the generated system changed, which means every figure ever taken against the old digest is a
figure about a different problem. The fix is to decide whether the change was intended before
touching the constant, not after.

---

## 9. Adding a family

1. Generate it from an existing `benchmark_systems` or `research` generator — never a second
   definition, which would drift. `corpus::text_instance` renders through
   `differential::polynomial_to_string`, the renderer whose output Zeebra's own parser and
   Singular both accept.
2. Name it by **variable count** — unless it comes from the cryptanalysis registry, in which case
   it keeps its **registry id**, which is its identity everywhere else in the crate and must not be
   renamed to suit a convention local to the corpus. `test_every_ladder_entry_builds_and_the_
   generated_families_are_named_by_variable_count` enforces both halves.
3. Add a match arm to `corpus::instance` and an entry to `corpus::ladder`. The arm is deliberate
   friction: a size nobody wrote down is a size nobody checked the equivalence of.
4. Write an equivalence test against a second engine's own literal, as §2 and §3 do. If no second
   engine ships that family, verify against Singular live and record the invariants.
5. Record its dimension. If it is positive-dimensional, say which tasks do not apply.
6. Freeze its digest, and only then publish a timing.
