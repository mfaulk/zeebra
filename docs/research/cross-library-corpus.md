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

So msolve names by variable count and agrees with Zeebra's type parameter. **The corpus is named by
variable count throughout, and the literature's `n` appears nowhere in it.** A test asserts that
every ladder entry's trailing number equals its built variable count, so a future entry cannot
reintroduce the ambiguity by being named carelessly.

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

## 5. Family status: what may be published

| Family | Instances | Equivalence verified against | Timing publishable? |
|---|---|---|---|
| Katsura | `katsura-4,5,6,7` | **msolve's own `kat6` literal**, generator for generator | **yes** |
| Cyclic (affine) | `cyclic-4,5,6` | **msolve's own `cyclic5` literal**, generator for generator | **yes** |
| Random MQ | — | not yet generated | no |
| Planted MQ | `benchmark_systems::planted` exists | not yet converted to an `Instance` | no |
| Fukuoka MQ Type III | parsed by `research::mq` from `ZEEBRA_MQ_DIR` | not yet converted; **not redistributable** | no |
| Poseidon | in the cryptanalysis registry | not yet converted to an `Instance` | no |
| Anemoi | in the cryptanalysis registry | not yet converted to an `Instance` | no |
| Zero-dimensional FGLM workloads | Katsura and Cyclic cover this | as above | **yes**, as `lex-basis-by-conversion` |
| Characteristic two | — | **blocked**: see §6 | no |

The four "not yet converted" rows are honest status, not oversight. Each needs a conversion from an
existing generator into the `Instance` text form, and each conversion is a place the ideal can
change silently — so each gets its own equivalence test against a second engine before any figure
is published. Doing four of those badly is worse than doing two of them properly.

**Fukuoka MQ carries an extra constraint.** The instances are "All Rights Reserved, no stated
licence" and **must never be redistributed** (`docs/research/external-provenance-policy.md`). They
are fetched locally by `tools/fetch-mq-challenge.sh` into `ZEEBRA_MQ_DIR` and referenced by digest.
A corpus entry for them therefore cannot carry the system text — it has to name the file and its
digest and build the instance at run time, which is a different shape from the generated families
and is why it is not bolted on here.

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
# name family rung dimension variables digest
cyclic-4 cyclic easy positive-dimensional 4 e1d8d59448b3d648…
cyclic-5 cyclic easy zero-dimensional 5 3274d14b224664ae…
cyclic-6 cyclic intermediate zero-dimensional 6 ed89afe173d16024…
katsura-4 katsura easy zero-dimensional 4 825a3aa54e152da5…
katsura-5 katsura easy zero-dimensional 5 6f305e37b2cc4ade…
katsura-6 katsura intermediate zero-dimensional 6 aa992992dfe29a23…
katsura-7 katsura challenging zero-dimensional 7 545cef6185ed10e4…
```

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
2. Name it by **variable count**.
3. Add a match arm to `corpus::instance` and an entry to `corpus::ladder`. The arm is deliberate
   friction: a size nobody wrote down is a size nobody checked the equivalence of.
4. Write an equivalence test against a second engine's own literal, as §2 and §3 do. If no second
   engine ships that family, verify against Singular live and record the invariants.
5. Record its dimension. If it is positive-dimensional, say which tasks do not apply.
6. Freeze its digest, and only then publish a timing.
