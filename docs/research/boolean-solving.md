# Boolean solving readiness: what works in characteristic two, and what the blocker actually was

Reference for #218 (G2), a child of the Boolean epic #196. **The headline result is a negative one
in the useful direction: the Gröbner stack already works in characteristic two, and nothing had to
change for it to.** The issue was written expecting a list of failures and said so — "Report what
breaks, in detail. A list of concrete failures is the most valuable possible output of this issue."
There are none at the pipeline level. The real gaps were elsewhere, and one of them is a correctness
hazard that nothing had noticed.

**Written in four passes.** §1–§5 are the first (#233): the stale blocker, the pipeline result, the
`0x11D` hazard, and the field-equation mechanism. §6–§10 are the second (#379), which asserted the
*solving* half the first pass left out, answered questions 4 and 5, and found three gaps — one of
them a panic on any text input over `GF(2^8)`. §13 is the third: that panic is **closed** (#377),
and §13 records the trait-level decision it turned on. §14 is the fourth: the differential oracle
now reaches `GF(2^8)` (#378), with the minimal polynomial asserted to agree on both sides rather
than conventionally shared — which is what §4's `0x11B`/`0x11D` hazard turns into once two
implementations have to talk. §9 is why the issue is still open: question 3's measurement was
deliberately not taken.

## 1. The blocker everyone was waiting on had already cleared

Five issues were scoped against a claim that was false when they were written.
`docs/research/additional-benchmarks.md` §5 (moved out in #668) said LowMC was "**Blocked, and on an interface rather
than on mathematics**… `src/fields/mod.rs` declares `mod binary_field;` — private, not exported";
`docs/research/fukuoka-mq.md` §1 (moved out in #668) marked four Fukuoka types "**no** — … is private"; `MqField::Gf2`
and `MqField::Gf256` refused with "**Not importable yet**: … is private".

The export landed in `8757b4a` (2026-11-05). `src/fields/mod.rs` has `pub use` for
`BinaryFieldElement`, `ExtensionFieldElement` and `IrreduciblePolynomial`, with `pub type Gf256` and
`pub type Gf32` beside them. It arrived as a **side effect of #123's `for_each_field!` work** rather
than as a deliberate unblocking, which is why nothing downstream noticed and why every document kept
citing it.

Worth recording as a process point rather than only a fact: a false blocker is more expensive than a
true one, because the issues sequenced behind it do not get re-examined. The export was reachable
through `zeebra::fields::BinaryFieldElement` for a day before five issues were written saying it was
not.

**One of those claims was load-bearing in a test.**
`grobner::research::mq::tests::test_the_binary_and_extension_fields_are_refused_by_name` (moved out in #668) asserted
`because.contains("not publicly exported")`, so the stale reason was pinned by the suite and would
have survived any amount of documentation editing. It now asserts the accurate reason *and* that the
stale phrase is absent, so the claim cannot come back.

Corrected: `docs/research/fukuoka-mq.md` §1 and §6 (moved out in #668), `docs/research/additional-benchmarks.md` §5 (moved out in #668) (as
a dated "superseded" note rather than a silent edit, since the section's reasoning is still worth
reading), `MqField`'s two variant doc comments, and the two `MqError::UnsupportedField` reason
strings.

## 2. `GF(2)` never needed `binary_field` at all

`PrimeFieldElement32<2>` and `PrimeFieldElement64<2>` work, and the README already recorded why:
`P = 2` keeps the wide-remainder multiplication path rather than reaching Montgomery form, because
`2^64` is not invertible modulo an even number, and the branch is on the const generic so it is
resolved at compile time.

Declared as `fields::Zp2`, with a doc comment saying it is the one declared modulus that is not odd.
Which of `Zp2` and `BinaryFieldElement<0b11>` the Fukuoka importer should use was left open by the
first pass and is **decided in §8: `Zp2`**.

## 3. The pipeline works in characteristic two

`grep -rl "BinaryFieldElement\|ExtensionFieldElement" src/grobner/ src/linalg/` was empty before
this issue. The arithmetic was tested and heavily optimized — M19-B took a `GF(2^63)` multiply from
212.70 ns to 2.02 ns with `PCLMULQDQ` and Barrett reduction — but F4, FGLM, `solve_one` and the
echelon backends had never been run over an even-characteristic field.

`grobner::tests::test_the_whole_pipeline_over_gf2` and `..._over_gf256` are modelled exactly on the
existing `test_the_whole_pipeline_over_bn254_fr`: a planted system through F4, the basis checked
against Buchberger's criterion **and** asserted equal to the classical engine's, FGLM to lex, the
converted basis asserted equal to a direct lex F4, then `solve_one` with the recovered point
re-evaluated against the original system rather than against the basis it came from.

**Both passed on the first run, with no change to any solver code.** The stack is generic over
`FiniteField` and the genericity held, which is what `test_the_grobner_stack_needs_no_field_cardinality`
was protecting. The suspects named in #218's question 1 — Montgomery form bypassed at `P = 2`,
`legendre_symbol` reporting every element a square, `sqrt` degenerating to `x^(q/2)`, no two-adicity
when `q` is a power of two — are all real properties of characteristic two, and none of them is on
the path this pipeline takes.

That is a genuine result and it should be read narrowly: the pipeline *completes and returns verified
points* on these systems. It says nothing about scale, nothing about the published instances, and
nothing about whether the answers mean what a cryptanalyst wants — which is §5.

### 3.1 `planted` degenerates in characteristic two, and the test that was almost wrong because of it

Found while writing §3, and the more useful half of it. `benchmark_systems::planted` emits, per
variable pair, `x_i^2 + x_{i+1}^2 - (a^2 + b^2)`. In characteristic two `x^2 + y^2 = (x + y)^2`, so
that generator is `((x_i + x_{i+1}) - (a + b))^2` — **a perfect square**, and the ideal it generates
is **not radical**.

So the characteristic-two pipeline test is not the same test as its odd-characteristic twin: it asks
the solver to recover a point from a nonradical ideal, which is strictly harder. It passes anyway.

`grobner::tests::test_planted_degenerates_to_a_square_in_characteristic_two` asserts the factorization
over `Gf256` and asserts that the same construction over `Zp2147483647` is **not** a square, so the
claim is pinned as a fact about the characteristic rather than about `planted`'s shape. It is a test
rather than a comment because a reader who assumed `planted` behaves uniformly would mis-read every
characteristic-two measurement taken with it — including the ones in §3.

## 4. `GF(2^8)` is two fields, and the challenge does not use the one Zeebra had

The correctness hazard. <https://www.mqchallenge.org/format.html> (read 2026-11-06) specifies the
Fukuoka `GF(2^8)` as

> `p(x) = x^8 + x^4 + x^3 + x^2 + 1`

`0x11D`. `fields::Gf256` was `BinaryFieldElement<X8_X4_X3_X_1>` = `0x11B`, **the AES polynomial** —
one bit apart, `x` where the challenge has `x^2`. Both irreducible of degree eight; the fields are
isomorphic; **the arithmetic is different**, because the reduction is modulo different polynomials.

Reading type II or type V coefficient bytes under `Gf256` would therefore construct a different
system from the published one, with nothing about the result looking wrong. This is precisely the
class of error `docs/research/fukuoka-mq.md` §2.1 (moved out in #668) guarded against for the monomial layout, which was
"verified rather than assumed" — the layout was checked at the time because a type III instance was
being imported, and the field representation was not, because no `GF(2^8)` instance was.

An order check cannot catch it: both fields have order 256, so `check_coefficient_field`'s
`F::order_limbs() != [declared]` test accepts either. Order determines a *prime* field; it does not
determine a non-prime one.

Added: `X8_X4_X3_X2_1` in `irreducible_polynomials.rs`, certified by
`binary_field::tests::test_declared_moduli_are_irreducible` (Rabin's test, as for the others), and
`fields::Gf256Mq` as the type. The distinction is asserted by
`binary_field::tests::test_the_two_degree_eight_moduli_are_different_fields`:

| check | value |
|---|---|
| `0x57 * 0x83` over `0x11B` | `0xc1` — the worked example in FIPS-197 §4.2 |
| `0x57 * 0x83` over `0x11D` | not `0xc1` |
| nonzero operand pairs of 65025 that differ | **more than 50 000** |

The AES anchor matters: taking the expected value from a published standard rather than from this
crate's own output is what makes the inequality evidence about the moduli instead of about the
implementation. The products are additionally cross-checked against an independent reduction —
carry-less multiply by shift-and-xor, then subtract shifted copies of the modulus bit by bit — which
shares no code with the shipped `PCLMULQDQ`-and-Barrett path, and which reproduces the AES value too
so it is not tuned to one modulus.

Not every pair separates the two fields, and the test says why rather than only asserting a
threshold: when the carry-less product already has degree below 8 there is nothing to reduce and both
moduli return it unchanged. Every product by 1 is such a case.

## 5. Field equations, and the rule for when they pay

A system over `F_q` has two solution sets and cryptanalysis wants the second: the points of the
variety over the algebraic closure, which is what an ideal in `F_q[x]` describes, and the points with
coordinates **in `F_q` itself**. The second is cut out by adjoining `x_i^q - x_i`.

Nothing in `src/grobner/` did this, and — worse — nothing refused to proceed without it, so a
`GF(2)` measurement taken before this issue would have been silently about the wrong ideal and every
published solving degree would have been incomparable. `grobner::field_equations` now provides
`field_equations`, `with_field_equations` and `rational_points_by_enumeration`.

**The consequence that makes it worth having is radicality.** `x^q - x` is squarefree and splits
completely over `F_q`, so `dim F_q[x]/(I + <x_i^q - x_i>)` is *exactly* the number of `F_q`-rational
points — counted once each, however many times they occur in `I`. A solution count becomes a
machine-independent invariant, in the role `docs/research/additional-benchmarks.md` §3.2 (moved out in #668) gives
Anemoi's quotient dimension.

`the_quotient_dimension_counts_gf2_points_only_with_field_equations` checks it against a comparand
that cannot be wrong: six random quadratics in eight Boolean variables with a planted solution, and
**exhaustive enumeration over all 256 assignments**. Measured:

| | |
|---|---|
| generators, bare | 6 |
| generators, with field equations | 14 |
| `GF(2)`-rational points, by enumeration | 2 |
| `dim F_2[x]/I` with field equations | **2** |
| bare ideal | **positive-dimensional** — FGLM does not apply to it at all |

The bare case is the honest illustration of the problem: six quadratics in eight variables are
underdetermined, so without field equations there is no quotient dimension to compare and no
zero-dimensional solve to attempt. With them there are two points and a quotient of dimension two.

The exhaustive-enumeration oracle is the design choice worth keeping. It is complete, trivially
correct, internal to the crate, and independent of the differential oracle — so it would have held
this result up even if §7 had found Singular unusable in characteristic two. It is also **prime
fields only**, for the reason §10 gives.

### 5.1 The rule

**Adjoining field equations is a judgement about `q`, not a default, and the module declines to
choose.** The generator has degree `q`, so it pays only when `q` is below the degree the computation
would reach anyway:

| field | field-equation degree | solving degrees actually measured | worth it |
|---|---:|---|---|
| `GF(2)` — Fukuoka I/IV, LowMC, HFE, SAT4CryptoBench | 2 | — | **yes, essentially always** |
| `GF(2^8)` — Fukuoka II/V | 256 | — | no |
| `GF(31)` — Fukuoka III/VI | 31 | 4 to 9 (`docs/research/fukuoka-mq.md` §4 (moved out in #668)) | **no** |
| `GF(65521)` — Courtois MinRank A–C (#205) | 65521 | — | never |

So the families this importer reaches **today** are exactly the ones that do not want field
equations, and the families that want them are the ones not yet importable. That is worth stating
plainly because it would otherwise look like the mechanism is unused.

`field_equations` refuses outright only when `q` exceeds a monomial exponent — `Monomial` stores
exponents as `u32` — returning `FieldEquationError::OrderNotRepresentable` as a value. That is a
representation limit rather than a policy, and it is the same answer a caller over BN254 would reach
more slowly.

The alternative mechanism named in #218's question 2 — reducing exponents modulo `x^q - x` inside
monomial arithmetic, as PolyBoRi does with a ZDD over `GF(2)` — is faster and changes what `Monomial`
means. **Not taken**, and recorded as a separate decision rather than deferred silently.

## 6. The solving half, which the first pass did not assert

§5 took the `GF(2)` field-equation ideal as far as a **quotient dimension** and stopped. That is the
counting result; it is not the result #219 needs. A SAT comparison needs *points*, so the question is
whether FGLM converts an ideal that has `x_i^2 - x_i` among its generators and whether the search
then returns a point of the **original** system rather than of the extended one. Neither was
asserted. Both now are, in `tests/boolean_readiness.rs`, against the same 256-assignment enumeration
§5 uses — so the oracle is still one that cannot be wrong.

| claim over `GF(2)`, 6 quadratics in 8 variables, seed 9 | result |
|---|---|
| `fglm_to_lex` on the field-equation ideal | converts; the output is a lex Gröbner basis |
| `solve_one` | returns a point, and it is one of the two the enumeration found |
| that point re-evaluated against the **bare** system | vanishes |
| `solve_zero_dimensional` against enumeration | **equal as sets** — both points, no others |

The set equality is the one worth having. Recovering *a* point is passed by a solver that drops a
solution or invents one over an extension; recovering exactly the enumerated set is not.

`GF(2^8)` is exercised too, and two of those results are new rather than confirmatory:

- **`roots` works over `GF(2^8)`.** Equal-degree splitting branches on the characteristic: in
  characteristic two the role of `h^((q^d - 1)/2)` falls to the absolute trace, which has `m * d`
  terms for `q = 2^m`. Every existing test of that branch was over `GF(2)`, where `m = 1` and a wrong
  `m` is invisible. It is also the solver's last step, so #197's and #198's ladders rest on it.
- **The degree-256 field equations are usable, not merely representable.** A single quadratic that is
  positive-dimensional bare becomes a zero-dimensional quotient of dimension **256** — one `GF(2^8)`
  point per value of the free variable — with the equations adjoined. §5.1's rule says the mechanism
  is *unwise* over `GF(2^8)`, and that is a statement about cost; it is not a capability limit, and
  the two are now distinguished by a test rather than by a reader's charity.
- **Solving works on a `GF(2^8)` system built by hand**, which keeps the §3 result from depending on
  `planted`'s degeneracy into a perfect square (§3.1).

## 7. Question 4 answered: Singular is the oracle in characteristic two, and already was

#218 asked whether Singular can be the oracle in characteristic two, and §6 of the first pass
recorded it as not attempted. It did not need attempting. `src/grobner/differential/check.rs`:

```rust
// before #378; the list is now `SUPPORTED_FIELDS: &[CaseField]`, and has GF(2^8) in it.
pub const SUPPORTED_CHARACTERISTICS: &[u64] = &[2, 3, 7, 13, 65537, 2147483647];
```

Characteristic two has been in the sweep all along. `src/grobner/differential/fixtures.rs` holds
**40 committed cases at characteristic 2** of 240 — an even 40 per characteristic — they are verified
offline on every run of `differential::tests::test_every_committed_fixture_agrees`, and a live sweep
against a local **Singular 4.4.1** covering all six characteristics passes
(`test_a_live_sweep_against_singular_agrees`, `--ignored`, 28 systems since #378 added a
seventh field).

So two claims in the tree were wrong in the same direction and are superseded here: #65's "the oracle
path is small-field only today", and this document's own first-pass statement that characteristic-two
fixtures had not been tried. Characteristic two was never the restriction.

The restriction *was* extension fields, in three places rather than one: the dispatch at
`check.rs:190` monomorphized only into `PrimeFieldElement64<p>`; `DifferentialCase` carried a
`characteristic: u64` and nothing else, so `GF(2)` and `GF(2^8)` were both `characteristic: 2` and
could not be told apart; and the two sides did not agree on how an element is written. All three are
**closed** (#378) — see §14. The oracle now reaches `GF(2^8)`, and nothing in this document's tree
is waiting on a field.

## 8. Question 5 decided: `Zp2`

`BinaryFieldElement<0b11>` — `x + 1`, the only irreducible of degree one — does work, and it is the
same field: its whole addition and multiplication tables agree with `Zp2`'s, all four pairs, which
`gf2_by_either_route_is_one_field_at_twice_the_storage` asserts rather than samples. Given that the
choice is free on behaviour, it is decided on storage and on code path:

| | `Zp2` = `PrimeFieldElement32<2>` | `BinaryFieldElement<0b11>` |
|---|---:|---|
| `size_of` | **4 bytes** | 8 bytes |
| multiplication | wide remainder, const-generic branch (§2) | `PCLMULQDQ` + Barrett, for a 1-bit modulus |
| declared alias | `fields::Zp2` | none — the literal has no constant |

**Decision: `GF(2)` is `Zp2` throughout, including in the Fukuoka importer of #197.** Half the
storage, no carry-less-multiply machinery for a field where multiplication is `and`, and it is the
**prime-field** route that every existing `GF(2)` test already takes — the differential harness
reaches characteristic two as `PrimeFieldElement64<2>` (`check.rs:190`), the same field at the other
declared width, so a caller picks a width rather than a field (§2). `BinaryFieldElement` earns its
keep at `GF(2^8)` and `GF(2^63)`, not at `GF(2)`.

## 9. Question 3: the layout facts, and the measurement deliberately not taken

The storage argument is split here into the half that is a fact about layout and the half that is a
number, because only the first could be settled without the machine.

Asserted, in `a_gf2_coefficient_costs_the_same_sparse_entry_as_any_other`:

| | bytes |
|---|---:|
| `(usize, Zp2)` — one sparse entry over `GF(2)` | **16** |
| `(usize, Gf256)` | 16 |
| `(usize, BinaryFieldElement<0b11>)` | 16 |
| `Monomial<8>` — eight `u32` exponents for what 8 bits describe | 32 |

So a `GF(2)` coefficient costs exactly what a `GF(2^8)` one costs and exactly what a 32-bit
prime-field one costs: the index's alignment pads the pair, and **one bit of information occupies 16
bytes**. That is #62/M19 §8's finding at the field where it bites hardest, and no arithmetic change
narrows it — only a different representation does.

**The per-nonzero cost is still not measured, and this pass did not measure it.** M26 holds this
machine for recorded measurements, and a timing taken beside it would be noise reported as a figure.
`examples/elimination_density.rs` and `examples/field_width.rs` remain the instruments, #272 (H16) is
scoped to exactly this for the linear-algebra kernel, and **#218 stays open on this question alone.**

## 10. Three gaps, filed, each pinned by a test

- **#377 (High) — `FiniteField::new` and `from_str` are `todo!()` for `BinaryFieldElement`.** The
  consequence is larger than it looks: `multi_poly_parser.rs` calls `F::from_str(..).unwrap()`, so
  **`MultivariatePolynomial::parse` panics over `Gf256`**. No `GF(2^8)` system can be read from text
  at all — which means *this*, and not the export of §1, is what blocks #197's and #198's importers.
  Over `GF(2)` the identical call works, because `Zp2` is a prime field, which is why nothing
  noticed. `ExtensionFieldElement::from_str` is `todo!()` too, and its `new` is the prime-subfield
  embedding, so a generic enumeration through `new` would walk 2 of 256 elements and report a point
  count that is **wrong rather than failed**. Mitigated here in the one caller this branch owned:
  `rational_points_by_enumeration` refused a field whose order and characteristic differ. **Now
  closed — see §13**, which records the trait-level decision about what `new(val: u64)` means.
- **#376 — `solve_one`'s default route misdiagnosed a missing field equation. Now fixed.** #218's
  gap 2 was "no field-equation mechanism, and no refusal when they are absent". The refusal existed
  and was correct, but not on the default path: `GrevlexF4ThenFglm` said *the system is not
  zero-dimensional* at once, while the default `DirectLexF4` exhausted a Macaulay-matrix budget and
  reported a **resource failure** — an error that tells a caller to raise a limit when the fix is to
  adjoin the equations. The fix is that a direct-lex attempt which crosses a resource limit has no
  basis to classify, so it computes a **grevlex** one and classifies that instead; both routes now
  end at `PositiveDimensional`. The diagnosis is a proof, not a guess — it fires only from a
  complete grevlex basis — so a zero-dimensional ideal that really is out of budget keeps its
  resource failure, which is what
  `one_missing_field_equation_is_still_a_resource_failure` pins: seven of the eight field equations
  leave *this* ideal zero-dimensional, and the lex budget is then genuinely to blame.
- **#378 — the differential oracle is prime-field only.** **Closed**; see §14. Was blocked on #377
  — there was no point emitting `GF(2^8)` rings while Zeebra could not read an element back — and
  unblocked by §13. All three parts are done: the dispatch keys on a field rather than a
  characteristic, `DifferentialCase` names its modulus, and the minimal polynomial is *asserted*
  to agree on both sides rather than conventionally shared.

Still deliberately out of scope, as in the first pass: **no import was enabled** (`MqField::Gf2` and
`MqField::Gf256` still refuse, with accurate reasons; wiring the importer against a published answer
file under `0x11D` is #197's), and **no performance work**.

## 11. Reproducing

```sh
cargo test --test boolean_readiness
cargo test --lib -- grobner::field_equations
cargo test --lib -- --exact grobner::tests::test_the_whole_pipeline_over_gf2
cargo test --lib -- --exact grobner::tests::test_the_whole_pipeline_over_gf256
cargo test --lib -- --exact grobner::tests::test_planted_degenerates_to_a_square_in_characteristic_two
cargo test --lib -- --exact fields::binary_field::tests::test_the_two_degree_eight_moduli_are_different_fields
cargo test --lib -- --exact fields::binary_field::tests::test_declared_moduli_are_irreducible
cargo test --lib -- --exact grobner::differential::tests::test_every_committed_fixture_agrees
```

`boolean_readiness` reports **11 passed, 0 ignored**: the two that named #377 —
`the_enumeration_oracle_should_cover_gf256` and `a_system_over_gf256_should_parse_from_text` — are
un-ignored and green (§13). The live Singular sweep of §7 needs a local install and is `--ignored`:

```sh
cargo test --lib -- --ignored --exact \
    grobner::differential::tests::test_a_live_sweep_against_singular_agrees

# needs a local Singular; the GF(2^8) half of the same (§14)
cargo test --release --lib -- --ignored --exact \
    grobner::differential::tests::test_a_live_gf256_sweep_against_singular_agrees
```

## 12. Consequences for the issues that were waiting on this

- **#219 (G1, SAT4CryptoBench)** — unblocked, including the part that matters: field equations exist,
  the `GF(2)` solve path returns verified points, and the Singular oracle is available in
  characteristic two (§7). Nothing on #218 still gates it, and #378 was never one of its gates —
  SAT4CryptoBench is over `GF(2)`, so what #378 added it did not need. What it still needs is its
  own: the benchmark's instances fetched and converted, and a decision on which of them are within
  reach at all.
- **#221 (G4, LowMC)** — unblocked, oracle included. Still rank 4 on its merits.
- **#197 (A5, Fukuoka types I–V)** — unblocked at the field level, and `Gf256Mq` exists. The
  `GF(2^8)` types are now importable from text too (§13); a coefficient is written as its
  coefficient bit pattern, `0..255`. The `GF(2)` types always could — use `Zp2` for those (§8). The
  `GF(2^8)` types also have a *basis* oracle now (§14), not only a published answer file — but
  only under `Gf256`'s modulus; the Fukuoka modulus is `Gf256Mq`'s `0x11D`, which is a one-line
  addition to the dispatch and is #197's to make when it needs it.
  **Delivered.** #197 took §8's decision and removed the importer's GF(2) refusal, so all six
  families now import — `Zp2`, `Gf256Mq`, `Zp31` — and `SUPPORTED_DIMENSIONS` gained `5` for the
  signature toys. The `0x11D`-versus-`0x11B` question is now a test rather than a recorded
  observation: 20 of 20 polynomials of type II `n = 10` vanish at the published answer under the
  challenge modulus and 0 of 20 under the AES one. See `fukuoka-mq.md` §14 (moved out in #668).
- **#198 (A6, HFE Challenge 1)** — the `GF(2)` ladder is unblocked, and the `GF(2^8)` text input the
  ladder's upper rungs need now exists (§13), with a `GF(2^8)` differential oracle behind it (§14).
  HFE-80 remains far out of reach; the reduced `HFE n_D` rungs on Steel's page are the target.
- **#206 (F2, MinRank modellings)** — gets the field-equation mechanism it needs for challenges D–F,
  and §5.1's rule says the mechanism is worthless for A–C over `GF(65521)`. That is the answer to
  F2's question 5 for the prime-field half, derived rather than assumed.
- **Anemoi over `GF(2^n)`**, deferred in `docs/research/additional-benchmarks.md` §9 (moved out in #668) — unblocked at
  the field level, and text input over `GF(2^8)` now works too (§13).
- **#272 (H16)** — owns the per-nonzero measurement of §9, and its end-to-end judgement belongs back
  on #218.

## 13. #377 closed: what `new` means, and what `from_str` reads

The gap of §10 was not a `todo!()` to fill in. The two `FiniteField::new` implementations meant
different things by `new(val: u64)` — `ExtensionFieldElement`'s was the prime-subfield embedding,
`BinaryFieldElement`'s inherent one was a bit pattern — and either reading, applied uniformly, broke
one of the two callers. Settled at the trait:

| | meaning |
|---|---|
| `FiniteField::new(val)` | the image of `val` under the unique ring homomorphism from the integers: `val mod p`. Uniform over every field, and **deliberately not onto an extension** |
| `FiniteField::from_str(s)` | the text `Display` writes, so `from_str(&a.to_string()) == Ok(a)` over every field in the crate |
| `KnownOrder::element_at(i)` | **new.** The bijection from `0..q` onto the field that the enumeration callers actually wanted from `new` |

Why that split. `new` as the embedding is the reading `ExtensionFieldElement` already had and the one
`solve.rs`'s comment already assumed, and it is the only reading that means the same thing in every
field; `BinaryFieldElement::new` is now `val mod 2`. `from_str` is a *representation* parser rather
than the embedding because `Display` has to distinguish all `q` elements and an integer embedding
cannot — so over an extension `from_str("5")` is deliberately not `new(5)`.

Concretely, a bare decimal in `from_str` is the element's **index**: the coefficient bit pattern over
`GF(2^m)`, the base-`p` digits over `GF(p^k)`. That rule agrees with `new` on `0..p` — so on `0` and
`1` in every field, and on the whole of any prime field, which is why nothing in the existing text
corpus changes meaning — and extends it to the whole field instead of folding onto the subfield.
`ExtensionFieldElement` additionally accepts the bracketed `[c_0, …, c_{k-1}]` form its `Display`
writes. Anything outside the field's representation is a `ParseFieldElementError`, not a panic.

`element_at`'s default **is** `new`, which is that bijection exactly when `q = p`; over a field whose
order and characteristic differ it returns `None` rather than an element `new` would have put in the
wrong place. So the prime fields inherit it correctly with no edit, both extension families override
it, and a future field that forgets to override reports that it cannot be enumerated instead of
enumerating wrongly — the §10 hazard is structurally closed rather than patched at one caller.
`rational_points_by_enumeration` walks `element_at` and now covers `GF(2^8)`;
`FieldEquationError::NotIndexableByInteger` survives as the refusal for a field that has not
overridden it, and no field in the crate raises it.

`multi_poly_parser.rs` no longer `unwrap`s: a coefficient outside the field, an unknown variable and
an exponent beyond a `u32` are all parse errors against the offending span.

Pinned by `from_str_inverts_display` and `new_is_the_integer_embedding` over all eleven
`for_each_field!` types, `element_at_covers_the_field_exactly_once` over the small ones, and
`fields::finite_field::tests::test_element_at_covers_an_extension_field_where_new_does_not`, which
runs both maps over `0..q` and counts their images: `q` against `p`.


## 14. #378 closed: the oracle reaches GF(2^8), and the modulus is asserted

§7 left three things between the harness and an extension field. All three are done.

**The case names a field.** `DifferentialCase`, `DifferentialFixture` and `GeneratedSystem` carried
`characteristic: u64`; they now carry a `CaseField` — `Prime { characteristic }` or
`Binary { modulus }`, the modulus as a bit pattern with the extension degree read off its degree. So
`GF(2)` and `GF(2^8)` are distinct values, and a `GF(2^8)` case records *which* degree-8 polynomial
the oracle reduced by. `SUPPORTED_CHARACTERISTICS` became `SUPPORTED_FIELDS`, and the dispatch in
`check.rs` matches a field rather than an integer.

**The modulus agreement is an assertion, in two independent places.** `Gf256` is `x^8+x^4+x^3+x+1`
and `Gf256Mq` is `x^8+x^4+x^3+x^2+1`: same characteristic, same order, and `0x57 * 0x83` is `0xc1`
in one and `0x52` in the other — §4's distinction, now load-bearing.

On Zeebra's side, `CaseField::matches` does not ask a field type what its modulus is; it multiplies.
In `GF(2)[x]/(P)` with `P = x^m + r` the relation `x^m = r` holds and determines `P`, so raising the
element whose bit pattern is `2` to the `m`-th power and comparing it with the element whose pattern
is `r` accepts exactly one modulus. That needed no new trait method and no change to `src/fields/`.
`test_a_gf256_case_checked_modulo_the_other_polynomial_is_rejected` is the assertion: a case
recorded modulo `0x11B` and checked against `Gf256Mq` fails on `Check::Field`.

On Singular's side, the harness does **not** use `ring R = (2^8, a), ...`. Singular's small Galois
fields take their minimal polynomial from an internal table a script cannot choose, which is exactly
the wrong property here. It declares an algebraic extension of the prime field instead —
`ring R = (2,a),(x1,…),dp;` with `minpoly = a^8+a^4+a^3+a+1` — which is the only form in which the
modulus is the harness's to state. Singular echoes `minpoly` back, the echo is parsed and compared,
and a ring reducing by something else is an `OracleError::ModulusMismatch`: an oracle failure, never
a comparison. `minpoly` is set in every ring, since it is a property of a ring and not of a session.

**The two sides write an element differently, and the text is translated.** Zeebra writes the decimal
of the coefficient bit pattern (§13); Singular writes `(a^3+a)`. Every polynomial crossing the
boundary is rewritten in both directions, so a committed fixture is always in Zeebra's syntax and
needs no conversion step to be read or pasted. Over a prime field both rewrites are the identity,
which is why the 240 recorded prime answers are byte-for-byte what they were — the migration renamed
their field and touched no datum.

**The corpus.** `FIXTURES_GF256`: 40 ideals over `GF(2^8)` in two to five variables — 19
zero-dimensional, 11 unit ideals, 10 positive-dimensional — generated against a live Singular 4.4.1
(build 44105) and verified offline, recording the source basis, the quotient dimension, the standard
monomials, every border normal form and the lex basis. So CI exercises the multiplication operators
column by column over an extension field with no Singular present. It is a *second* table rather
than more rows in the first: a generated header's regeneration command is only true of the sweep
that wrote it, and adding a seventh field to the first sweep's list changes which field every seed
above index 23 is generated over — so 240 recorded prime answers would all have been replaced to add
one `GF(2^8)` row. Each table is reproducible by the one command in its own header.

`test_the_gf256_fixtures_reach_past_the_prime_subfield` is why the corpus means something: a table
of `GF(2^8)` cases whose every coefficient happened to be `0` or `1` would pass every other test
while covering nothing the `GF(2)` corpus already covers.

**What is still not there.** Only `Gf256`'s modulus is in the dispatch. `Gf256Mq`'s `0x11D` — the
Fukuoka MQ Challenge modulus, which #197 needs — is a one-line arm away, and deliberately not added
here: nothing in the repo generates systems over it yet, and a supported field with no fixture would
fail `test_the_fixtures_cover_every_field_and_variable_count` by design. Extensions of odd
characteristic (`Gf13Pow4`) are not covered either; `CaseField` has no variant for them, because
Singular's `minpoly` syntax would need the coefficient translation generalized past GF(2) and no
open issue wants it. Both are noted on the issues that would use them rather than left implicit.

## 15. #218 closed: question 3 measured, question 7 recorded, and the backends reached

§9 left this issue open "on this question alone". This section closes it, and corrects two things
the earlier passes claimed.

### 15.1 Question 7: no NTT over `GF(2^m)`, and none is wanted

**Recorded as a won't-do, which is all #218 asked for.** The multiplicative group of `GF(2^m)` has
order `2^m - 1`, which is odd, so it contains no element of order `2^k` for any `k >= 1` and there
is no two-adic root of unity to build a radix-2 transform on. `src/fields/two_adic.rs` says the same
thing from the other side: `GF(2)`'s two-adicity is zero.

That is not a gap to fill. Nothing in the crate needs one: the Boolean path is F4 and FGLM over
`Monomial<N>`, and the univariate transforms that would want an NTT — `src/fft/`, Bluestein, the
Graeffe root-finding of #161 — are reached only over prime fields with the required two-adicity.
A characteristic-two instance that wanted fast univariate multiplication would use carry-less
multiplication, which **already exists** and which M19-B measured at 105x on the operation. So the
honest record is: the obstacle is real, the capability is not needed, and the alternative is
already shipped. **Do not build it**, and revisit only if something asks.

### 15.2 Question 3: the per-nonzero cost, measured

`examples/boolean_density.rs` is the instrument. It eliminates the **same structural system at two
field widths** — random quadratics in `n` variables with `x_i^2 - x_i` adjoined, one equation per
variable, seed 218 — over `Zp2` and over `Zp2147483647`, and times all three backends over every
matrix.

Two notes on the design, both of which are corrections to what an earlier draft of this harness
asserted:

- `benchmark_systems::planted` is **not** the workload. It is structured, and at `n = 12` it builds
  a widest matrix of 54 x 36 with every elimination under 0.01 ms — real figures about nothing.
  #218's own reproducible experiment specifies *random* quadratics, and the construction used here
  is the one `field_equations`' dimension test uses.
- `with_field_equations` is **not** used for the wide-field side. `x_i^q - x_i` at
  `q = 2147483647` is a degree-2^31 generator, and F4 refuses it at 200 000 matrix rows — which is
  what the first run of this harness did. The adjoined generators are degree two at both widths,
  and over `GF(2)` they *are* the field equations, which
  `boolean_restriction_is_the_gf2_field_equation` asserts against the shipped
  [`field_equations`](../../src/grobner/field_equations.rs) rather than arguing from `q = 2`.

§9's layout facts are confirmed and unchanged: `size_of::<(usize, Zp2)>()` is **16**, the same as
over a 32-bit prime and over `GF(2^8)`, so one bit of information occupies 16 bytes — a factor of
**128**. The index is what pins it: a `usize` column number is 8 bytes before any coefficient is
stored.

**And the measurement adds a finding §9 did not anticipate.** The two widths do not build the same
matrices, though the structural system and its monomial support are identical:

| n | field | widest | entries | peak live | row ops | live entry bytes |
| ---: | --- | --- | ---: | ---: | ---: | ---: |
| 6 | `Zp2` | 251 x 184 | 5 628 | 2 193 | 5 940 | 35 088 |
| 6 | `Zp2147483647` | 256 x 190 | 8 325 | 4 299 | 12 282 | 68 784 |
| 8 | `Zp2` | 1296 x 833 | 51 214 | 44 949 | 104 759 | 719 184 |
| 8 | `Zp2147483647` | 1292 x 829 | 91 084 | 108 712 | 222 280 | 1 739 392 |
| 10 | `Zp2` | 4209 x 2363 | 347 397 | 469 286 | 1 150 140 | 7 508 576 |
| 10 | `Zp2147483647` | 4252 x 2405 | 678 266 | 1 107 279 | 2 272 797 | 17 716 464 |

**Over `GF(2)` the same system needs about half the entries and about half the row operations** —
1.95x fewer entries and 1.98x fewer row operations at `n = 10`, and 2.36x less peak live memory.
Coefficients are 0 or 1 and `a + a = 0`, so additions cancel mod 2 far more often and rows go to
zero that would not over a large prime.

**Every figure in that table is a count rather than a timing**, so it is exact and reproduces
bit-for-bit on any machine under any load. That is deliberate: this workstation runs several agents
and the benchmark lock was held throughout, so a wall-clock column would have been a figure about
the queue. The harness does report per-backend milliseconds and nanoseconds per row operation —
the normalization that separates "fewer operations" from "cheaper operations" — and those belong in
a run taken under `tools/benchlock.sh` on a quiet box. What they will show is already known
independently and is not a characteristic-two effect: `Zp2` is a four-byte cell and
`Zp2147483647` an eight-byte one, which is the comparison
`MILESTONE-SIMD-PARALLELISM.md` §8.4 measured at 2.80x on the dense backend.

So the conclusion for a representation decision is sharper than §9's, and in the opposite direction
from the intuition the 16-byte figure invites. **`GF(2)` is already cheaper in memory than the wide
field, and not for the reason the question asked about**: the entry is exactly the same size, there
are simply fewer of them. The 128x gap between a bit and its 16 bytes is real and is entirely a
representation cost — which is what makes it #272's to collect, and why no arithmetic or field
change narrows it.

`n = 12` is compiled and reachable as an argument but is not measured: random quadratic Boolean F4
does not finish there inside ten minutes where `n = 10` takes seconds.

### 15.3 The characteristic-two gap §3 implied was closed, and was not

§3 wrote that "F4, FGLM, `solve_one` **and the echelon backends**" had never run in characteristic
two, and implied all four were then closed. Three were. The fourth was not: `src/linalg/` contained
no `Zp2`, `Gf256` or `BinaryFieldElement` at all, so of the three backends only
[`Backend::Adaptive`] had ever run at this characteristic — and only indirectly, because that is
what `F4Options::default()` selects. `Sparse` and `Dense` had never been run over an
even-characteristic field by anything.

Closed now, and **in the tests rather than in the example**, because an example is not run by CI:
`test_every_backend_agrees_on_every_shape_and_field` and
`test_every_backend_honours_the_split_contract` in `src/linalg/echelon.rs` now check `Zp2` and
`Gf256` alongside the five odd fields they already covered. Both shapes of even characteristic are
there because they are different code — `Zp2` keeps the wide-remainder path, since `2^32` is not
invertible modulo an even number, while `Gf256` is carry-less multiplication with a Barrett
reduction.

Worth checking rather than assuming, for a reason specific to the characteristic: every nonzero
coefficient over `GF(2)` is one, so normalization never divides and `pivot_inversions` stays zero
throughout; and the frequent cancellation §15.2 measures is exactly the path on which the three
backends maintain their nonzero counters by separate code. The example still runs all three and
asserts the same agreement, which is how the measurement knows its own timings are of the same
computation.
