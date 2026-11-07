# Boolean solving readiness: what works in characteristic two, and what the blocker actually was

Reference for #218 (G2), a child of the Boolean epic #196. **The headline result is a negative one
in the useful direction: the Gröbner stack already works in characteristic two, and nothing had to
change for it to.** The issue was written expecting a list of failures and said so — "Report what
breaks, in detail. A list of concrete failures is the most valuable possible output of this issue."
There are none at the pipeline level. The real gaps were elsewhere, and one of them is a correctness
hazard that nothing had noticed.

**Written in two passes.** §1–§5 are the first (#233): the stale blocker, the pipeline result, the
`0x11D` hazard, and the field-equation mechanism. §6–§10 are the second (#379), which asserted the
*solving* half the first pass left out, answered questions 4 and 5, and found three gaps — one of
them a panic on any text input over `GF(2^8)`. §9 is why the issue is still open: question 3's
measurement was deliberately not taken.

## 1. The blocker everyone was waiting on had already cleared

Five issues were scoped against a claim that was false when they were written.
`docs/research/additional-benchmarks.md` §5 said LowMC was "**Blocked, and on an interface rather
than on mathematics**… `src/fields/mod.rs` declares `mod binary_field;` — private, not exported";
`docs/research/fukuoka-mq.md` §1 marked four Fukuoka types "**no** — … is private"; `MqField::Gf2`
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
`grobner::research::mq::tests::test_the_binary_and_extension_fields_are_refused_by_name` asserted
`because.contains("not publicly exported")`, so the stale reason was pinned by the suite and would
have survived any amount of documentation editing. It now asserts the accurate reason *and* that the
stale phrase is absent, so the claim cannot come back.

Corrected: `docs/research/fukuoka-mq.md` §1 and §6, `docs/research/additional-benchmarks.md` §5 (as
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
class of error `docs/research/fukuoka-mq.md` §2.1 guarded against for the monomial layout, which was
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
machine-independent invariant, in the role `docs/research/additional-benchmarks.md` §3.2 gives
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
| `GF(31)` — Fukuoka III/VI | 31 | 4 to 9 (`docs/research/fukuoka-mq.md` §4) | **no** |
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
pub const SUPPORTED_CHARACTERISTICS: &[u64] = &[2, 3, 7, 13, 65537, 2147483647];
```

Characteristic two has been in the sweep all along. `src/grobner/differential/fixtures.rs` holds
**40 committed cases at characteristic 2** of 240 — an even 40 per characteristic — they are verified
offline on every run of `differential::tests::test_every_committed_fixture_agrees`, and a live sweep
against a local **Singular 4.4.1** covering all six characteristics passes
(`test_a_live_sweep_against_singular_agrees`, `--ignored`, 24 systems).

So two claims in the tree were wrong in the same direction and are superseded here: #65's "the oracle
path is small-field only today", and this document's own first-pass statement that characteristic-two
fixtures had not been tried. Characteristic two was never the restriction.

**The restriction is extension fields**, and it is three things rather than one: the dispatch at
`check.rs:190` monomorphizes only into `PrimeFieldElement64<p>`; `DifferentialCase` carries a
`characteristic: u64` and nothing else, so `GF(2)` and `GF(2^8)` are both `characteristic: 2` and
cannot be told apart; and neither side can render or read the elements — Zeebra's parser panics over
`Gf256` (§10), and Singular needs its Galois-field ring syntax with a declared minimal polynomial,
which has to be *the same* polynomial on both sides, which §4 showed is a real distinction.

The consequence for the issues: **#219 (G1) and #221 (G4) are over `GF(2)` and have their oracle
today.** What lacks one is the `GF(2^8)` half of #197 and #198, which is **#378**.

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
  count that is **wrong rather than failed**. Fixed here in the one caller this branch owns:
  `rational_points_by_enumeration` now refuses a field whose order and characteristic differ. The
  general fix is a trait-level decision about what `new(val: u64)` means and is #377's.
- **#376 — `solve_one`'s default route misdiagnoses a missing field equation.** #218's gap 2 was "no
  field-equation mechanism, and no refusal when they are absent". The refusal exists and is correct,
  but not on the default path: `GrevlexF4ThenFglm` says *the system is not zero-dimensional* at once,
  while the default `DirectLexF4` exhausts a Macaulay-matrix budget and reports a **resource
  failure** — an error that tells a caller to raise a limit when the fix is to adjoin the equations.
  Both halves are asserted, so closing #376 breaks the test on purpose and brings this section with
  it.
- **#378 — the differential oracle is prime-field only.** §7. Blocked on #377: there is no point
  emitting `GF(2^8)` rings while Zeebra cannot read an element back.

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
cargo test --lib -- --exact grobner::research::mq::tests::test_the_binary_and_extension_fields_are_refused_by_name
cargo test --lib -- --exact grobner::differential::tests::test_every_committed_fixture_agrees
```

`boolean_readiness` reports **8 passed, 2 ignored**; the two ignored name #377 and turn green when it
closes. The live Singular sweep of §7 needs a local install and is `--ignored`:

```sh
cargo test --lib -- --ignored --exact \
    grobner::differential::tests::test_a_live_sweep_against_singular_agrees
```

## 12. Consequences for the issues that were waiting on this

- **#219 (G1, SAT4CryptoBench)** — unblocked, including the part that matters: field equations exist,
  the `GF(2)` solve path returns verified points, and the Singular oracle is available in
  characteristic two (§7). Nothing on #218 still gates it.
- **#221 (G4, LowMC)** — unblocked, oracle included. Still rank 4 on its merits.
- **#197 (A5, Fukuoka types I–V)** — unblocked at the field level, and `Gf256Mq` exists, but the
  `GF(2^8)` types **cannot be imported from text until #377**. The `GF(2)` types can. Use `Zp2` for
  those (§8).
- **#198 (A6, HFE Challenge 1)** — the `GF(2)` ladder is unblocked. HFE-80 remains far out of reach;
  the reduced `HFE n_D` rungs on Steel's page are the target.
- **#206 (F2, MinRank modellings)** — gets the field-equation mechanism it needs for challenges D–F,
  and §5.1's rule says the mechanism is worthless for A–C over `GF(65521)`. That is the answer to
  F2's question 5 for the prime-field half, derived rather than assumed.
- **Anemoi over `GF(2^n)`**, deferred in `docs/research/additional-benchmarks.md` §9 — unblocked at
  the field level; text input over `GF(2^8)` waits on #377.
- **#272 (H16)** — owns the per-nonzero measurement of §9, and its end-to-end judgement belongs back
  on #218.
