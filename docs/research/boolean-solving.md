# Boolean solving readiness: what works in characteristic two, and what the blocker actually was

Reference for #218 (G2), a child of the Boolean epic #196. **The headline result is a negative one
in the useful direction: the Gröbner stack already works in characteristic two, and nothing had to
change for it to.** The issue was written expecting a list of failures and said so — "Report what
breaks, in detail. A list of concrete failures is the most valuable possible output of this issue."
There are none at the pipeline level. The real gaps were elsewhere, and one of them is a correctness
hazard that nothing had noticed.

§6 lists what this issue did *not* do, because three of its six questions remain open.

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
**Which of `Zp2` and `BinaryFieldElement<0b11>` the Fukuoka importer should use is still open** — see
§6.

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
correct, internal to the crate, and independent of Singular's characteristic restriction — which
means §6's open question about the differential oracle does not block this result.

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

## 6. What this issue did not do

Three of #218's six questions are still open, and the issue should not be closed on this document
alone.

- **The representation cost is not measured** (question 3). `Monomial<N>` is an exponent array where
  a bit set would do, and a sparse entry is `(usize, F)` padded by the index's alignment to 16 bytes
  at any field width — **16 bytes to store one bit** over `GF(2)`, which is the strongest argument in
  the crate for a bitset representation and is still an argument rather than a number.
  `examples/elimination_density.rs` and `examples/field_width.rs` are the instruments and were not
  run for this.
- **The Singular oracle in characteristic two is untested** (question 4).
  `differential/comparison.rs` matches a fixture's characteristic and #65 records the limit — "the
  oracle path is small-field only today". Whether characteristic-two differential fixtures can be
  generated and compared was not attempted. §5's enumeration oracle sidesteps it for that result
  only; #219 and #221 will want an answer.
- **The `GF(2)` representation decision is recorded as open, not made** (question 5). `Zp2` and
  `BinaryFieldElement<0b11>` are the same field and not the same code path or storage.
- **No import was enabled.** `MqField::Gf2` and `MqField::Gf256` still refuse, now with accurate
  reasons. Wiring the importer and checking it against a published answer file under `0x11D` is
  #197's deliverable and deliberately not bundled here — the same discipline
  `docs/research/additional-benchmarks.md` §5 asked for in the other direction.
- **No performance work.** Finding out what works came first.

## 7. Reproducing

```sh
cargo test --lib -- grobner::field_equations
cargo test --lib -- --exact grobner::tests::test_the_whole_pipeline_over_gf2
cargo test --lib -- --exact grobner::tests::test_the_whole_pipeline_over_gf256
cargo test --lib -- --exact grobner::tests::test_planted_degenerates_to_a_square_in_characteristic_two
cargo test --lib -- --exact fields::binary_field::tests::test_the_two_degree_eight_moduli_are_different_fields
cargo test --lib -- --exact fields::binary_field::tests::test_declared_moduli_are_irreducible
cargo test --lib -- --exact grobner::research::mq::tests::test_the_binary_and_extension_fields_are_refused_by_name
```

## 8. Consequences for the issues that were waiting on this

- **#197 (A5, Fukuoka types I–V)** — unblocked at the field level. `Gf256Mq` exists; the answer-file
  test under the right modulus is the next step and is #197's.
- **#198 (A6, HFE Challenge 1)** — the `GF(2)` ladder is unblocked at the field level. HFE-80 itself
  remains far out of reach; the reduced `HFE n_D` rungs on Steel's page are the target.
- **#219 (G1, SAT4CryptoBench)** — unblocked, and it will want field equations present, which it now
  can have. It will also want the Singular-oracle answer this issue did not produce.
- **#221 (G4, LowMC)** — unblocked. Still rank 4 on its merits.
- **#206 (F2, MinRank modellings)** — gets the field-equation mechanism it needs for challenges D–F,
  and §5.1's rule says the mechanism is worthless for A–C over `GF(65521)`. That is the answer to
  F2's question 5 for the prime-field half, derived rather than assumed.
- **Anemoi over `GF(2^n)`**, deferred in `docs/research/additional-benchmarks.md` §9 — unblocked at
  the field level.
