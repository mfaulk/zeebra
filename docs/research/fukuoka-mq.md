# Fukuoka MQ Challenge: the published generator, the format, and what the record actually records

**Measured at:** publication bound `54205923`…`35083579` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).
**Except §4.5**, whose pair was measured at `b7847824` and records it: a bound recovered later is
the weaker form, and a figure taken after the convention existed should not need one.

Reference for #70 (A1), M21-A (#92) and #197 (A5). Consumes the provenance conventions of
`docs/research/external-provenance-policy.md` §9 and the four-claim ledger of
`docs/research/minrank.md`.

#70 added §0, §2.5 and §7–§13, and rewrote §2, §3 and §6. The numbering of §1–§6 is unchanged from
the previous revision, because ten other files cite it; the new material is appended rather than
interleaved. #454 appended §4.4 and rewrote §6's dimension bullet.

If you are here for one question — *can an instance be reproduced without downloading it?* — the
answer is **yes, from three integers and a published file of π**, and §7 has the recipe, the
verification, and the two ways the challenge's own verifiers get it wrong.

**The F4 baseline half of #70 is not here.** No run, no timing, no estimate. §4 holds measurements
other work recorded; nothing in §7–§10 is a measurement of this crate.

---

## 0. Sources of record

Each read in place rather than through a search summary, with the bytes pinned. All are primary:
the challenge's own site, its own utility downloads, and the paper it names as its reference. All
accessed **2026-11-07**.

| short name | what it is | URL | sha256 | bytes |
|---|---|---|---|---|
| **`site`** | challenge front page: introduction, the six types, the hall of fame, the download index, the policy and rules | <https://www.mqchallenge.org/> | `55370796310515341f43320aa99ccb8e002c21e0c2d9ec5ddfc2b2d14540ecf6` | 93 222 |
| **`format`** | the file-format specification, with a worked expansion of one polynomial per field | <https://www.mqchallenge.org/format.html> | `c5671f7feb3c8a72462a8820d970e8fccf30d50487748c02a9c01bc00f5603dd` | 7 440 |
| **`guidance`** | how to participate; the rules again; **the coefficient-verifier and Magma-reader downloads** | <https://www.mqchallenge.org/guidance.html> | `2c531a6dfdea4b35fb68a4e31c1bc4c18e0fac08a1abcce7f63fdcd012cf2d79` | 7 208 |
| **`submissions`** | "the full list of all submission details" — every recorded solve, not the front page's top five | <https://www.mqchallenge.org/submission/index.html> | `5254b50362300ce43216effbe0345e4cb70553a4330175e189193866579a814c` | 47 769 |
| **`details/*`** | 37 per-submission pages for types II, III, V and VI, carrying runtime, hardware, notes and the answer vector | `https://www.mqchallenge.org/details/details_<TYPE>_<DATE>.html` | per row in the fixture (§3) | — |
| **`util.m`** | the challenge's **own Magma reader** for an instance file | <https://www.mqchallenge.org/utility/util.m> | `9ac5cd6a991b76ce5daa39284d7a52d23ad2c630a4cbca1275bb500924415c43` | 1 179 |
| **`verifier-enc`** | coefficient verifier for types I–III: generator source plus the π file | <https://www.mqchallenge.org/utility/CoefVerifier_enc.tar.bz2> | `acdeac81b6eba37eb747ec3e13a62aa924cc8e953cb13641f27df72490e7f73c` | 32 022 033 |
| **`verifier-sig`** | coefficient verifier for types IV–VI | <https://www.mqchallenge.org/utility/CoefVerifier_sig.tar.bz2> | `e14a2ff46082721fe2290c08d481e60e696d0e122a64842f3de6a7a023feac65` | 32 023 317 |
| **`PI`** | the generator's randomness source: 200 000 000 ASCII `0`/`1` characters, identical in both verifier archives | `verifyCoef_{enc,sig}/PI` | `58f55ded23d13c56178dbcae8803acfff03c09db4a6ae142fbcb2e31acdfbe98` | 200 000 000 |
| **`YDHTS15`** | Yasuda, Dahan, Huang, Takagi, Sakurai, *MQ Challenge: Hardness Evaluation of Solving Multivariate Quadratic Problems*, NIST Workshop on Cybersecurity in a Post-Quantum World, Washington D.C., 2–3 April 2015; IACR ePrint 2015/275 — the reference `site` names | `eprint.iacr.org` 403s here (§13); read as the Wayback capture [`web.archive.org/web/20211005222623id_/https://eprint.iacr.org/2015/275.pdf`](https://web.archive.org/web/20211005222623id_/https://eprint.iacr.org/2015/275.pdf) | `eabc435f29c1aa481d80430ced9c0912a0e1968acd380a20af1b526e5db64f55` (11 pp.) | 223 844 |

The Wayback CDX index shows the `YDHTS15` PDF under one content digest
(`IAADXY4AYGVVT7GT4I4ENILWM6GNIAGI`) across captures from 2015-09-08 to 2021-10-05, so the snapshot
read is the same document the challenge has linked throughout.

**Licensing.** `site` and every page under it carry "COPYRIGHT © 2015 FUKUOKA MQ CHALLENGE All Right
Reserved" and **no licence grant**. Per `external-provenance-policy.md` §4 nothing is redistributed:
no instance file, no answer vector, no π file, and no verifier source is copied into this
repository. §3 is the redistribution record.

---

## The finding, before the detail

The challenge is usually described as a set of published files. It is better described as a
**published deterministic generator**, and the files are its output:

> Every published Fukuoka MQ instance is reproducible from `(type, n, seed)` plus one 200 Mbit file
> of π that the challenge itself distributes. Confirmed by regenerating all six types' toy examples
> coefficient for coefficient (§7.2).

Three consequences, in descending order of how much they change what this repository should do.

1. **The redistribution problem has a clean answer.** A corpus entry does not need the instance
   bytes or a download recipe for them; it needs three integers and the digest of `PI`. §12.
2. **The challenge's own coefficient verifiers do not work.** Both of them, in two different and
   specific ways (§7.3). A participant who ran the GF(31) verifier against a genuine type III file
   would see 93% of its coefficients disagree and reasonably conclude the download was corrupt.
3. **The constant column is not generated from π**, in any of the six types — and for the three
   signature types, where `guidance` says it is, where it comes from is **not established** (§7.4).

Two further results that are provenance rather than generation:

- **A real GF(2^8) instance now checks out, under the challenge's modulus and not under the AES
  one.** All 20 polynomials of type II `n = 10` seed 0 vanish at the published answer modulo
  `x^8+x^4+x^3+x^2+1`; all 20 fail modulo the AES `x^8+x^4+x^3+x+1` (§2.4). That was §2.4's open
  check and it is now closed from the data side.
- **The only published comparands at the sizes this crate reaches are the challenge team's own
  Magma F4 runs**, and they were not in this repository before: type III `n = 20` in 259.27 s and
  type VI `n = 15` in 2 764.41 s, on a 1 TB machine in March 2015 (§8.2).

---

## 1. The challenge

`YDHTS15` §1 and `site`. For quadratic `f_1 … f_m` in `n` variables over a finite field `F`, find
`v ∈ F^n` with `f_i(v) = 0` for all `i`. Six families, in two shapes:

| type | field | shape | published range | importable here |
|---|---|---|---|---|
| I | GF(2) | encryption, `m = 2n` | `n = 55…100` | **no** — no import path (§6) |
| II | GF(2^8) | encryption, `m = 2n` | `n = 35…54` | **no** — the GF(2^8) path exists (§2.5) but no compiled dimension reaches `n ≥ 35` |
| III | GF(31) | encryption, `m = 2n` | `n = 34…53` | **yes** |
| IV | GF(2) | signature, `n ≈ 1.5m` | `m = 55…100` | **no** — as type I |
| V | GF(2^8) | signature, `n ≈ 1.5m` | `m = 16…35` | **yes at `m = 16`** — `n = 24`, the same arm type VI uses (§4.5) |
| VI | GF(31) | signature, `n ≈ 1.5m` | `m = 16…35` | **yes** |

The ranges are counted from `site`'s own download links: 100 instance files each for types II, III,
V and VI (five seeds × twenty sizes) and 230 each for types I and IV (five seeds × forty-six
sizes). They agree with `YDHTS15` Table 4 "Minimum of `m` and `n`", which gives the starting
parameters as `(m, n) =` `(110, 55)`, `(70, 35)`, `(68, 34)`, `(55, 82)`, `(16, 24)`, `(16, 24)` for
types I–VI.

`n ≈ 1.5m` is exact and it is a **truncation**: the generator computes `n = m * 1.5` in C and
assigns it to an `int` (§7.1), so `m = 17` gives `n = 25`, not 26. Every recorded signature solve
obeys `n = floor(3m/2)`, asserted by
`fukuoka_mq_records::test_the_signature_families_have_n_equal_to_the_truncation_of_one_and_a_half_m`.

**Toy examples exist for all six types**, which the previous revision of this document did not
record: types I, II and III publish `n = 10, 15, 20` and types IV, V and VI publish `n = 5, 10, 15`.
Each archive holds five seeds and an answer file per seed.

**The GF(31) families need no new arithmetic**: `PrimeFieldElement64<31>` already existed, and the
32-bit prime field of #62 landed as `Zp31` as an independent optimization rather than a
prerequisite.

---

## 2. The file format

```text
Galois Field : GF(31)
Number of variables (n) : 10
Number of polynomials (m) : 20
Seed : 0
Order : graded reverse lex order

*********************
16 3 26 15 14 14 ... 27 18 ;
5 0 18 23 6 31 ... 8 9 ;
```

One line per polynomial after the `***` marker, terminated by ` ;`, each carrying
`n(n+1)/2 + n + 1` coefficients — 66 for `n = 10`, 136 for `n = 15`, 231 for `n = 20`. A companion
`-answer` file holds a solution as `[22, 22, 28, ...]`.

**The site does document this.** The previous revision of this section said "the site documents
none of this; it was read off the toy examples", and that was wrong: `format` specifies the format
for all three fields, with a worked expansion of two polynomials, and `util.m` is the challenge's
own reference reader. Both are used below, and both agree with what had been inferred.

One header spelling to know about. `format`'s examples print `Number of equations (m)`; the
generator (§7.1) and every real file print `Number of polynomials (m)`. `MqInstance::parse` accepts
the latter, which is the one that occurs in the data. A parser written from `format` alone would
reject every genuine file; `util.m` sidesteps the question by reading the header **positionally**,
taking line 2 as `n` and line 3 as `m` without looking at the keys.

### 2.1 The monomial layout, verified rather than assumed

**The coefficient vector is every monomial of degree at most two, in descending grevlex order.**

That had been established empirically — four candidate layouts evaluated at a published answer,
exactly one making all `m` polynomials vanish. It is now also established from two primary sources,
which matters because an empirical check at one point is weaker than a specification.

`format`, for `n = 4` with `x1 > x2 > x3 > x4`:

> the order of monomials should be `x1² > x1x2 > x2² > x1x3 > x2x3 > x3² > x1x4 > x2x4 > x3x4 >
> x4² > x1 > x2 > x3 > x4 > 1`

and it then expands its own GF(2) example's first two rows, `1 1 0 0 1 1 0 0 0 0 1 0 0 1 0` and
`0 0 0 0 1 1 0 1 0 1 0 1 0 1 1`, as

> `x1² + x1x2 + x2x3 + x3² + x1 + x4` and `x2x3 + x3² + x2x4 + x4² + x2 + x4 + 1`

Both expansions were checked against that monomial list position by position and both are right.

`util.m` says the same thing in code:

```
P := PolynomialRing(Fq, n, "grevlex");
Mono := MonomialsOfDegree(P, 2) join MonomialsOfDegree(P, 1) join {1};
Mono := Reverse(Sort(Setseq(Mono)));
```

— descending grevlex over degree ≤ 2, which is what the importer does by sorting with
`MonomialOrder::GradedReverseLexicographic` rather than by a hand-rolled index loop. A loop that
happened to agree would be a coincidence nobody could check;
`mq::tests::test_the_layout_is_descending_grevlex` pins the agreement, and
`mq::tests::test_a_published_instance_is_reproduced` pins that the reconstruction vanishes at the
published answer.

Concretely, for `n = 4` the first few are `x0², x0x1, x1², x0x2, x1x2, x2², x0x3, …`, then
`x0, x1, x2, x3`, then `1`.

### 2.2 Coefficients are uniform over `0..=31`, not `0..=30`

`31` appears literally in the published GF(31) files and is congruent to zero. Counted over type III
`n=10` seed 0, across its 1 320 coefficients: the token `0` occurs 46 times and the token `31`
occurs 40, so **residue zero occurs 86 times against a mean of 42.6 for the other thirty** — twice
as likely as any other coefficient in the published data. (Recounted from a fresh download on
2026-11-07; the previous revision's table of the same counts is consistent with this.)

This had been inferred from the histogram, with the note "the generator evidently produced values
mod 32". §7.1 confirms it from the generator: a GF(31) coefficient is `readPI(pos, 5)`, five raw
bits of π, with no reduction and — in the published data — no rejection. `format`'s own GF(31)
example contains a `31` in its third row, so the specification page shows it too.

It decides a parser question: the importer accepts `0..=q` and reduces, rather than rejecting `q`
as out of range. `32` is rejected. It is also a real bias in the instances, which anyone quoting a
solving-degree measurement "against random MQ systems" should know about.

### 2.3 The coefficient type is checked, not assumed

`MqInstance::system` is bounded on `F: KnownOrder`, not `F: FiniteField`, and that bound is the
point: a field whose order cannot be read cannot be compared against the header, and an unchecked
coefficient type silently reduces every coefficient into the wrong field.

The first version checked only that the *header* said GF(31). A reviewer caught that
`instance.system::<10, PrimeFieldElement64<7>>()` therefore built a system with every coefficient
reduced modulo seven — a different mathematical problem, whose solutions and Gröbner behaviour
cannot be attributed to the challenge. Nothing about the resulting system looks wrong, which is
what makes it worth a type bound rather than a convention.

`check_coefficient_field` answers two separate questions in order: whether this importer has a path
for the field at all (GF(2) and GF(2^8) do not), and whether the supplied type *is* that field.
Orders are compared as limb slices rather than integers, because a field order need not fit a
`u64`.

### 2.4 GF(2^8) is not one field, and the challenge does not use the AES one

`fields::Gf256` is `BinaryFieldElement<X8_X4_X3_X_1>` = `0x11B`, **the AES polynomial**. The
challenge's modulus is `0x11D` — one bit apart, `x^2` where AES has `x`. Both are irreducible of
degree eight and the two fields are isomorphic, but they are not the same field: one pair of bytes
has two products. Over AES `0x57 * 0x83 = 0xc1` (FIPS-197 §4.2); over the challenge's it does not,
and more than fifty thousand of the 65 025 nonzero operand pairs separate the two.

`fields::Gf256Mq` is the challenge's field, declared separately for that reason and certified
irreducible by `binary_field::tests::test_declared_moduli_are_irreducible`.
`binary_field::tests::test_the_two_degree_eight_moduli_are_different_fields` asserts the
distinction rather than describing it. Both run green as of this revision.

**The stronger check is now done, outside this crate.** The previous revision said it "belongs with
the import itself and is #197's". It still does as a committed test, but the question of fact is
settled: taking type II `n = 10` seed 0
(sha256 `1bfd90a6d45894b62a78ff72bd056f108c137fd28d11405397180c4e6790c4ae`) and its published
answer `[a3, 67, 64, 5c, ab, 81, 4f, e6, f5, b8]`, and evaluating all twenty polynomials under the
§2.1 monomial layout:

| modulus | polynomials vanishing at the published answer |
|---|---|
| `0x11D`, the challenge's | **20 / 20** |
| `0x11B`, AES's | **0 / 20** |

Repeated over all five seeds at `n = 10`, over `n = 15` seed 0, and over type V `n = 5` all five
seeds: every one vanishes under `0x11D`. So reading a type II or type V coefficient byte under
`Gf256` would build a different system from the published one, with nothing about the result
looking wrong — and the error is not subtle in its effect, it is total.

Note what an order check does **not** catch, and why the modulus must be part of the field
specification rather than derived from the order: two GF(2^8)s with different irreducible
polynomials have the same order, so `F::order_limbs() == [256]` accepts either. §12.

### 2.5 GF(2^8) is written as hex, and the header carries the modulus

The GF(2^8) header is **not** `GF(2^8)` or `GF(256)`. `format` and every type II and type V file
print, verbatim:

```text
Galois Field : GF(2)[x] / x^8 + x^4 + x^3 + x^2 + 1
```

So the file states its own irreducible polynomial, which §2.4 is about. `format` on the coefficient
encoding:

> Any polynomial `a = a7x^7 + a6x^6 + … + a1x + a0 (mod p(x))` represents uniquely an element of
> GF(2^8). To this element, we associate 2-digits hex number equal to the number `a7a6…a1a0` in
> base 2.

with its own worked pair: `de` is `1101 1110` = `x^7+x^6+x^4+x^3+x^2+x`, and `8d` is `1000 1101` =
`x^7+x^3+x^2+1`. Both check out. `util.m` agrees —
`ele := Intseq(StringToInteger(arr[j], 16), 2); MQ[i] := MQ[i] + Fq!ele*Mono[j]` — reading the token
base 16 and the resulting integer as a coefficient bit pattern, lowest degree first. That is
exactly what the inherent `BinaryFieldElement::new` takes.

**Three concrete things this cost the importer**, all of them #197's and **all three now fixed**:

1. `MqField::parse` matched only `"GF(2)"`, `"GF(256)"` and `"GF(2^8)"`, so a genuine type II or
   type V file failed at the header with `MqError::BadHeader`. No real GF(2^8) instance could be
   parsed at all. Filed as #414 and **fixed**: `MqField::parse_header` reads the quotient-ring
   spelling and returns the stated modulus alongside the field, which `MqInstance::modulus`
   records.
2. That header rejection was **load-bearing for correctness, not tidiness**. Coefficients were
   parsed with `token.parse::<u64>()`, i.e. decimal, and the range check was `value > 256`. So a hex
   byte whose digits happen to all be decimal — `08`, `13`, `99` — would have parsed as a
   *different* element and passed the range check silently. Accepting the real header without also
   switching to base 16 would have turned a loud failure into a wrong system, so #414 did both at
   once: `MqField::radix` is 16 for GF(2^8) on coefficient rows and answer vectors alike, and
   `MqField::max_coefficient` is `0xff` there rather than the order.
3. `MqInstance::parse_answer` split on `!c.is_ascii_digit()`, so the published GF(2^8) answer
   `[a3, 67, 64, 5c, ab, 81, 4f, e6, f5, b8]` yielded nine values rather than ten, each of them
   wrong, with no error. Filed as #415 and **fixed**: the parser is a method on the instance, takes
   its base from `MqField::radix`, and returns `Result` — so a coordinate count that is not the
   instance's `n` is `MqError::WrongAnswerCount` and an unreadable or out-of-range token is
   `MqError::BadAnswerValue`, instead of either being dropped.

Since `from_str` for `BinaryFieldElement` reads a **decimal** integer as a bit pattern (#377), it is
not the route for these tokens: the importer has its own base-16 decode.

**And the coefficient route is not `FiniteField::new` either.** For `BinaryFieldElement` the trait
`new` is the prime-subfield embedding — `Gf256Mq::new(0xa7)` is `1` — so building a GF(2^8) system
through it would collapse every byte to a bit and produce a system of the right shape whose every
coefficient is wrong. `MqInstance::system` goes through `KnownOrder::element_at`, which for a binary
field is the bit pattern `util.m` writes; the prime types stay on `new`, because the published
GF(31) files carry the literal token `31` and it is congruent to zero. Pinned by
`test_gf256_coefficients_do_not_go_through_the_prime_subfield_embedding`.

### The modulus is verified against the coefficient type, not assumed

Because the header *states* the irreducible polynomial, `MqInstance::check_coefficient_field` can
check it rather than trust a convention. It derives the coefficient type's own modulus from
arithmetic — in a binary field `element_at(2)` is `x`, so `x^8` is the modulus with its leading term
dropped, which is the defining relation of the quotient ring and the only thing separating two
irreducible polynomials of the same degree — and refuses a mismatch as `MqError::WrongModulus`. So
`Gf256` (AES, `0x11B`) is refused for a challenge file and `Gf256Mq` (`0x11D`) is accepted, and
neither order comparison nor type signature could have told them apart.

---

## 3. Redistribution

> COPYRIGHT © 2015 FUKUOKA MQ CHALLENGE All Right Reserved.

No stated licence. **No instance file, answer vector, π file or verifier source is committed to
this repository.** `tools/fetch-mq-challenge.sh` fetches the GF(31) toy instances into
`research/instances/mq/` (gitignored) and verifies the SHA-256 of each file its manifest names. Its
four checksums were re-verified against fresh downloads on 2026-11-07 and are unchanged; type III
`n = 10` seed 0 is still `9436e45dbd4247f152681e954f1db19d92e8cf5e76b2bc35530bed74aae522ba`.

```sh
tools/fetch-mq-challenge.sh            # fetch and verify
tools/fetch-mq-challenge.sh --verify   # check what is already there
```

`PI` is in the same position and has its own script, because it is fetched once and then serves
every instance (§7, `src/grobner/research/mq_generator.rs`):

```sh
tools/fetch-pi.sh                      # fetch, extract and verify PI
tools/fetch-pi.sh --verify             # check what is already there
```

Both destinations honour `ZEEBRA_MQ_DIR`, and `research/instances/` is gitignored.

The checksums are what make a result reproducible without redistributing the data, which is what
`Provenance::sha256` and `Provenance::redistribution` are for. Unconditional parser coverage comes
from a hand-written fixture in the same format; the test against the genuine instance is
`#[ignore]`d, because a test that silently passed when its data is absent would be worse than no
test.

**What *is* committed** is `research/fukuoka-mq/solved-instances.tsv`: the parameters, dates,
contestants, algorithms, hardware and published figures of all 37 recorded solves of types II, III,
V and VI, with each row naming the page it came from. No answer vector and no coefficient. Checked
by `tests/fukuoka_mq_records.rs` (§8.4, §11).

---

## 4. What zeebra does with it

Type III, `n = 10`, seed 0 — 20 quadratics in 10 unknowns over GF(31):

| | |
|---|---|
| import | parses, 66 coefficients × 20 polynomials |
| reconstruction | all 20 vanish at the published answer `[22, 22, 28, 12, 9, 2, 1, 18, 11, 25]` |
| solve | **111 ms**, `AutoWithFallback`, one attempt |
| route | grevlex F4 then FGLM; 6 batches, largest matrix 1468x859, 168,020 peak entries (2.7 MB) |
| quotient dimension | **`D = 1`** — a unique solution, as an overdetermined encryption instance should have |
| result | the published point, recovered without being told it |

Checked in both directions deliberately. A wrong monomial layout could in principle vanish at one
point by accident; it could not also be *solved* to that same point.

**This is not a competitive result and should not be quoted as one.** It is a toy example, published
precisely so that implementations can check themselves, and `n = 10` is 24 variables short of the
smallest published type III challenge.

### 4.1 The whole published type III family, under one stated budget (M23-D)

`tools/scoreboard.sh mq <id>` under the frontier budget — 200,000 columns, **20,000,000 live
entries**, which is the bound that binds, and a wall clock that never did. Pinned to cores 0–7.

| instance | vars | eqs | deg | outcome | `D` | F4 | total |
|---|---:|---:|---:|---|---:|---:|---:|
| type III `n=10` seed 0 | 10 | 20 | 4 | **verified witness** | 1 | 114 ms | 114 ms |
| type III `n=15` seed 0 | 15 | 30 | 4 | **verified witness** | 1 | 7 873 ms | 7 874 ms |
| type III `n=20` seed 0 | 20 | 40 | 5 | stopped at 20 001 424 live entries | — | 67 496 ms | 67 497 ms |

**`n = 15` recovers the published answer**, and the run says so: the recovered point is compared
against the published answer coordinate by coordinate, and it matches. That is the strongest check
available on this family — the solver was not told the answer, `D = 1` says the solution is unique,
and the point that came back is the one the challenge publishes.

`n = 20` crosses the entry cap at degree 5 after 67.5 s. So the published type III toy examples end
at `n = 15` under this budget, and `n = 20` is the first one that does not fit. Both figures are
reproducible resource bounds rather than timeouts. §8.2 records that `n = 20` was solved by Magma
F4 in 259.27 s in 2015 on a 1 TB machine; that is a published fact about the instance, not a
comparison with the row above.

### 4.2 Type VI `n = 15`: eight slices, and a rate that does not exist

Type VI is underdetermined, so a slice is the only way in: fix `n − m = 5` of the fifteen variables
at values drawn from a precommitted seed and solve the rest. Eight seeds, and **every one of them
crossed the entry cap at degree 9**, each in about 29.5 s.

The campaign is therefore recorded as *having reached no verdict* — not as eight failures. The
distinction is the whole point of the record:

> `0 witnesses in 8 slices; success rate 0.00% to 32.44%`

was what the first version of the runner printed, and it is a claim about the **instance** that
nothing established. A slice that ran out of budget did not test whether it contains a solution, so
it is not a Bernoulli trial of that question. `Campaign::stopped` now counts those separately,
`Campaign::decided()` is the rate's denominator, and `success_rate_basis_points` returns `None`
when nothing was decided. This was found by running the campaign, which is the argument for running
it.

§8.2 records that this instance was solved by Magma F4 in 2 764.41 s in 2015. Note that the
published route is not the one above: every signature-type solve on the site guesses variables
(§8.4), so a slicing strategy is the published approach rather than a workaround.

### 4.3 Type VI `n = 10`: a rate that does exist

The same campaign at the size that finishes, eight precommitted seeds, three of ten variables fixed:

| | |
|---|---|
| slices | 8, all **decided** |
| witnesses | **6** |
| per-slice time | 569–595 ms |
| expected work per witness | **0.8 s**, including the two empty slices |
| success rate | **40.9% to 92.9%** (Wilson, 95%, over the eight decided slices) |

Every witness was evaluated against the *original* published coefficient vectors, so the
specialization is inverted rather than assumed, and the two empty slices are recorded as facts
about those slices.

This is the pair the plan asked for. At `n = 10` the campaign produces an expected cost per witness
and an interval on the rate; at `n = 15` it produces neither, because none of its slices reached a
verdict. The two sit in the same table only because the record distinguishes *decided* from
*stopped* — and the interval at `n = 10` is still 52 points wide on eight trials, which is what
eight trials support.

For contrast with M22-E: its two type VI `n = 10` slices finished at degree 9 with 4 315 columns.
Five surplus variables at `n = 15` is past the wall, and the degree is the same 9 either way — what
grows is the width at that degree.

### 4.4 Type VI `m = 16`: the first real challenge, imported (M27-B, #454)

`SUPPORTED_DIMENSIONS` now reaches **24**, and `fukuoka-mq-VI-n24-seed0` is the first row in this
family that is **challenge data rather than a toy example**. Type VI publishes `m = 16..=35`, and the
generator computes `n = m * 1.5` into an `int`, so the smallest of those is `n = 24`. The file's own
header confirms it:

```text
Galois Field : GF(31)
Number of variables (n) : 24
Number of polynomials (m) : 16
Seed : 0
```

`sha256 354de307fa5524d01c8a6ece3c712c27119cf3388bdd7a3e1c84095ed6cc43de`, 325 coefficients per
polynomial (`binomial(26, 2)`), fetched by `tools/fetch-mq-challenge.sh`. **No instance bytes, no
answer vector and no coefficient are committed** — §3 is unchanged by this, and a real challenge
publishes no answer at all, so the witness check here is evaluation against the imported
coefficient vectors and nothing else.

`m = 16` happens to be exact — `1.5 * 16` is 24 on the nose — and **the next size up is where the
truncation bites**: `m = 17` is `n = 25`, not 26, because the `double` is assigned to an `int`
(§7.1). So 24 and 25 are consecutive dimensions and not a step of two, which is what a reader
extrapolating `1.5m` would expect.

Everything below the dimension is still a toy example. Type III's smallest real instance is
`n = 34`; `n = 24` is the smallest real instance in **any** type this crate can import.

#### The slice policy at the larger dimension

Unchanged in kind and worse in degree. Type VI is a signature family, `n > m`, so it is
positive-dimensional as published and a run of it is a run of a **slice**:

- `n − m = 8` of the 24 variables are fixed, at values drawn from a precommitted seed. Eight, not
  some tuned number: it is the count that squares the system, and the published route is also a
  guessing one (§8.4), so slicing is the challenge's own approach rather than a workaround.
- The formulation string stays `slice(8 fixed, seed s)` and the transformation is recorded as
  `specialize variables 16..24 at seed s`. The fixed variables are the last eight, which is a
  choice and is recorded as one.
- **A slice result is a result about the slice.** A witness lifts — `Specialization::apply` appends
  the pinning forms `x_i − a_i`, so a recovered point is a point of the original variety and is
  re-evaluated against the published coefficient vectors — but an empty or stopped slice says
  nothing about the instance. `Campaign::decided()` is the denominator and
  `success_rate_basis_points` is `None` when nothing was decided (§4.2).
- The slice is **not** registered as its own challenge row. `fukuoka-mq-VI-n24-seed0` is the
  published instance; the slice is a formulation of it, which is what the `transformations` field
  is for.

#### One diagnostic run, and it is a diagnostic

`tools/scoreboard.sh mq fukuoka-mq-VI-n24-seed0 --seeds 1`, frontier budget, cores 0–7, under
`tools/benchlock.sh`. **Not a completion attempt**: one slice, to find out where the wall is.

| | |
|---|---|
| shape after slicing | 24 generators in 24 variables — 16 substituted quadratics plus 8 pinning linear forms |
| outcome | **`stopped_at_limit`**, `max_live_nonzeros` |
| stop | 20 010 753 live nonzero entries needed against the 20 000 000 cap |
| degree | **6** reached; highest completed degree **5** |
| largest matrix | **13 602 × 19 132** |
| peak live nonzeros | 14 329 816 (≈229 MB estimated; 1.38 GB process `VmHWM`) |
| pairs reduced / elements added | 4 967 / 503 |
| wall | **43.2 s** as committed; 43.2, 50.9 and 65.6 s over three runs — all at `1409a48`, and 42.1, 43.4 and 44.3 s re-measured at three later commits for the comparison in §4.5 |

The stop is **deterministic and the wall clock is not**. All three runs stopped at the same degree
on the same entry count, 20 010 753, with the same 13 602 x 19 132 matrix and the same 14 329 816
peak — and spread 53% in time on a machine running other agents' work. Everything above the wall
row is a property of the instance; the wall row is a property of the afternoon. The committed
record is the run under `tools/benchlock.sh` that got the lock uncontended.

Note the degree. Type VI `n = 15` crossed the same cap at **degree 9**; `n = 24` crosses it at
**degree 6**, with a matrix 13 602 × 19 132 against that run's 20 315 × 20 146. Eight surplus
variables rather than five does not push the wall out by three degrees of headroom — it pulls the
wall in, because what grows is the width at every degree. Faugère solved this instance in 2015 in
5 280 s with F5-FGb (§8.1); that is a published fact about the instance and **not** a comparison
with the row above, which is a 43-second resource stop under a deliberate cap.

So the honest statement after #454 is narrower than "Zeebra reaches the challenge": the **importer**
reaches it, the registry names its bytes, and the solver stops at degree 6 under this budget. What
changed is that the gap is now measured rather than merely stated.

### 4.5 Type V `m = 16`: the same size over GF(2^8) (M27, #510)

`m = 16` is `n = 24` in *both* signature families, so the arm #454 compiled serves type V as well —
and since #414 and #415 the GF(2^8) import path is correct, modulus checked against the header
rather than assumed. What was missing was the runner: the scoreboard's MQ visitors were written
against `PrimeFieldElement64<31>`, so the type V challenge **imported and could not be run**. They
are generic over the coefficient type now and the dispatch is on `MqInstance::field`, which comes
from the file. `fukuoka-mq-V-n24-seed0` is registered alongside the type VI row:

```text
Galois Field : GF(2)[x] / x^8 + x^4 + x^3 + x^2 + 1
Number of variables (n) : 24
Number of polynomials (m) : 16
Seed : 0
```

`sha256 fb4b6a3d27fb8263b1a9883745691f3836ad747a6a4052d28919ea5b1a213cc7`, 325 coefficients per
polynomial, fetched by `tools/fetch-mq-challenge.sh`. No instance bytes, no answer vector and no
coefficient are committed, and a real challenge publishes no answer at all. The slice policy is
§4.4's unchanged: `n - m = 8` variables fixed at a precommitted seed, the result a result about
that slice.

#### The two fields at one size

One diagnostic slice each, `--seeds 1`, under `tools/benchlock.sh` on cores 0-7, **always measured
as a pair at one commit** so the two walls are comparable — §4.4's type VI figures were taken at
`1409a48`, a day and several F4 changes earlier (the monomial hasher, in-place scaling, the 2x8
matrix tiling). The committed figures are the pair at **`b7847824`**, which is a
commit on `main` rather than a branch commit — so `Environment::stamp_is_resolvable` holds by its
first route, with nothing to reconstruct.

Three pairs exist because the first was taken at `a3e5d66`, which #530's squash merge did not
preserve (#547), and the second at a branch commit of the fix for that, which its own merge would
not have preserved either. `research/scoreboard/runs/` holds the records for the `a3e5d66` and
`b7847824` pairs; the middle pair's records were discarded with the branch, so only its two wall
figures survive, below, as part of the spread. What all three agree on is the point of quoting
them.

| | type VI, GF(31) | type V, GF(2^8) |
|---|---|---|
| outcome | `stopped_at_limit`, `max_live_nonzeros` | the same |
| entries needed against the 20 000 000 cap | 20 010 753 | 20 011 556 |
| degree reached / highest completed | **6** / 5 | **6** / 5 |
| largest matrix | **13 602 x 19 132** | **13 602 x 19 132** |
| peak live nonzeros | 14 329 816 (~229 MB estimated) | 14 762 419 (~236 MB estimated) |
| process `VmHWM` | 1.382 GB | 1.395 GB |
| pairs reduced / elements added | 4 967 / 503 | 4 968 / 504 |
| wall | **44.3 s** (42.1, 43.4, 44.3) | **111.1 s** (105.1, 106.4, 113.8, 111.1) |

**The combinatorics are the same and only the arithmetic differs.** Same stopping degree, the same
13 602 x 19 132 matrix to the row, 4 967 pairs against 4 968 and 20 010 753 entries against
20 011 556 — a difference of one pair and 803 entries out of 20 million, which is incidental
cancellation over a different field and not a different computation. Every row above the wall
reproduced **to the digit across three pairs at three commits**, which is a stronger statement than
one pair could make: the entry count, the matrix and the pair count are properties of the instance
and the field, and nothing in the F4 work between those commits — the monomial hasher, in-place
scaling, the 2x8 tiling — changes them at this size.

The wall is the only thing the field moves, and it moves it by about **2.5x** — 2.51x at the
committed pair, 2.49x and 2.62x at the other two, on a machine running other agents' work under the
bench lock. With the computation held fixed that factor is the field's arithmetic. The two routes,
for the record: GF(31) multiplies with one Montgomery step, and `BinaryFieldElement` multiplies with a
`PCLMULQDQ` behind a cached feature probe — this machine has the instruction — followed by a
Barrett reduction. Both fields invert by Fermat exponentiation, so inversion is a wash in kind —
the exponents differ (`q - 2` at `q = 2^8` against `q = 31`) and so does the cost of each
multiplication inside it. Which part of the multiply dominates the 2.5x is not measured here, and
the figure does not rest on an answer: it is a wall ratio at a fixed matrix, not an attribution. No
table-lookup route exists for this field in the crate.

That is the useful reading of the pair. Where §4.4's type VI and type III comparison was about
*shape* — eight surplus variables pull the wall in rather than pushing it out — this one holds the
shape fixed and prices the field. It also says where a GF(2^8) optimization would and would not
help: nothing here is bound by the entry count, which the two fields reach within 0.004% of each
other, so a narrower element would not move the stopping degree at all. It would move the 2.5x.

Faugère solved this instance in 2015 in 24 648 s with F5-FGb (§8.1), and the 370-second figure the
same size carries at **seed 2** is per subsystem of a hybrid attack (§8.4) rather than a total.
Neither is a comparison with the row above, which is a 111-second resource stop under a deliberate
cap.

---

## 5. What type VI is for

Type VI is the signature family: `n ≈ 1.5m`, so **underdetermined** — `n = 10` carries only 7
polynomials. That makes it positive-dimensional and out of scope for the zero-dimensional solvers
as it stands, which is M21-E's case rather than a failure. The natural experiment is to fix
`n − m` variables and solve the slice, with every recovered point verified against the original
coefficient vectors and every dead slice recorded as the experiment it is — which, per §8.4, is
also what every published type V and type VI solve did.

---

## 6. Open

- **GF(2^8) import** is three specific defects, not one gap: the header is unparsed (#414), the
  coefficients need base 16 and silently mis-read as decimal if the header check is relaxed without
  it (#414). The third, `parse_answer` mis-parsing a hex answer without erroring, is closed (#415):
  it reads base 16 over GF(2^8) and refuses a short or unreadable file by name. The modulus
  question is settled: `Gf256Mq` (`0x11D`), verified against a published answer in §2.4. #197 owns
  the import path. **#454's gate on #414 and #415 turned out to be already lifted**: both are
  closed, so GF(2^8) imports, and type V's smallest real instance is `m = 16` — the *same* `n = 24`
  the type VI row needed. One dispatch arm therefore serves two fields, and
  `mq::tests::test_the_real_n24_challenges_import` asserts both genuine files parse, carry 325
  coefficients per polynomial, reach the compiled dimension, and refuse the AES modulus. Type II
  starts at `n = 35` and is still out of reach. **Registering and running the type V row is not
  done**: the scoreboard's MQ path is hardwired to `PrimeFieldElement64<31>`, so it needs a field
  dispatch first — #510.
- **The exported-module story is finished and is no longer a reason for anything.** The previous
  revision of §1 still said "the binary and extension field modules exist and are not publicly
  exported" two paragraphs after correcting exactly that claim. Both modules have been public since
  `8757b4a` (2026-11-05), and **#377 closed the deeper blocker**: `FiniteField::new` and `from_str`
  were `todo!()` for the characteristic-two fields, so no GF(2^8) system could be parsed at all.
  `grep -n 'todo!()' src/fields/` is now empty and `KnownOrder::element_at` exists for the
  enumeration callers. Note for the importer that `BinaryFieldElement::from_str` reads a **decimal**
  integer as a bit pattern, so it is not the route for a hex challenge token.
- **GF(2) import** needs the import path and the toy dimensions types I and IV publish, which are
  `n = 10, 15, 20` and `n = 5, 10, 15` respectively (§1) — and §7.2 confirms both reproduce from
  the generator. The field exists two ways — `fields::Zp2` (`PrimeFieldElement32<2>`, which keeps
  the wide-remainder path because `2^32` is not invertible modulo an even number) and
  `BinaryFieldElement<0b11>` — and which one the importer should use is a decision to record once,
  not per call site. #197.
- **Characteristic 2 is no longer untested in the solver.** `grep -rl "BinaryFieldElement" src/grobner/`
  used to be empty. `grobner::tests::test_the_whole_pipeline_over_gf2` and its `Gf256` twin now take
  a planted system through F4, Buchberger agreement, FGLM, both routes to lex, and `solve_one`, with
  the recovered point re-evaluated — and they passed without any change to the solver. Note that
  `benchmark_systems::planted` **degenerates in characteristic two**: `x^2 + y^2 = (x + y)^2`, so its
  first generator per pair is a perfect square and the ideal is nonradical. Asserted by
  `grobner::tests::test_planted_degenerates_to_a_square_in_characteristic_two`, because a reader who
  assumed otherwise would mis-read every characteristic-two measurement taken with that generator.
- **Field equations are available and are not a default.** `grobner::field_equations` adjoins
  `x_i^q - x_i`, whose degree is `q`. Over GF(2) that is degree 2 and makes the ideal radical, so
  `dim F_2[x]/I` becomes exactly the GF(2)-point count — checked against exhaustive enumeration at
  `n = 8`. **Over GF(31) it is degree 31**, against solving degrees of 4 to 9 measured on the type
  III and type VI instances in §4, so for the families this importer actually reaches today the
  answer is no. Types I and IV will want them; types III and VI will not.
- **The GF(2^8) path is end to end, not just the importer.** #414 and #415 fixed the header and
  the hex coefficients; #510 made the scoreboard's MQ visitors generic over the coefficient type
  and dispatch on `MqInstance::field`, so `fukuoka-mq-V-n24-seed0` is registered and runnable and
  §4.5 is its diagnostic. What remains out of reach in this family is **size, not field**: type V
  publishes `m = 16..=35`, so the next size up is `m = 17` at `n = 25`, which no compiled dimension
  reaches. Type II starts at `n = 35`.
- **The smallest published challenge is `n = 34` (type III) or `m = 16` (types V and VI)**, not
  `n = 55`; the `n = 55` figure in the previous revision was type I's range. **Type VI `m = 16` is
  `n = 24`**, and #454 compiled it: `SUPPORTED_DIMENSIONS` is now `[10, 15, 20, 24]` and §4.4 is the
  diagnostic. The list stops there rather than covering `n = 34..=53` and `n = 55..=100`, and an
  unsupported size is still `MqError::UnsupportedDimension` rather than a panic — compiling
  dimensions that cannot be used would be worse than saying so, and each entry costs a
  monomorphization of the whole multivariate stack. The registry row carried the old error until
  #501 and is now `fukuoka-mq-III-n34-seed0`, at the real smallest type III size; §8.1 records that
  size as solved, so the row is `solved externally` and not open.
- **A 32-bit prime field** (#62) landed, as `Zp31`. It halves the bytes a *dense* elimination moves
  and is worth 2.8x there, but the solver's default `Backend::Adaptive` gains nothing measurable —
  0.98x to 1.04x — because a sparse entry is `(usize, F)` and the index's alignment pads it to 16
  bytes at either width. Measured in `docs/MILESTONE-SIMD-PARALLELISM.md` §8; the importer is
  unaffected either way.
- **The F4 baseline #70 asks for is not recorded**, deliberately. No run, no timing, no estimate;
  the machine was frozen for M26's recorded measurements while #70 was worked. §8.2 is the published
  substitute and is not a measurement of this crate.

---

## 7. The generator

`guidance` links two archives under `utility/` that `site` and `format` do not mention. They are
the whole of this section.

**Implemented** as of #420: `src/grobner/research/mq_generator.rs` is the walk below, and
`tools/fetch-pi.sh` fetches and checksums the stream. Implementing it changed what this section
claims, in three ways that only running against the data could show:

- **Both of §7.3's "defects" are parameters**, and the published data falls into three classes —
  toy example, real encryption, real signature — which differ in whether `31` is resampled and
  whether the constant column comes from π. The table is in §7.3; the types are `ThirtyOne` and
  `ConstantColumn`.
- **A real signature challenge is reproducible in full**, constants included, from `(type, m, seed)`
  alone. §7.4 recorded that as not established, on toy-example evidence.
- Its parameters are `(type, n, m, seed)` and **not** `(type, n, seed)`. `n` and `m` are related by
  the type's own rule for every real instance, but not for the type IV–VI toy example at `n = 5`,
  whose header says `m = 3` where `floor(1.5 * 3)` is 4. The pair the file states is the pair the
  walk was run with, so it is what the generator takes; `MqParameters::challenge` applies the rule
  for the real files, which do obey it.

Two smaller choices, both to keep a failure loud. The constant column, where it is not generated, is
**required from the caller** — there is no path that fills it with zeros, because a system with zero
constants is a different system. And the digit stream is validated as `0`/`1` on construction rather
than read the way `readPI` does, which treats every non-`'0'` byte as a one bit, so a truncated
download would otherwise produce plausible coefficients.

The offline tests drive a synthetic stream of a few hundred bytes, so the arithmetic — strides,
widths, the carry across polynomials, the extra read, the wrap at the end — is checked in CI
without the data. The comparison against genuine files is `#[ignore]`d and is §7.2 and §7.3's table
as an assertion rather than as a paragraph.

> **Coefficient Verifier.** The coefficients of the challenges are generated from the digits of PI.
> We provide two kinds of coefficient verifier to let participants check the correctness of the
> downloaded challenges. For encryption scheme (Type I, Type II, Type III), the encryption
> coefficient verifier can check all the coefficients except the constant term, which is generated
> by the secret answer of MQ challenge team. For signature scheme (Type IV, Type V, Type VI), the
> signature coefficient verifier can check all the coefficients including the constant terms.

Each archive holds the generator source (`generateCoef_{enc,sig}.h`, `util.h`,
`coefVerifier_{enc,sig}.cpp` — under 4 kB of C++ in total) and `PI`, 200 000 000 ASCII `0`/`1`
characters, byte-identical between the two archives. `guidance` says those characters are digits of
π; nothing below depends on whether they are (§13).

### 7.1 The recipe

From `coefVerifier_enc.cpp` and `coefVerifier_sig.cpp`:

```c
/* encryption, types 1-3 */  m = 2*n;      start = type*n;  interval = (seed+n)*10 + type;
/* signature,  types 4-6 */  n = m*1.5;    start = type*n;  interval = (seed+n)*10 + type;
```

`n = m*1.5` assigns a `double` to an `int`, hence the truncation of §1. `readPI(pos, bits)` reads
`bits` characters of `PI` from offset `pos` and treats each non-`'0'` as a 1 bit, most significant
first. A coefficient is then

| field | read | value |
|---|---|---|
| GF(2) | `readPI(pos, 1)` | 1 bit |
| GF(2^8) | `readPI(pos, 4)`, `readPI(pos+4, 4)` | two hex nibbles, printed as a 2-digit hex byte |
| GF(31) | `readPI(pos, 5)` | 5 bits, `0..=31` |

and after each coefficient `pos += interval; pos %= 200000000`. Polynomials are emitted in order,
with `pos` carrying across them, and each carries `binomial_coef(n+2, 2)` coefficients — the same
number as `n(n+1)/2 + n + 1`, asserted against the importer by
`fukuoka_mq_records::test_the_coefficient_count_is_the_binomial_the_generator_uses`.

So an instance is a function of `(type, n, m, seed)`, `PI`, and §7.3's rejection policy. No seed is
secret and `PI` is published. Two corrections to "a function of `(type, n, seed)`", both found by
implementing it (#420): `m` is not always the type's rule applied to `n` — the type IV–VI toy
example at `n = 5` carries `m = 3` where `floor(1.5 * 3)` is 4 — and the rejection policy differs
between the toy examples and the real challenges.

### 7.2 Verified against every published toy example

The generator was reimplemented against the shipped `PI` and compared coefficient for coefficient
against freshly downloaded toy examples. "Non-constant coefficients" means the first
`binomial_coef(n+2,2) − 1` of each polynomial; §7.4 is the constant.

| type | field | instance | non-constant coefficients | result |
|---|---|---|---|---|
| I | GF(2) | `n = 10` seed 0 | 1 300 | **exact** |
| II | GF(2^8) | `n = 10` seeds 0 and 4; `n = 15` seed 0 | 1 300, 1 300, 4 050 | **exact** |
| III | GF(31) | `n = 10` seeds 0 and 3; `n = 15` seed 0; `n = 20` seed 0 | 1 300, 1 300, 4 050, 9 200 | **exact**, with §7.3's correction |
| IV | GF(2) | `n = 10`, `m = 7`, seed 0 | 455 | **exact** |
| V | GF(2^8) | `n = 15`, `m = 10`, seed 0; `n = 5`, `m = 3`, seed 0 | 1 350, 60 | **exact** |
| VI | GF(31) | `n = 15`, `m = 10`, seed 0; `n = 10`, `m = 7`, seed 0; `n = 5`, `m = 3`, seed 0 | 1 350, 455, 60 | **exact** |

Zero mismatches in 27 530 coefficients across all six types and both shapes. "Exact" is the whole
claim: not a distributional match, every coefficient.

### 7.3 Both shipped verifiers are broken

Neither archive reproduces the data it exists to check. Both failures are in the generator source,
both are one-line, and both are reported here rather than worked around.

**1. `generate31` rejects `31`, and the *toy examples* do not.** `generateCoef_enc.h`:

```c
coef = readPI(pos, 5);
while (coef == 31) {               /* not in the toy examples; yes in the real challenges */
        pos += interval;
        pos %= PI_LEN;
        coef = readPI(pos, 5);
}
```

Running `./coefVerifier 3 10 0` diverges from the genuine toy file at **polynomial 0, coefficient
55**, where the file has `31` and the verifier emits `30`; because the rejection also advances
`pos`, everything after that is shifted and **1 214 of 1 300 coefficients disagree**. Remove the
`while` loop and the match is exact. Same at `n = 15` (first divergence at coefficient 42,
3 884/4 050 disagree), `n = 20` (coefficient 14, 8 912/9 200) and `n = 10` seed 3 (coefficient 8,
1 263/1 300).

**The previous revision of this section then generalized, and was wrong to.** It is not that the
loop is a defect in the generator; it is that **the loop is a parameter of the file**, and the two
published classes are on opposite sides of it. Found by #420's implementation on its first run
against the data, which reproduced all nine toy examples exactly and disagreed with
`challenge-6-16-0` on 5 012 of 5 184 coefficients, first at polynomial 0 coefficient 24 — the
signature of a rejection, not of a misread.

Counted over the token streams:

| file | coefficients | `31` | `30` | mean per residue |
|---|---:|---:|---:|---:|
| `ToyExample-type3-n20-seed0` | 9 240 | **310** | 302 | 289 over 32 values |
| `ToyExample-type6-n15-seed0` | 1 360 | **40** | 57 | 42 over 32 values |
| `challenge-6-16-0` (real, `m = 16`) | 5 200 | **0** | 166 | 168 over 31 values |

Zero occurrences in 5 200 draws where the rate would put ~168 is not a sampling accident, and the
`30` count moving from "one of 32" to "one of 31" is the other side of the same change. So the real
challenges were generated **with** the rejection and the toy examples **without** it. Both are
reproducible; neither policy reproduces both. `MqParameters::thirty_one` carries it, and
`ThirtyOne`'s documentation is this table.

This affects types III and VI — the two families this crate imports — and only them: types I, II,
IV and V have no such loop, and no value a bit or a byte can hold is out of range anyway.

**2. The signature generator reads one coefficient too many per polynomial.**
`generateCoef_sig.h` loops `j < mon` where the encryption version loops `j < mon-1`, and prints no
literal constant, so it consumes a π value for the constant term and advances `pos` for it. The
published signature files do not: their first `mon-1` coefficients match the π stream exactly, and
their constants do not come from it. The first divergence is therefore at exactly the constant of
polynomial 0 — coefficient 65 of 66 at `n = 10`, 135 of 136 at `n = 15`, 20 of 21 at `n = 5` — and
the extra read desynchronizes every later polynomial. Verified for all three signature types.

**This one is also a parameter, and the shipped verifier is right about the file it was written
for.** The paragraph above is true of the signature *toy examples* and false of the real signature
challenges, which take `mon` reads per polynomial and whose constant **is** the last of them:
`challenge-6-16-0` and `challenge-5-16-0` each reproduce on all 325 coefficients of all 16
polynomials, constants included, under exactly the rule `generateCoef_sig.h` implements. Measured
by #420 at the same time as the rejection policy, and the two together give §7's three classes:

| class | reads per polynomial | the value `31` | the constant column | measured on |
|---|---|---|---|---|
| toy examples, all six types | `mon - 1` | kept | **not** from π | 27 530 coefficients, §7.2 |
| real encryption, types I–III | `mon - 1` | **resampled** | **not** from π | `challenge-3-34-0`, 42 840 |
| real signature, types IV–VI | **`mon`** | resampled | **from π** | `challenge-{5,6}-16-0`, 5 200 each |

So `guidance`'s claim that the signature verifier "can check all the coefficients including the
constant terms" is **true of the challenges and false of the toy examples** — the opposite of what
the previous revision of this section concluded from the toy examples alone.

Neither verifier is patched here: nothing in this repository runs them, and the reimplementation in
`src/grobner/research/mq_generator.rs` — which carries both axes as `ThirtyOne` and
`ConstantColumn` — is the check that is actually used.

### 7.4 The constant column

For the encryption types the constant is **by design** not from π, and `YDHTS15` says why.
Algorithm 1, Step 4:

> Select randomly a vector `x0` in `F^n`. … Compute `c^(k)` such that the associated system of
> equations has a solution `x0`.

and `YDHTS15` §4: "we construct the system corresponding to encryption scheme with a random
solution by adjusting the constant coefficients". So the encryption constants *are* the planted
answer, which is why `site`'s rule 4 says the challenge team will not compete in types I–III, and
why the verifier prints a literal `0` there. Fully explained, and consistent with the data.

For the signature types the previous revision recorded it as **not established**, and the two
authoritative statements as conflicting:

- `guidance`: "the coefficients are all chosen from PI digits, and the MQ challenge team do not
  know the answers".
- `YDHTS15` Algorithm 2: "Select randomly `a_ij`, `b_i`, `c^(k)` for all `i, j, k`" — all
  coefficients random, constants included.

**Established now, and `guidance` is right about the challenges.** A real signature challenge's
constants *are* from π: they are the `mon`-th read of each polynomial, under the rejection policy,
and `challenge-6-16-0` and `challenge-5-16-0` reproduce in full — 16 polynomials × 325
coefficients each, zero mismatches, nothing taken from the file but `n` and `m`. The evidence that
looked like a refutation was entirely about the toy examples, where it still holds: type VI
`n = 15` seed 0's ten constants are `[11, 2, 27, 4, 21, 23, 5, 16, 27, 20]`, and they are not
produced by continuing `pos` past the `m(mon-1)` main reads, nor by a second pass from `start`, nor
by any offset in the first 4 000 000 bits of `PI` at that instance's `interval`.

The consequence for this repository is the useful one. A **real signature challenge needs no
instance file at all** — `(type, m, seed)` and `PI` rebuild it exactly, which is what
`MqParameters::challenge` plus `GeneratedMq::into_instance` do, and it removes the redistribution
problem for types IV–VI outright. A **real encryption challenge** is rebuilt except for one column
per polynomial, and that column is the planted answer, so no walk can produce it and no walk should
pretend to: `into_instance_with_constants` takes it from the caller.

---

## 8. What the record records

### 8.1 Largest solved, and smallest unsolved

From `submissions` and the 37 detail pages behind it. "Largest solved" is the maximum over every
recorded solve, ranked by `n` for the encryption types and by `m` for the signature types, as the
challenge ranks them.

| type | largest solved | date | solver | algorithm | hardware | published figure |
|---|---|---|---|---|---|---|
| II | `n = 38` seed 0 | 2026-09-28 | Javier Verbel | XL with block Wiedemann | 2× AMD EPYC 7763, 16× 64 GB DDR4-3200 | 811 805 s (9 d 9 h 30 m) wall |
| III | `n = 38` seed 3 | 2020-08-03 | Chou, Niederhagen, Yang | XL with block Wiedemann | 2× AMD EPYC 7742 | 23.34 d wall; VmPeak 49.45 GB |
| V | `m = 21` seed 0 | 2026-09-17 | Ting Li, Yao Sun | improved F4 via smaller matrices | 2× RTX 5090 (32 GB each), 16 threads Intel 6530, 256 GB | 722 188 s (8 d 8 h 36 m) wall |
| VI | `m = 24` seed 0 | 2025-10-16 | Sakata, Takagi | HDF4 (Hilbert-driven F4) and MF4 (mutant F4) | 4× AMD EPYC 7763 | 994 320 s (11 d 12 h 12 m) wall |

"Smallest unsolved" has two answers and they are different numbers, so both are given. §8.3 is why
neither is a statement about hardness.

| type | sizes with a recorded solve | smallest size with **no** record | smallest `(size, seed)` with **no** record |
|---|---|---|---|
| II | `n = 35, 36, 37, 38` | `n = 39` | `(35, 1)` |
| III | `n = 34, 35, 36, 37, 38` | `n = 39` | `(34, 2)` |
| V | `m = 16…21` | `m = 22` | `(16, 3)` |
| VI | `m = 16…24` | `m = 25` | `(16, 2)` |

### 8.2 The only published comparands at sizes this crate reaches

Buried in the hall of fame under the name "Yun-Ju Huang / MQ challenge team" are four 2015
submissions on the **toy** examples. They are the lowest-ranked rows on the site and the most
useful ones here, because they are the only published results at sizes this repository has
actually imported.

| instance | solver | date | algorithm | hardware | published time |
|---|---|---|---|---|---|
| type II `n = 20` (`m = 40`) seed 0 | Yun-Ju Huang | 2015-03-20 | Magma V2.19-9, F4 | Intel Xeon E5-4617 @ 2.90 GHz, 1 TB RAM | **75.60 s** |
| type III `n = 20` (`m = 40`) seed 0 | Yun-Ju Huang | 2015-03-20 | Magma V2.19-9, F4 | Intel Xeon E5-4617 @ 2.90 GHz, 1 TB RAM | **259.27 s** |
| type V `n = 15` (`m = 10`) seed 0 | Yun-Ju Huang | 2015-03-20 | Magma V2.19-9, F4 | Intel Xeon E5-4617 @ 2.90 GHz, 1 TB RAM | **2 879.450 s** |
| type VI `n = 15` (`m = 10`) seed 0 | Yun-Ju Huang | 2015-03-20 | Magma V2.19-9, F4 | Intel Xeon E5-4617 @ 2.90 GHz, 1 TB RAM | **2 764.41 s** |

Two of those four are instances this repository has run and not solved (§4.1, §4.2): type III
`n = 20` crossed the 20 000 000-entry cap at degree 5, and type VI `n = 15` reached no verdict in
eight slices. **This is not a comparison and nothing here licenses one** — the budget that stopped
those runs is a deliberate entry cap, not an attempt at the published figure, and the 2015 machine
had 1 TB of RAM. What the four rows establish is that these instances *are* solvable by F4 on one
machine, which is a different and more useful fact than a time: a future attempt has a target that
is known to exist.

The hardware is the same machine `YDHTS15` §5 used for its own calibration experiments ("four
6-core Intel Xeon E5-4617 at 2.9 GHz"), which is consistent with these being the challenge team's
own setup runs.

### 8.3 Why the hall of fame is an undercount

`site`'s own rules, quoted so nobody reads the tables as a census:

> Concerning challenges with the same number of variables `n`, only the first five instances solved
> will be recorded.

> we allow the submissions of challenges with the same number of variables `n` … at most once per
> participant.

So a missing `(size, seed)` row means "not recorded", not "not solved": it could be a sixth solve
at that size, or a solve by someone who already holds a row at that size and is barred from
submitting another. The §8.1 "smallest with no record" columns are therefore an **upper bound on
how far the published record reaches**, not a lower bound on difficulty. Both rules are asserted
against the fixture by `fukuoka_mq_records::test_the_rows_obey_the_challenges_own_recording_rules`.

The front page shows five rows per type; `submissions` is the complete list, and it is where the
fixture comes from. For types II, III, V and VI the complete counts are 6, 8, 12 and 11, so the
front page shows 5 of 12 for type V and 5 of 11 for type VI — well under half of what is on
record.

### 8.4 The figures are not in one unit, and some are not totals

The 37 pages express "Running Time" in at least five conventions: `32 days 18 hours 26 minutes`,
`324,591 seconds`, `16.06 days`, `811805 seconds (9 days 9 hours 30 minutes)`, and
`370 cpu seconds for each subsystem`. The fixture converts all of them to seconds and keeps the
original string beside it so the conversion can be rechecked by eye.

**Five of the 37 figures are not totals.** Every signature-type record is a hybrid attack — guess
some variables, solve the rest, repeat — and five rows report the cost of *one* subsystem rather
than of the campaign. Type V `m = 16` seed 2 reads "370 cpu seconds for each subsystem" and would
be, quoted as a total, by far the fastest solve on the site. The fixture tags each figure
`wall-total`, `per-subsystem-cpu` or `per-subsystem-wall`, and
`fukuoka_mq_records::test_the_per_subsystem_figures_are_exactly_the_known_ones` pins the set of
five by name, because the distinction is invisible in the number.

**Two rows publish peak memory, with different metrics**: type III `n = 36` gives 29.77 GB
"peak memory demand (VmHWM)" and type III `n = 38` gives "VmPeak: 49.45 GB". Resident high-water
mark and peak virtual size are not the same number for the same run, so a figure without its
metric is not comparable with anything — including with `src/util/peak_memory.rs`. That is the
entire published evidence on memory for these four types.

The figures are **internally consistent where they can be checked**, which is the main reason to
trust the transcription. Six rows publish block-Wiedemann phase breakdowns, and in every case the
phases account for the stated total (exactly for the 2015 type III row; within 1.5 s on 811 805 for
the 2026 type II row; within 0.04% on the two that are printed only to hundredths of a day). Three
rows publish a subsystem count, a per-subsystem average and a process count, and every one of them
reproduces the stated total to better than 0.004%:

| row | derived | published | residual |
|---|---|---|---|
| VI `m = 22` 2023-11-14 | 3 × 61 102 / 1 = 183 306 s | 183 307 s | 0.0005% |
| V `m = 20` 2023-08-22 | 245 × 15 319 / 2 = 1 876 578 s | 1 876 608 s | 0.0016% |
| V `m = 21` 2026-09-17 | 80 × 9 027 / 1 = 722 160 s | 722 188 s | 0.0039% |

Three further rows publish a count and an average but are excluded. VI `m = 21` 2023-10-23 states
four simultaneous processes for four subsystems — one round — and comes out 2.6% above the derived
value, which is the campaign's own overhead; the fixture omits its process count so the test's 0.1%
tolerance can stay tight enough to catch a transposed digit. The **two 2025 type VI rows do not
reconcile at all**: 707 subsystems × 19 972 s against a stated total of 1 857 440 s implies
7.6-way parallelism, and 2 011 × 7 830 against 994 320 s implies 15.8-way — neither an integer, and
neither stated in the notes. Recorded as unreconciled rather than resolved; no figure here turns on
it.

---

## 9. Verifying a solution

The challenge's objective is a root of a polynomial system, so the witness check is substitution
and it is total: evaluate all `m` polynomials at the candidate and require every one to be zero.
No oracle, no reference implementation and no trust in the solver is needed. That is the cheapest
witness check of any family in this corpus apart from MinRank's single rank computation.

Three things make it worth stating precisely rather than assuming.

1. **Evaluate against the original coefficient vectors, not against anything derived.** A
   specialized or reduced system can have roots the original does not. §4's type VI campaigns do
   this, which is why their witnesses mean something.
2. **Evaluate in the right field.** §2.4: under the AES modulus every one of the twenty type II
   `n = 10` polynomials fails at the genuine answer. A verifier in the wrong GF(2^8) rejects every
   correct witness, and one in the wrong characteristic (§2.3) accepts wrong ones.
3. **Published answers are available far more widely than the toy `-answer` files suggest.** Every
   one of the 37 recorded solves prints its full answer vector on its detail page — asserted for
   the whole fixture by
   `fukuoka_mq_records::test_every_recorded_solve_publishes_an_answer_vector`. So for types II, III,
   V and VI there are 37 fetchable witnesses, not 4, and they reach up to `n = 38` and `m = 24`.
   They are a check on an *importer* long before they are a target for a solver: a correctly
   imported type III `n = 34` instance must vanish at the 2015 answer, and that costs one
   evaluation.

Answer-file syntax is `[v1, v2, …]`, decimal for GF(2) and GF(31) and two-digit hex for GF(2^8).
Both bases are handled — §2.5 item 3, #415 — and the same `MqField::radix` decides the base of a
coefficient row, which is #414.

---

## 10. Submitting

Recorded for completeness; **nothing has been or should be submitted under #70**.

`submission.html` is a web form with required fields Name, Type, Number of Variables `(n)`, Answer,
Algorithm and Runtime, plus optional Institute, Email, Hardware and Notes. The answer field's own
placeholder is `from x_1 to x_n, ex, [0h, 3a, 2b]`. Contact is `mqchallenge@googlegroups.com`
(`site`); `submission.html`'s own footer still gives the older ISIT Fukuoka address and
`mq-challenge@isit.or.jp`, while `site` and `guidance` give Okayama University of Science — the
footers disagree and the newer one is on the pages that have been updated since 2015.

`guidance` asks participants not to solve more than two instances at the same `n`, and
`site`'s rule 3 limits a participant to one recorded solve per `n`.

---

## 11. Corrections to the record

Collected so they are not buried.

1. **The site documents the format.** §2's previous text said "the site documents none of this; it
   was read off the toy examples". `format` specifies all three fields and expands two polynomials
   by hand, and `util.m` is the challenge's own reader. The empirical finding was right; the claim
   that it had to be empirical was not. (§2, §2.1)
2. **The GF(2^8) header is `GF(2)[x] / x^8 + x^4 + x^3 + x^2 + 1`.** Not `GF(2^8)`, not `GF(256)`.
   `MqField::parse` matched neither of the real spellings, so no genuine type II or type V file
   parsed. The header carries the modulus, which means it can be *verified* rather than assumed —
   and since #414 it is: `MqInstance::check_coefficient_field` derives the coefficient type's own
   modulus and refuses a mismatch, so `Gf256` is refused for a challenge file where `Gf256Mq` is
   accepted. (§2.5, #414)
3. **"The binary and extension field modules are not publicly exported" was stale in two places,
   and the real blocker was different.** Both modules have been public since `8757b4a`; the thing
   that actually prevented a GF(2^8) parse was `todo!()` in `FiniteField::new`/`from_str`, closed
   by #377. (§6)
4. **Toy examples exist for all six types**, at `n = 10, 15, 20` for types I–III and
   `n = 5, 10, 15` for types IV–VI. The previous revision recorded only type III's and type VI's.
   (§1)
5. **The published challenge sizes start at `n = 34`/`m = 16`, not `n = 55`.** `n = 55…100` is types
   I and IV. (§1, §6)
6. **`n ≈ 1.5m` is `floor(3m/2)` exactly**, from the generator's own `int n = m * 1.5`. (§1, §7.1)
7. **The `0..=31` coefficient range is confirmed from the generator**, not just from a histogram: a
   GF(31) coefficient is five raw bits of π. The earlier inference "the generator evidently produced
   values mod 32" was correct. (§2.2, §7.1)
8. **Both official coefficient verifiers fail to reproduce the published instances.** The GF(31)
   encryption generator adds a `31`-rejection the data does not have; the signature generator reads
   one coefficient too many per polynomial. (§7.3)
9. **`guidance`'s claim that the signature verifier checks the constant terms is false.** The
   published signature constants are not from the π stream. (§7.3, §7.4)
10. **The hall of fame is not a census.** The site's own rules 2 and 3 make it an undercount, so a
    missing `(size, seed)` is not evidence of an unsolved instance. (§8.3)
11. **Five of the 37 published runtimes are per-subsystem, not totals**, and two peak-memory
    figures use different metrics. Quoting either kind as a total is a category error the site does
    not flag. (§8.4)

---

## 12. What this means for #73 (A4)

#73 drafts a common schema and should be drafted against what A1 actually imported. Five findings
bear on it. `minrank.md` §7 raised three gaps; the third of those is reinforced here and four are
new.

1. **"A deterministic generator plus its parameters" has to be a first-class entry shape, and for
   this source it is the *preferred* one.** #73's field 3 offers it as an alternative to embedding
   the system. For Fukuoka it is strictly better: `(type, n, seed)` plus `PI`'s digest regenerates
   the instance exactly (§7.2), which sidesteps #73's whole embedded-data-versus-download-recipe
   question for 760 instance files at the cost of three integers. The caveat is sharp and must be
   expressible: it regenerates **all but one coefficient per polynomial**, the constant column
   (§7.4). A schema that cannot say "reproducible except for this column" would have to call these
   either reproducible or not, and both are wrong.
2. **The generator artifact's digest is not the instance's digest.** #73's field 1 asks for "content
   hash of the downloaded artifact", singular. Here there are two unrelated artifacts — the 200 MB
   `PI` (`58f55ded…`) and the instance file (`9436e45d…`) — and an entry may legitimately pin only
   the first. Both need a place.
3. **A non-prime field's modulus must be mandatory, not optional.** #73's field 2 lists "modulus or
   irreducible polynomial" alongside characteristic and degree. §2.4 shows the order is not enough
   to identify the field: two GF(2^8)s with different irreducible polynomials have the same order
   and different arithmetic, and reading the challenge's bytes under the AES modulus makes every
   polynomial fail at the genuine answer. An entry over a non-prime field without a modulus is not
   under-specified, it is ambiguous between two different problems.
4. **A published figure needs its unit *and* its scope *and* its metric.** This is `minrank.md`
   §7's third gap, and this family makes it concrete rather than merely acute. One source produced,
   for the same four types: five time conventions, figures that are wall-clock totals and figures
   that are the CPU cost of one subsystem of an unstated number (§8.4), and two memory figures under
   two different metrics (VmHWM and VmPeak). #73's field 8 distinguishes measured from extrapolated,
   which is necessary and not sufficient: a measured per-subsystem CPU figure and a measured
   wall-clock total are both measured and are not the same kind of number. Structure, not prose —
   `fukuoka_mq_records::test_the_per_subsystem_figures_are_exactly_the_known_ones` exists because
   the distinction is invisible in the value.
5. **An entry can carry many witnesses, each with its own provenance, and most of them are not in
   the instance archive.** #73's field 5 reads as one optional published solution. Here every one of
   the 37 recorded solves publishes a full answer vector on its own URL (§9), reaching to `n = 38`
   and `m = 24` — far past any instance with an `-answer` file. Those are importer checks available
   today at sizes no solver here will reach for a long time, and a schema that holds one witness per
   entry cannot express them.

A sixth point is scope rather than schema: Singular can serve as the oracle for these entries, since
they are small-field, consistent with #73's note on `differential/comparison.rs`. But for a Fukuoka
entry it is not needed — substitution against the published answer is cheaper and independent of
any other implementation.

---

## 13. Secondary-only, uncertain, and not established

**Nothing in §0–§10 rests on secondary literature.** Every parameter, format detail, generator rule,
record, date, solver, algorithm and hardware string was read from the challenge's own pages, its own
utility downloads, or the paper it names as its reference. There is no equivalent here of
`minrank.md` §9's secondary-only table, and that is a property of this source rather than of the
effort: the Fukuoka challenge is unusually well documented and still live.

**Not established.**

- **Where the signature types' constant terms come from.** §7.4. `guidance` says π, `YDHTS15` says
  random, and the data rules out the natural π reading. Recorded as unresolved rather than
  reconstructed, which is the point of the exercise.
- **Whether `PI`'s 200 000 000 characters really are π's binary expansion.** It is the generator's
  input and every published coefficient follows from it, so nothing in §7 depends on the answer.
  Spot-checking was not done: the file does not begin at π's binary point, so a check would need the
  offset, which is not published.
- **Whether the published answers for the solved real instances actually satisfy those instances.**
  Not checked — it would mean downloading up to `n = 38` challenge files, and the import path for
  the GF(2^8) half does not exist (§6). The toy-size answers were checked and all pass (§2.4, §7.2).
- **Why the two 2025 type VI rows' totals do not follow from their own subsystem counts and
  averages** (§8.4). The notes omit the parallelism; the implied figures are 7.6 and 15.8.
- **Whether any `(size, seed)` pair without a record has in fact been solved.** Unfalsifiable from
  here, and §8.3 is why it is likely for the low sizes.
- **The 2.6% residual on type VI `m = 21` 2023-10-23** (§8.4) is attributed to campaign overhead,
  which is plausible and not stated by the source.
- **The contact-address disagreement** between `submission.html`'s footer and `site`'s (§10). Both
  are on the live site; the newer appears on the pages that have been updated since 2015.

**Attempted and failed, with what was tried.**

| target | what was tried | result |
|---|---|---|
| `YDHTS15` from the publisher | `https://eprint.iacr.org/2015/275.pdf`, the URL `site` itself links | **`403`**, 5 409 bytes of error page. Matches `minrank.md` §9 and `elimination-beyond-grobner.md` §8: this host's PDFs are blocked from here while its abstract pages are not. **Obtained** from the Wayback Machine instead, and the CDX index shows one content digest across captures 2015-09-08 to 2021-10-05, so the snapshot is the document the challenge has linked throughout |
| the π recipe for the signature constants | continuing `pos` past the `m(mon-1)` main reads; a second pass from `start`; and an exhaustive scan of the first 4 000 000 bits of `PI` for any offset reproducing all ten of type VI `n = 15` seed 0's constants at this instance's `interval` | **not found.** §7.4. The scan covers 2% of the file, so this is "not found", not "not there" |
| the π recipe read directly off decimal or base-32 digits of π | computed π's binary expansion independently by the Machin arctan series (verified against the known decimal and hex digits) and searched its base-32, base-32-mod-31, decimal-pair and base-256 expansions for the first eight coefficients of type III `n=10` seed 0 and type II `n=10` seed 0 | **not found**, in streams of 1 598 base-32, 1 200 decimal-pair and 998 base-256 digits. Superseded and explained by §7.1: the offset is `type*n` and the stride is `(seed+n)*10+type`, so no contiguous reading of π could have matched |
| a published answer for an unsolved instance | — | **none exists, by construction.** `site` rule 4: for types I–III the team plants and keeps one answer; for types IV–VI "the MQ challenge team do not know the answers". So the only answers for signature types are the ones solvers submitted, which is exactly the 37 detail pages (§9) |
| the challenge's own GF(31) verifier, run against its own data | built `CoefVerifier_enc` and ran `./coefVerifier 3 10 0` | **mismatched 1 214 of 1 300 coefficients.** Not an environment problem — §7.3 isolates it to a `while (coef == 31)` loop that the published data does not have, and removing it gives an exact match |
