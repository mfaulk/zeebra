# Fukuoka MQ Challenge: format, what was verified, and what is reachable

Reference for M21-A (#92), which consumes #70 and #73.
Source: <https://www.mqchallenge.org/>

## 1. The challenge

Six families of random multivariate quadratic systems over three fields, in two shapes:

| type | field | shape | `m` vs `n` | importable here |
|---|---|---|---|---|
| I | GF(2) | encryption | `m = 2n` | **no** — no import path; the field exists (§6) |
| II | GF(2^8) | encryption | `m = 2n` | **no** — no import path, and the modulus differs (§2.4) |
| III | GF(31) | encryption | `m = 2n` | **yes** |
| IV | GF(2) | signature | `n ≈ 1.5m` | **no** — as type I |
| V | GF(2^8) | signature | `n ≈ 1.5m` | **no** — as type II |
| VI | GF(31) | signature | `n ≈ 1.5m` | **yes** |

**The "importable here" column used to read "`binary_field.rs` is private" and
"`extension_field.rs` is private". That is no longer the reason** — both modules have been publicly
exported since `8757b4a` (2026-11-05), which arrived as a side effect of #123's `for_each_field!`
work rather than as a deliberate unblocking. §2.4 and §6 record what actually remains.

GF(31) needed **no new arithmetic**: `PrimeFieldElement64<31>` already existed. The 32-bit prime
field of issue #62 has since landed as `Zp31`, and was an independent optimization rather than a
prerequisite — which was worth settling before the first importer PR, because the plan's §6.2 left
it ambiguous.

GF(2^8) is the one real gap, and it is interface work rather than mathematics: the binary and
extension field modules exist and are not publicly exported. Deliberate scope, and deliberately
not smuggled into this PR.

Published sizes run `n = 55` to `n = 100`. Toy examples are published at `n = 10, 15, 20` for
type III and `n = 5, 10, 15` for type VI — not the same sizes for both, which the fetch script
lists explicitly rather than looping over a common range.

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

One line per polynomial, terminated by ` ;`, each carrying `n(n+1)/2 + n + 1` coefficients — 66
for `n = 10`. A companion `-answer` file holds the published solution as `[22, 22, 28, ...]`.

The site documents none of this; it was read off the toy examples.

### 2.1 The monomial layout, verified rather than assumed

**The coefficient vector is every monomial of degree at most two, in descending grevlex order.**

That is what the file's own `Order` header says, but the header does not say how a coefficient
*vector* is indexed, and a monomial-order translation error is the failure mode an importer has —
silent, and it produces a different polynomial system that is wrong everywhere.

So it was determined empirically. Four candidate layouts were evaluated at the published answer for
type III `n=10` seed 0:

| candidate layout | all 20 polynomials vanish? |
|---|---|
| upper-triangular column-major, then linear, then constant | **yes** |
| row-major | no |
| upper-triangular column-major, reversed | no |
| row-major, reversed | no |

And the winning enumeration was then checked to be *exactly* descending grevlex over all monomials
of degree ≤ 2 — it is, so the importer sorts with `MonomialOrder::GradedReverseLexicographic`
rather than reimplementing an index pattern. A hand-rolled loop that happened to agree would be a
coincidence nobody could check; the test asserts the sort is strictly descending under that order
*and* that the reconstruction vanishes at the published answer.

Concretely, for `n = 4` the first few are
`x0², x0x1, x1², x0x2, x1x2, x2², x0x3, …`, then `x0, x1, x2, x3`, then `1`.

### 2.2 Coefficients are uniform over `0..=31`, not `0..=30`

`31` appears literally in the published GF(31) files and is congruent to zero. Counted over type-III
`n=10` seed 0, across its 1,320 coefficients:

| residue | 0 | 1 | 2 | … | 30 | 31 |
|---|---:|---:|---:|---|---:|---:|
| count | 46 | 55 | 35 | … | 38 | 40 |

So 0 and 31 both occur, each about 1/32 of the time, and **zero is therefore twice as likely as any
other coefficient** in the published data: 86 of 1,320 against roughly 40. The generator evidently
produced values mod 32. Not a defect to correct — the instances are what they are — but worth
recording rather than rediscovering, and it decides a parser question: the importer accepts
`0..=q` and reduces, rather than rejecting `q` as out of range. `32` is rejected.

It is also a small bias in the challenge instances themselves, which anyone quoting a solving-degree
measurement against random MQ systems should know about.

## 2.3 The coefficient type is checked, not assumed

`MqInstance::system` is bounded on `F: KnownOrder`, not `F: FiniteField`, and that bound is the
point: a field whose order cannot be read cannot be compared against the header, and an unchecked
coefficient type silently reduces every coefficient into the wrong field.

The first version checked only that the *header* said GF(31). A reviewer caught that
`instance.system::<10, PrimeFieldElement64<7>>()` therefore built a system with every coefficient
reduced modulo seven — a different mathematical problem, whose solutions and Gröbner behaviour
cannot be attributed to the challenge. Nothing about the resulting system looks wrong, which is
what makes it worth a type bound rather than a convention.

`check_coefficient_field` answers two separate questions in order: whether this importer has a path
for the field at all (GF(2) and GF(2^8) do not, per §2.4), and whether the supplied type *is* that
field. Orders are compared as limb slices rather than integers, because a field order need not fit a
`u64` — the comparison has to be right for the wide fields M20 added, not only for the ones this
importer reaches.

Note what that check does **not** catch, and §2.4 is about: order alone does not determine a
non-prime field. Two GF(2^8)s with different irreducible polynomials have the same order and
different arithmetic, so `F::order_limbs() == [256]` would accept either.

## 2.4 GF(2^8) is not one field, and the challenge does not use the AES one

`format.html` (read 2026-11-06) specifies the field as

> `p(x) = x^8 + x^4 + x^3 + x^2 + 1`

That is `0x11D`. `fields::Gf256` is `BinaryFieldElement<X8_X4_X3_X_1>` = `0x11B`, **the AES
polynomial** — one bit apart, `x` where the challenge has `x^2`. Both are irreducible of degree
eight and the two fields are isomorphic, but they are not the same field: the arithmetic reduces
modulo different polynomials, so one pair of bytes has two products. Over the AES modulus
`0x57 * 0x83 = 0xc1` (FIPS-197 §4.2); over the challenge's it does not, and of the 65025 nonzero
operand pairs more than fifty thousand separate the two.

So reading a type II or type V coefficient byte under `Gf256` would build **a different system from
the published one**, with nothing about the result looking wrong — the same class of error §2.1
guarded against for the monomial layout, which was verified rather than assumed. The layout was
checked at the time because a type III instance was being imported; the field representation was
not, because no GF(2^8) instance was.

`fields::Gf256Mq` is the challenge's field, declared separately for that reason and certified
irreducible by `binary_field::tests::test_declared_moduli_are_irreducible`.
`binary_field::tests::test_the_two_degree_eight_moduli_are_different_fields` asserts the
distinction rather than describing it. The stronger check — that a published answer file evaluates
every polynomial to zero under `0x11D` and fails to under `0x11B` — belongs with the import itself
and is #197's.

## 3. Redistribution

> COPYRIGHT © 2015 FUKUOKA MQ CHALLENGE All Right Reserved.

No stated licence. **The instance files are not committed to this repository.**
`tools/fetch-mq-challenge.sh` fetches them into `research/instances/mq/` (gitignored) and verifies
the SHA-256 of each file a manifest or test names:

```sh
tools/fetch-mq-challenge.sh            # fetch and verify
tools/fetch-mq-challenge.sh --verify   # check what is already there
```

The checksums are what make a result reproducible without redistributing the data, which is exactly
what `Provenance::sha256` and `Provenance::redistribution` are for. Unconditional parser coverage
comes from a hand-written fixture in the same format; the test against the genuine instance is
`#[ignore]`d, because a test that silently passed when its data is absent would be worse than no
test.

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
precisely so that implementations can check themselves, and `n = 10` is 45 variables short of the
smallest unsolved challenge. What it establishes is that the import is faithful and the pipeline
runs end to end on data this project did not generate.

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
and the point that came back is the one the challenge publishes. M22 had computed a basis for this
instance; this completes the pipeline to a checked witness.

`n = 20` crosses the entry cap at degree 5 after 67.5 s. So the published type III toy examples end
at `n = 15` under this budget, and `n = 20` is the first one that does not fit. Both figures are
reproducible resource bounds rather than timeouts.

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

## 5. What type VI is for

Type VI is the signature family: `n ≈ 1.5m`, so **underdetermined** — `n = 10` carries only 7
polynomials. That makes it positive-dimensional and out of scope for the zero-dimensional solvers
as it stands, which is M21-E's case rather than a failure. The natural experiment is to fix
`n − m = 3` variables and solve the slice, with every recovered point verified against the original
coefficient vectors and every dead slice recorded as the experiment it is.

## 6. Open

- **GF(2^8) import** needs the import path and a check against a published answer file under the
  **right modulus** — `Gf256Mq` (`0x11D`), not `Gf256` (`0x11B`). §2.4. The export it used to be
  blocked on landed in `8757b4a`; the modulus is the live issue and it is a correctness one. #197.
- **GF(2) import** needs the import path and the toy dimensions types I and IV publish, which are
  not type III's or type VI's. The field exists two ways — `fields::Zp2`
  (`PrimeFieldElement32<2>`, which keeps the wide-remainder path because `2^32` is not invertible
  modulo an even number) and `BinaryFieldElement<0b11>` — and which one the importer should use is
  a decision to record once, not per call site. #197.
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
- **`n = 55` and up** are far beyond the current solvers; `SUPPORTED_DIMENSIONS` is `[10, 15, 20]`
  and an unsupported size is `MqError::UnsupportedDimension` rather than a panic. Compiling
  dimensions that cannot be used would be worse than saying so.
- **A 32-bit prime field** (#62) landed, as `Zp31`. It halves the bytes a *dense* elimination moves
  and is worth 2.8x there, but the solver's default `Backend::Adaptive` gains nothing measurable —
  0.98x to 1.04x — because a sparse entry is `(usize, F)` and the index's alignment pads it to 16
  bytes at either width. Measured in
  `docs/MILESTONE-SIMD-PARALLELISM.md` §8; the importer is unaffected either way.
