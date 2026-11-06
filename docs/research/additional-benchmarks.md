# Additional research benchmarks: the shortlist, what was rejected, and why

Deliverable for A3 (#72), a child of the benchmark-corpus epic #65. A1 (#70) covered the Fukuoka MQ
Challenge — see [`fukuoka-mq.md`](fukuoka-mq.md) — and A2 (#71) the Ethereum Foundation challenges.
This issue surveys the rest of the published landscape and answers one question: **which instances
carry a published number that zeebra could be right or wrong against?**

It is a shortlist, not a reading list. Nothing here authorizes an implementation. M23-0 froze the
challenge registry while this survey was in progress, which is the gate every candidate below has to
pass through; §6 re-checks the schema conclusions against what it actually froze, and finds one gap
that should be closed before the first candidate is registered.

## 1. The shortlist, ranked

Four candidates are accepted against a cap of five. The fourth is held behind an interface
prerequisite and the first two are the ones worth doing.

| # | Candidate | Field | External reference point | Status |
|---|---|---|---|---|
| 1 | Anemoi `ℓ=1` CICO, `N = 1..8` rounds, models `FCICO` and `PCICO` | `GF(p)`, p ∈ {2³²−209, 2⁶⁴−353, BN-254, BLS12-381} | per-round Magma F4 and FGLM times, `d_reg`, and quotient dimension, **in raw logs under MIT** | accept — rank 1 |
| 2 | Griffin `t=12, α=3`, `r ∈ {5,6,7}` CICO | `GF(p)`, p = 28407454060060787 | per-step times and peak memory, plus **five published CICO witnesses** | accept — rank 2, reconstruction verified (§2) |
| 3 | Anemoi `ACICO` — a third model of candidate 1, not a new primitive | `GF(p)`, p = 1481823929 | solving degree constant in rounds; GB computed past 100 rounds | accept — rank 3, cheap given 1 |
| 4 | LowMC reduced-round, full S-box layer `(n,s) ∈ {(129,43),(192,64),(255,85)}`, `r ∈ {2,3,4}` | `GF(2)` | **claimed complexities only** — `log₂ T`, `log₂ M`; no runtimes, no challenge files | accept, blocked — §5 |

Rejected: UOV, MAYO, Arion, XHash8, and STAP Zoo as a dependency. See §7.

Ranking rationale, in one line each:

1. **Anemoi via `six-worlds-anemoi`** — the only candidate whose external reference point is
   *redistributable raw data* rather than a number in a table, the only one with a
   machine-independent invariant zeebra can check (§3.2), and the one that lands on the part of
   zeebra that is actually weakest.
2. **Griffin via the FreeLunch appendix** — the only candidate with a published witness, which makes
   correctness checkable rather than merely plausible, and the only one with a measured
   memory ladder from 14 MB to 27.6 GB.
3. **Anemoi `ACICO`** — a second formulation of a primitive candidate 1 already requires, so it
   costs a model and not an implementation, and it feeds C2 (#79) directly.
4. **LowMC** — a genuinely different problem shape, and the only `GF(2)` entry, but it needs
   `binary_field` exported first and its published results are not computations.

## 2. The reconstruction check: Griffin passes, and the witness settles an ambiguity

The issue's go/no-go is a reconstruction check — can one published parameter set be instantiated
from the specification in hand, without guessing? The target chosen was Griffin with
`(t, α) = (12, 3)` reduced to `r ∈ {5, 6, 7}` rounds over the 55-bit prime
`p = 28407454060060787`, which is the instance the FreeLunch experiments of Table 3 were run on.
`tools/check-griffin-reconstruction.py` is the check; it runs in 43 ms and needs only the standard
library.

**Result: pass.** All five published CICO solutions — two at `r=5`, two at `r=6`, one at `r=7` — are
reproduced exactly, with the zero first coordinate at both ends that is the CICO condition.

Two things had to be resolved, and the difference between them is the point of the exercise.

**The linear layer is not in the paper.** Definition 11 says only "for `M ∈ F^{t×t}` a matrix".
The construction comes from the designers' reference implementation, `instantiate_matrix` in
`plain_impls/src/griffin/griffin_params.rs` of
<https://extgit.isec.tugraz.at/krypto/zkfriendlyhashzoo>: for `t` divisible by four, entry `(i,j)`
is `M₄[i mod 4][j mod 4]`, doubled when `i` and `j` fall in the same four-wide block, with

```text
M₄ = [[5,7,1,3],
      [4,6,1,1],
      [1,3,5,7],
      [1,1,4,6]]
```

It depends on `t` alone — no randomness, no field-specific choice — so it is a dependency on a
*source*, not on a guess. This is the answer to investigation task 2 for Griffin: **reconstructible
from the paper plus one named function of the reference implementation.**

**The `(δ, µ)` index convention is ambiguous, and the witness decides it.** The appendix gives
`δᵢ = 4(i+1)`, `µᵢ = 7(i+1)²` for `i = 0, …, r-1`, but `δ` and `µ` are indexed by *branch*, of which
there are `t = 12`, not by round. Both readings were tried:

| reading | published solutions reproduced |
|---|---|
| branch `i` takes `(4(i+1), 7(i+1)²)` | 0 / 5 |
| branch `i` takes the `(i-2)`-th pair, `(4(i-1), 7(i-1)²)` | **5 / 5** |

The second matches the reference implementation, where `alpha_beta` has length `t-2` and is indexed
from zero for branches `2 … t-1`. **This is not a guess** — the published input/output pairs are a
decision procedure, and a wrong reading fails all five. An instance with published parameters but no
witness would have left this undecidable, which is the argument for ranking Griffin above everything
that lacks one.

A consistency check that costs nothing: Griffin requires `δᵢ² - 4µᵢ` to be a quadratic non-residue.
For the published formula that is `-12(i+1)²`, so the condition reduces to `-12` being a non-residue
mod `p` — it is, and the script asserts it before doing anything else.

## 3. Anemoi: the strongest candidate, and the three models of it

### 3.1 What is published

Anemoi is specified in Bouvier, Briaud, Chaidos, Perrin, Salen, Velichkov and Willems,
*New Design Techniques for Efficient Arithmetization-Oriented Hash Functions: Anemoi Permutations
and Jive Compression Mode*, CRYPTO 2023 — read at <https://hal.science/hal-04276646>. For odd
characteristic and `ℓ = 1` the permutation is `Anemoi(x,y) = M ∘ R_r ∘ … ∘ R_1(x,y)` with
`R_i(x,y) = H ∘ M(x + c_i, y + d_i)` and `M(x,y) = (2x + y, x + y)`. Round constants are **fully
derived in the paper** from the first two hundred digits of π: with
`π₀ = 1415926535897932…` and `π₁ = 8214808651328230…`, the constants are
`c_j^i = g(π₀^i)² + (π₀^i + π₁^j)^α` and `d_j^i = g(π₁^j)² + (π₀^i + π₁^j)^α + g⁻¹`.

The one implementation-defined choice is `g`, "a generator of the multiplicative subgroup". The
reference implementation <https://github.com/anemoi-hash/anemoi-hash> (MIT, commit `3e86ff0c`) takes
`F.multiplicative_generator()`, which is Sage's smallest primitive root — deterministic, but a
convention rather than a specification. **Record it as a reconstruction dependency**, not as a gap:
the same repository's `check_polynomial_verification` emits and checks the CICO polynomial system
itself, so it is also the oracle for a faithful generator, in exactly the role Sage played for the
Poseidon work in M21-B.

The two named hash instances are `AnemoiSponge-BN-254` and `AnemoiSponge-BLS12-381`, both claiming
127 bits of security. `prime_field_256.rs` already provides `Bn254Fr` and `Bls12_381Fr`.

### 3.2 The reference point: raw logs, not a table

Koschatko, Lüftenegger and Rechberger, *Exploring the Six Worlds of Gröbner Basis Cryptanalysis:
Application to Anemoi*, ToSC 2024 №4, pp. 138–190, DOI `10.46586/tosc.v2024.i4.138-190` — read from
<https://tosc.iacr.org> — publishes two algebraic models of Anemoi CICO (`FCICO`, `PCICO`), three
variable orderings each, and **all of its experimental output** at
<https://github.com/IAIK/six-worlds-anemoi> (MIT, commit `fa056e6f`). Experiments ran on an
Intel Xeon E5-2630 v3 @ 2.40 GHz with 378 GB RAM under Debian 11, Magma V2.26-2.

That repository is the reason this candidate ranks first. The `results/` files are complete verbose
Magma F4 logs — per-degree matrix dimensions, `d_reg` per step, quotient dimension, and separated
Gröbner-basis and FGLM timings — for `α ∈ {3,5,7,11}`, `p ∈ {65537, 2³²−209, 2⁶⁴−353, BN-254,
BLS12-381}`, and `GF(2ⁿ)` for `n ∈ {15,17,31,63,65,127,255,257}`. **MIT means the reference data can
be committed**, which the Fukuoka files cannot be.

For `α = 3`, `ℓ = 1`, `p = 2⁶⁴ − 353`, ordering `o1`:

| rounds `N` | `FCICO`: vars | GB (s) | FGLM (s) | `PCICO`: vars | GB (s) | FGLM (s) | quotient dim |
|---|---|---|---|---|---|---|---|
| 3 | 6 | 0.017 | 0.199 | 4 | 0.010 | 0.320 | 125 |
| 4 | 8 | 0.280 | 67.8 | 5 | 0.199 | 56.4 | 625 |
| 5 | 10 | 9.32 | 22057 | 6 | 5.70 | 15570 | 3125 |
| 6 | 12 | 132.5 | — | 7 | 372.2 | — | — |
| 7 | 14 | 1623 | — | 8 | 26402 | — | — |
| 8 | 16 | 18215 | — | — | — | — | — |

The logs stop reporting FGLM past `N=5`; the Gröbner step alone continues to `N=8`. **The
conversion, not the basis, is the wall** — at `N=5` FGLM costs 2400× the F4 that preceded it. For a
crate whose FGLM scalability is the subject of its own milestone document, that is the single most
useful fact in this issue.

`FCICO` uses `2N` variables with every generator of degree `α`; `PCICO` uses `N+1` variables with
degrees growing to `2N`. Same primitive, same solutions, two different shapes for a solver to meet —
which is C2 (#79) handed a ready-made experiment.

**An invariant worth more than any timing.** Across `α ∈ {3,5,7,11}` and both models, the measured
quotient dimension is exactly `(α+2)^N`:

| `α` | `N=1` | `N=2` | `N=3` | `N=4` |
|---|---|---|---|---|
| 3 | 5 | 25 | 125 | 625 |
| 5 | 7 | 49 | 343 | 2401 |
| 7 | 9 | 81 | 729 | — |
| 11 | 13 | 169 | 2197 | — |

`dim F_p[x]/I` does not depend on the machine, the library, or the wall clock, so zeebra can be
checked against it directly and a disagreement is a defect rather than a performance difference.
It is also the one number here that must be tagged `Claim::Observed` and not `Claim::Proved`: these
are measurements from one implementation, and the designers' corresponding statement is a
conjecture. The manifest's Proved/Observed distinction exists for precisely this.

### 3.3 The round numbers under attack

Six Worlds, Table 1, for `α = 3` and `ω = 2`, gives minimum round numbers in each of its six worlds
against the designers' 21 (128-bit) and 37 (256-bit); its headline is that **41 rather than 37
rounds would be needed for 256-bit security**, with no safety margin included. Its Table 2 compares
estimated attack complexity against FreeLunch and against the resultant-based work: for `α=3` at
256 bits and `ω = 2.81`, 246 bits (this work), 203 (FreeLunch).

FreeLunch's own Anemoi experiments (Table 7, `ℓ=1`, `α=3`) run `r = 3 … 7`, ending at
10725 s for `polyDet`, 156348 s for `matGen` and 42.3 GB. **Those are not reproducible as an
instance**: unlike Griffin, the FreeLunch paper publishes no Anemoi round constants, no `a`, and no
witness. Use the numbers as a difficulty scale, not as a target.

### 3.4 `ACICO`

Campa and Roy, *Gröbner Basis Cryptanalysis of Anemoi*, EUROCRYPT 2025 (eprint 2025/814),
introduce `ACICO`, a model designed so that the DRL (or weighted-DRL, for `α > 3`) Gröbner basis is
*structurally known*, extends past two branches, and admits a proof that the system is in shape
position — which makes FGLM applicable by construction rather than by observation.

**Source read: Luca Campa, *Gröbner Basis Cryptanalysis and its Application to Arithmetization
Oriented Symmetric Primitives*, Master's thesis, Università degli Studi di Udine, 2024,
CC BY-NC-SA, <https://netlibrary.aau.at/obvuklhs/content/titleinfo/11390967/full.pdf>**, whose
chapter 5.4.3 is the `ACICO` work, co-supervised by Roy. The eprint and Springer versions were not
retrievable from this environment — see §8. Any claim quoted from `ACICO` should cite the thesis
until the paper itself has been read, and the numeric `d_I` columns of its Tables 5.10–5.12 should
not be quoted at all: the values increment by one per round and so appear to be `log₂ d_I`, which
the captions do not say.

What is unambiguous, and what makes `ACICO` worth a model: experiments on `p = 1481823929` (31 bits)
on an Intel Xeon Gold 6342 @ 2.80 GHz with 48 GB RAM, using SageMath, msolve, Singular, Macaulay2,
NTL and FLINT, give a **solving degree that does not grow with the number of rounds** — 9, 30, 42
and 66 for `α = 3, 5, 7, 11` — with the Gröbner basis computed "for more than 100 rounds" in
single-digit milliseconds. The entire cost is the univariate-polynomial step and the factoring after
it. That corroborates §3.2 from an independent direction and sharpens it: under the right model the
basis is free and conversion is everything.

## 4. Griffin and the FreeLunch line

Bariant, Boeuf, Lemoine, Manterola Ayala, Øygarden, Perrin and Raddum, *The Algebraic FreeLunch:
Efficient Gröbner Basis Attacks Against Arithmetization-Oriented Primitives*, CRYPTO 2024 — read at
<https://inria.hal.science/hal-04690640>. The approach chooses a monomial order in which the natural
CICO system **already is** a Gröbner basis, so there is no F4 step at all; the attack is three
stages, `sysGen` → `matGen` (the multiplication matrix `T₀`) → `polyDet` (a determinant of a
structured polynomial matrix). Experiments: one core of an AMD EPYC 7352 @ 2.3 GHz with 250 GB,
`p = 0x64ec6dd0392073`, SageMath/Magma/NTL/FLINT for `sysGen`, FLINT for `matGen`, PML for
`polyDet`.

Griffin, `(t, α) = (12, 3)` — Table 3, with the §2 reconstruction:

| rounds | `log₂` polyDet | sysGen (s) | matGen (s) | polyDet (s) | memory |
|---|---|---|---|---|---|
| 5 | 26 | 0.17 | 0.02 | 0.53 | 14 MB |
| 6 | 34 | 4.0 | 6.67 | 50.78 | 471 MB |
| 7 | 41 | 2558 | 3361 | 5727 | 27.6 GB |

Full-round Griffin is 10 rounds at `t = 12`; the paper extrapolates `≈ 4.2·10¹¹` s on one core.

**What this candidate is and is not.** It is a pinned, witnessed instance with a calibrated
three-point difficulty ladder, over a 55-bit prime that needs no new arithmetic. It is *not* a
like-for-like comparison for zeebra's F4: FreeLunch's point is that its order makes the basis
computation vacuous, and the paper notes that the same system in grevlex "well exceeds the security
level" at the suggested round count. So the honest framing is the one epic #65 already allows — a
recorded outcome with the resource wall that stopped it, against a competitor figure for the same
instance. The `r=5` and `r=6` rungs are small enough that a failure would be informative rather
than inevitable.

A detail that matters for the manifest: the published witness is a **12-coordinate permutation
input**, while the polynomial system's variables are `x₀ … x_r`. Those are different coordinate
systems. See §6.

## 5. LowMC is a claimed-complexity competition, not a source of runnable instances

Stated explicitly because mistaking it for one would waste the effort. The LowMC Cryptanalysis
Challenge, <https://lowmcchallenge.github.io/>:

- The deliverable is **the fastest attack**, scored by "the biggest gain in efficiency over
  exhaustive search", with prizes in EUR. There are no challenge files to download and solve, and
  no submitted runtimes — the results tables report `log₂ T` in bit operations and `log₂ M` in bits.
- Data complexity is **1** — a single plaintext/ciphertext pair — which is what makes the setting
  interesting and also means there is no data to distribute.
- The two winning methods after the third round are "Linearization + G&D + MITM" (Banik, Barooti,
  Vaudenay, Yan; Asiacrypt 2021) and Dinur's "Polynomial Method" (Eurocrypt 2021).
- **The polynomial-method entries are not executable at any scale.** Full S-box layer, by the site's
  own tables: `(129,4)` is `log₂ T = 130` with `log₂ M > 65`; `(192,4)` is `188` with `> 95`;
  `(255,4)` is `245` with `> 120`. `2⁶⁵` bits is four exabytes. These are analytic estimates and the
  memory exponents say so.

What LowMC *is* good for, and why it is on the shortlist at rank 4:

- **Reduced-round instances are pinnable.** `lowmcchallenge/lowmcchallenge-material` (commit
  `73fdcee5`) carries reference implementations with the matrices and constants as committed data —
  `lowmc_129_43_4.py` with `matrices_and_constants_129_4.dat`, and the same for `(192,64,4)`,
  `(255,85,4)`, and the partial-S-box-layer sets `(128,1,140)`, `(128,10,14)`, `(192,10,21)`,
  `(256,10,28)`, `(192,1,210)`, `(256,1,280)`. A manifest can checksum those files.
- **Memory-model discipline.** A corpus whose entries all report seconds will not teach anything
  about a result stated as `log₂ M > 65`. zeebra already separates `estimated_peak_bytes` from
  `peak_resident_bytes` for this reason, and LowMC is where that separation would be exercised
  against an external claim.
- **A different problem shape.** `GF(2)`, full-state linear layers, and a key-recovery objective
  rather than CICO.

**Blocked, and on an interface rather than on mathematics.** `src/fields/mod.rs` declares
`mod binary_field;` — private, not exported — which is the same wall that makes `MqField` refuse the
Fukuoka `GF(2)` and `GF(2^8)` families by name. Until that module is public, nothing in this
candidate can be imported. Do not bundle the export with the import.

> **Superseded, 2026-11-06 (#218).** The export landed in `8757b4a` (2026-11-05): `src/fields/mod.rs`
> now `pub use`s `BinaryFieldElement`, `ExtensionFieldElement` and `IrreduciblePolynomial`. It
> arrived as a side effect of #123's `for_each_field!` work rather than as a deliberate unblocking,
> which is why this section did not notice. The instruction not to bundle the export with the import
> was followed — by accident, but followed.
>
> What #218 then found is that the export was never the substantive obstacle, and three things were:
>
> - **No test exercised the Gröbner stack in characteristic two at all.** That is now closed:
>   `grobner::tests::test_the_whole_pipeline_over_gf2` and its `Gf256` twin take a planted system
>   through F4, Buchberger agreement, FGLM, both routes to lex and `solve_one`, and **passed with no
>   change to the solver**. The stack was generic over `FiniteField` and the genericity held.
> - **There was no way to adjoin field equations**, without which a `GF(2)` measurement is about the
>   wrong ideal. `grobner::field_equations` now does, with the radicality consequence checked
>   against exhaustive enumeration. Over `GF(2)` the generator has degree 2 and is worth adjoining;
>   the module declines to make that choice for fields where it is not.
> - **The representation question is open and unmeasured**: `Monomial<N>` is an exponent array where
>   a bit set would do, and a sparse entry is `(usize, F)` padded to 16 bytes at any width — 16 bytes
>   per bit over `GF(2)`. Unchanged, and now the only one of the three still outstanding.
>
> So LowMC's rank-4 placement is unchanged on its merits — its published results are still claimed
> complexities rather than computations — but it is **no longer blocked**. #221 resumes it, and
> notes one thing this section missed: the partial-S-box-layer sets have `s = 1`, so a 3- or 4-round
> reduction of `(128,1,140)` is one S-box per round and genuinely small.

## 6. Consequences for the frozen registry (M23-0) and for A4 (#73)

**M23-0 landed `grobner::research::challenge` while this survey was in progress, and it changes the
answer here.** This section was first written against `InstanceManifest`; it has been re-checked
against the schema that actually exists. A `ChallengeManifest` defines a *problem* where an
`InstanceManifest` defines a *file*, its identity is a SHA-256 digest over family, objective tag and
parameters, and `registry()` is frozen by `test_the_registry_is_frozen`, which pins every id and
digest. Adding a family is therefore a deliberate edit that fails a test if it redefines anything —
the correct gate for everything in §1, and it is already in place.

### 6.1 Closed by M23-0

- **Generated instances.** Resolved. Identity is a parameter digest, and the module documentation
  says so outright: "a challenge need not be a file: the 2026 CICO targets are a sentence and five
  numbers, and their round constants are *derived* rather than published."
  `InstanceManifest::missing()` requiring `provenance.sha256` simply does not apply, and
  `ChallengeParameters::MqSystem` keeps a `sha256` for the one family whose problem *is* a file.
- **A witness in the permutation's coordinates.** Resolved. `CicoTarget::PlantedFrom { inputs, free }`
  records a witness as constrained and free *input words*, not as the polynomial system's variables.
  Griffin's published pairs fit it directly at `k = 1`.
- **The reduced-round framing.** `BenchmarkClass::FaithfulReduction { of }` and
  `Significance::ReducedInstanceWitness { of }` are precisely what every candidate in §1 is, and
  they make the "says nothing about the full-round primitive" caveat structural instead of
  editorial.
- **A weighted monomial order — withdrawn as a schema gap.** The FreeLunch order and `ACICO`'s
  `WDRL` are properties of an *attack*, not of a problem; they belong in
  `ExperimentRecord::configuration` and `transformations`. `InstanceManifest::monomial_order`
  describes a file's coefficient layout, which none of these candidates has an analogue of.

### 6.2 Still open, and it is the one that matters

**There is nowhere to put the published competitor figure.** `ExternalStatus` records *whether and
when* a problem was solved elsewhere — `NoneRecorded { as_of }`, `SolvedExternally { verified }`,
`PublishedWithAnswer` — and carries no time, no memory and no hardware. "FreeLunch reports 5727 s
for `polyDet` and 27.6 GB on one core of an AMD EPYC 7352 at 2.3 GHz" is still homeless: not an
instance property, not a zeebra measurement, and not a status. Every candidate in §1 is a candidate
*because* it has such a figure, so a reference-point record — paper, parameters, step, reported time
and memory, hardware, software — should be decided before the first one is registered. It must sit
outside `canonical()` for exactly the reason program metadata does: a corrected extrapolation must
not change a problem's identity.

### 6.3 What each candidate would require of the registry

- **`ChallengeParameters` needs an `AnemoiCico` variant, and the model must be inside it** — hence
  inside the digest. `FCICO` at `N=5` is ten generators of degree 3; `PCICO` at `N=5` is six
  generators of degrees up to 10. Same primitive, same solutions, two different polynomial systems.
  If the model is not in `canonical_lines`, two digests collide on problems a solver meets
  completely differently. This supersedes the earlier "record generator degrees" framing: the
  degrees follow from the model, so the model is the field.
- **`Objective::CicoExact` fits Anemoi and Griffin as written.** Its statement is about "the
  permutation-with-initial-linear-layer", and Griffin's Definition 11 does begin with `M × ·`. No
  new objective tag — and §2 of the scoreboard document is right that adding a relaxed one would
  change every digest that used it.
- **LowMC needs both a new parameters variant and a new objective.** Key recovery from a single
  plaintext/ciphertext pair is neither `CicoExact` nor `MqRoot`. A second reason to keep it at
  rank 4, beyond the `binary_field` export.
- **`ExternalStatus::PublishedWithAnswer` is the right status** for Griffin `r ∈ {5,6,7}` and for the
  `six-worlds-anemoi` rows, which makes `significance(true)` a `Reproduction` — honest, and the
  strongest claim available on a solved reduced instance.
- **Anemoi needs `derived_digest` more than Poseidon does.** That digest exists because a parameter
  checksum cannot notice a changed *generator*. Anemoi's round constants depend on `g`, which the
  reference implementation takes to be `F.multiplicative_generator()` — a Sage convention rather than
  a specified value, per §3.1 — so the constants are exactly the kind of thing that could change
  under an unchanged identity.

## 7. Rejection list

| Rejected | Reason |
|---|---|
| **UOV** | Round-2 parameter sets, from `src/params.h` of the reference implementation <https://github.com/pqov/pqov>, are `GF(16)` `n=160, m=64` and `GF(256)` `n=119, m=45` / `n=193, m=72` / `n=259, m=96`. All are far out of reach, and no published *reduced* parameter set with a *measured* attack runtime was found: "Oil and Vinegar: Modern Parameters and Implementations" (TCHES 2023) is an implementation paper, not a cryptanalysis-at-toy-scale paper. A shrink we choose ourselves has no external number, which is the one thing the corpus is for. Also `GF(16)`/`GF(256)`, so blocked on `extension_field` as well. |
| **MAYO** | The Round-3 specification, <https://pqmayo.org/assets/specs/mayo-round3.pdf>, gives `MAYO1/2/3/5` as `(n,m,o,k,q) = (88,80,8,10,16)`, `(86,64,13,5,16)`, `(118,108,10,11,16)`, `(154,142,12,12,16)`. Table 2.2's "additional parameter sets" are trade-offs *at the same NIST levels 1/3/5*, not reduced instances; the specification contains no toy parameters and no attack experiments. Same verdict and same `GF(16)` blocker as UOV. The issue anticipated this and said to be prepared to reject it. |
| **Arion / ArionHash** | FreeLunch Table 5 reports 2-round Arion with `(e, α) = (3, 121)` across 3–8 branches, and the memory is already 3.4–134 GB *at two rounds* — a one-rung ladder that starts above Griffin's top rung. No round constants and no witness are published, so it is not reconstructible either. The primitive's own ToSC 2026 paper exists; nothing changes the ladder. |
| **XHash8** | FreeLunch's own conclusion is that `polyDet` costs about `2²¹⁴`, "significantly higher than brute force", so XHash8 "seems very secure against the techniques presented in this paper". A target with no practical published result calibrates nothing. |
| **STAP Zoo as a dependency** | `https://stap-zoo.com/` is **unreachable from this environment**, independently from two clients: `curl` gets `TLS connect error: … ssl/tls alert handshake failure` and bare `openssl s_client` gets `SSL alert number 40` with no peer certificate, under TLS 1.3 and when forced to TLS 1.2; `WebFetch` gets `HANDSHAKE_FAILURE_ON_CLIENT_HELLO`. DNS resolves to `141.193.213.10/.11`. The issue recorded the same failure on 2026-11-04 and this confirms it is not transient. It may still be a useful *human* lookup for whether a primitive's parameters were revised after an attack; it must not become a CI or fetch-script dependency. Browser reachability was not re-tested here. |

## 8. Source retrieval, and a note for A4's fetch scripts

**`eprint.iacr.org` PDF paths return HTTP 403 from this environment** — bot protection, consistent
across `curl` with a browser user-agent and referer, across HTTP/1.1, on both `/2024/347.pdf` and
the versioned `/archive/2024/347/<timestamp>.pdf` form, and from `WebFetch`. The *abstract* pages
fetch fine. This is an operational constraint on the corpus, not an inconvenience: any provenance
record that names an eprint PDF as its fetch URL will fail in CI here.

Everything in this document was read from a mirror that does work:

| Document | Read from |
|---|---|
| FreeLunch (CRYPTO 2024) | <https://inria.hal.science/hal-04690640/document> |
| Anemoi (CRYPTO 2023) | <https://hal.science/hal-04276646/document> |
| Six Worlds (ToSC 2024 №4) | `tosc.iacr.org`, article 11953 — ToSC is open access |
| `ACICO` | Campa's thesis at `netlibrary.aau.at` — see §3.4 for the caveat |
| MAYO Round-3 specification | <https://pqmayo.org/assets/specs/mayo-round3.pdf> |
| UOV parameters | `src/params.h`, <https://github.com/pqov/pqov> |
| LowMC challenge and material | `lowmcchallenge.github.io`, `github.com/lowmcchallenge/lowmcchallenge-material` |
| Griffin linear layer | `extgit.isec.tugraz.at/krypto/zkfriendlyhashzoo` (GitLab API) |

Recommendation for A4: provenance should allow a **mirror URL alongside the canonical one**, and
fetch scripts should prefer HAL, ToSC and GitHub raw over eprint. The UOV specification itself is
hosted on Google Drive, which is worse still.

## 9. What this issue did not do

- **No solving, and no generator.** The reconstruction check evaluates a permutation; it does not
  build a polynomial system or call F4. Candidates 1–4 are proposals.
- **The eprint versions of `ACICO` (2025/814) and of Griffin (2022/403) were not read.** Griffin's
  specification was reached through the FreeLunch restatement and the reference implementation,
  which §2 then verified against published witnesses; `ACICO` was read in the thesis. Both gaps are
  recorded above rather than papered over.
- **Anemoi over `GF(2ⁿ)` was not assessed.** The `six-worlds-anemoi` results cover
  `n ∈ {15,…,257}`, FreeLunch leaves even characteristic as future work, and zeebra's
  `binary_field`/`extension_field` are private. It is a real extension of candidate 1 and it waits
  on the same export as candidate 4.
- **No comparison against A2's Ethereum Foundation material.** If A2 lands a Poseidon or Rescue
  instance, the overlap with candidate 1 — both prime-field CICO, both FGLM-dominated — should be
  checked before both are imported.
