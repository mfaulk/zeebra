# Feistel-MiMC and Rescue-Prime: generated, checked against the reference, and measured

**Measured at:** `PENDING_SHA`

#203 (C7). The executable follow-on to `docs/research/ef-cryptanalysis.md` §4, which is #71's
survey and **landed on 2026-11-08** — so this document does not restate the survey. What it adds is
two faithful generators, the formulation question answered with a measurement, and the two
rejections stated so they are not reopened.

## 0. The premise shifted, and what that changed

#203 was written when #71 (A2) was open with no deliverable, and it says so: "there is no
`docs/research/ethereum-foundation` document". That is no longer true. `ef-cryptanalysis.md`
answers #203's research questions 1, 2, 4, 5 and the field question in full, with primary sources,
read dates and per-file SHA-256 digests. So questions 1 and 2 below are **cross-checks** of that
survey rather than fresh reading, and §5 and §6 are restatements of its rejections with the one
thing it could not give: executable confirmation.

Everything #203 lists under "technical gaps" was genuinely absent, and all of it is here:

| gap | status |
|---|---|
| 1. No Feistel-MiMC or Rescue-Prime generator | both land, `src/grobner/research/{feistel_mimc,rescue_prime}.rs` |
| 2. `x^{1/α}` has no representation | written as `y^α = x`, §4.2, deliberately and recorded |
| 3. No reference-vector fixtures | **all ten** reference KATs reproduce, §1 |
| 4. `ChallengeParameters` has no variant for either primitive | **not done** — see §8 |
| 5. A2 has not run | superseded; A2 landed 2026-11-08 |

## 1. Faithfulness, which is the only thing that makes the rest worth reading

The reference implementation is `krypto/zkfriendlyhashzoo` at commit
`b9c09d5a6302725a65ff59e4219d1beb4c524154` (MIT), cloned over HTTPS from
<https://extgit.iaik.tugraz.at/krypto/zkfriendlyhashzoo> on **2026-11-09**. The two instance files'
digests reproduce `ef-cryptanalysis.md` §4's exactly, which is an independent confirmation of that
survey's read:

| file | SHA-256 |
|---|---|
| `bounties/src/feistel_mimc/feistel_mimc_instances.rs` | `bb093e58d08a508659c163944fb83e4f47c5112e5c9f44962df07b6ff5eddd38` |
| `bounties/src/rescue_prime/rescue_prime_instances.rs` | `5d8474b90f735a3fa2a2f8311e8a6867d7c4203d07ca8d502807d65f469facc9` |

**The reference ships known-answer tests, and all ten of them reproduce here.** That is a stronger
check than any unit test this crate could write for itself, because each output depends on every
round constant, on the seed, on the S-box placement and on the field: two fields of the same order
with different moduli would not agree, which is the #197 failure made impossible to repeat.

| primitive | instances | input | reproduced |
|---|---|---|---|
| Feistel-MiMC | `r ∈ {22, 25, 30, 35, 40}` | `[0, 1]` | **5 of 5** |
| Rescue-Prime | `EASY1`, `EASY2`, `MEDIUM`, `HARD1`, `HARD2` | `[0, 1, 2…]` | **5 of 5** |

The tests are `research::feistel_mimc::tests::test_the_permutation_matches_the_reference_test_vectors`
and `research::rescue_prime::tests::test_the_permutation_matches_the_reference_test_vectors`.

### 1.1 Feistel-MiMC's constants are derived, so the derivation is what is pinned

The reference does not tabulate them. `FeistelMimcParams::instantiate_rc` seeds a SHAKE128 with the
ASCII string `"FeistelMimc"` followed by the field characteristic, and reads field elements out of
the squeeze stream by rejection sampling eight-byte little-endian words. Reproducing that needed
SHAKE128, which this crate did not have; `src/util/shake128.rs` is a hand-written Keccak-f[1600]
sponge, in the role `src/util/sha256.rs` already plays and for the same stated reason.

**One detail decides every constant and no shape check could catch it.** The reference absorbs
`F::char().as_ref()` one `u64` at a time, and its `Fp64` is an `ff` `PrimeField` whose `FrRepr` is
**two** limbs wide for a 64-bit modulus — `ff` needs a spare bit for Montgomery arithmetic. The seed
is therefore `p` as eight little-endian bytes **followed by eight zero bytes**. Zeebra's
`KnownOrder::characteristic_limbs()` is canonical and reports one limb, so using it directly would
absorb eight bytes, produce a completely different and entirely plausible constant schedule, and
reproduce no test vector. `feistel_mimc::SEED_LIMBS` states the reference's representation width,
and the KATs are what prove it right.

The SHAKE is seeded with the string and the characteristic **alone** — not with the round count — so
the constants of an `r`-round instance are the first `r` of any longer instance's. A reduced-round
rung is the authoritative instance **truncated**, not a different primitive. Asserted by
`test_the_round_constants_are_a_prefix`.

`FeistelMimc::derived_digest` pins the schedule, because `p`, `α` and `r` would be unchanged if the
seed width or the rejection rule moved and every constant would shift:

| `r` | digest |
|---|---|
| 6 | `f45af9dbf35aadf9` |
| 22 | `8d52a882efde458b` |
| 40 | `d1a97b7391e61728` |

### 1.2 Rescue-Prime's constants are tabulated, so they are transcribed

The opposite choice, and it is the reference's rather than this crate's: `rescue_prime_instances.rs`
is a literal table. It is transcribed into `research/rescue-prime/bounty-constants.txt`, which
carries the source file's digest in its header. The shapes cross-check against `ef-cryptanalysis.md`
§4.2's independently — `MDS2` is 2×2, `MDS3` is 3×3, and each round-constant block has `2N` rows of
width `t`: 8×3, 12×2, 14×2, 10×3, 16×2. All five agree, and
`test_the_constant_tables_have_the_published_shapes` asserts it.

### 1.3 The inverse S-box exponent is computed from the field's own order

`α^{-1} mod (p − 1)` for `α = 3` and `p = 2^64 − 59` is **`12297829382473034371`**. Anemoi's, at
`p = 2^64 − 353`, is `12297829382473034175` — two numbers a glance cannot tell apart, which is why
`RescuePrime` derives it from `F`'s order rather than carrying a constant, and why
`test_the_two_sbox_exponents_are_mutually_inverse` checks `x^α` and `x^{α^{-1}}` are mutually
inverse **by evaluation on actual field elements** over forty inputs rather than by comparing
against a transcribed value.

## 2. The authoritative parameters, and the Feistel-MiMC revision

Field for all of it: `p = 18446744073709551557 = 2^64 − 59`, which is `fields::Zp18446744073709551557`
and needed no work. Objective for all of it: **CICO(1) on the trailing word**,
`Perm(X…, 0) = (Y…, 0)`, as the reference's own verifier writes it — `output[output.len() - 1] == 0`
and nothing else. `Objective::CicoExactTrailing` is that objective's tag in this crate. Note this is
**not** the convention `AnemoiCico` uses, which constrains the *leading* word; the two are different
problems and both modules say so.

### 2.1 Feistel-MiMC: both ladders, and which is authoritative

`bounties21` says only "The initial parameters were broken and were replaced". Both sets are
established in `ef-cryptanalysis.md` §4.4 from two independent directions, and both are carried in
code as `feistel_mimc::BOUNTY_ROUNDS` and `feistel_mimc::WITHDRAWN_ROUNDS`.

**Authoritative (replacement), from `feistel_mimc_instances.rs`, `α = 3`:**

| `r` | stated level | designers' estimate | bounty | published real cost |
|---:|---:|---|---|---|
| 22 | 18 | `2^36` | $2 000 | est. `2^47` |
| 25 | 20 | `2^40` | $4 000 | est. `2^52` |
| 30 | 24 | `2^48` | $6 000 | est. `2^60` |
| 35 | 28 | `2^56` | $12 000 | — |
| 40 | 32 | `2^64` | $26 000 | — |

**Withdrawn, and the two that fell:**

| `r` | stated level | designers' estimate | bounty | published real cost |
|---:|---:|---|---|---|
| **14** | 12 | `2^24` | $6 000 | **`2^33`, 3 minutes** |
| **18** | 15 | `2^32` | $12 000 | **`2^40`, 6 hours** |

The whole original ladder was `r ∈ {6, 10, 14, 18, 22}`, replaced by commit
`e69d08f612f8534ef60651cb01fc326b67230ec1`, 2021-12-20, "update the feistel-mimc instances".
**What broke the first set is that `r = 14` and `r = 18` were solved by equation solving at `2^33`
and `2^40`, three minutes and six hours** — against designer estimates of `2^24` and `2^32`, so the
attacks cost *more* than estimated and the instances were still too easy at the advertised security
levels of 12 and 15 bits. The ladder then shifted up wholesale and **the old hardest rung, `r = 22`,
became the new easiest.** `test_both_ladders_are_recorded` asserts that overlap, because it is the
one fact that makes "r = 22" ambiguous without a ladder named alongside it.

One inconsistency, carried from the survey: `bounties21` states "Parameters are fixed on November
23d 2021" and the replacement commit is dated 2021-12-20, four weeks later.

`hm2021` adds the designers' own expectation for this family: full 64-bit security needs **81
rounds** (`64 · log_3 4`), and "we are not aware of anything better than equation solving which
costs about `3^r` for `r` rounds". The attack of record on Feistel-MiMC *is* an algebraic one.

### 2.2 Rescue-Prime: `m` is not always 3

#203 and #71 both describe the Rescue-Prime bounty as `m = 3`. **Three of the five instances are
`m = 2`**, and `test_three_of_the_five_instances_are_width_two` pins it:

| instance | `t` (= `m`) | `α` | `N` | stated level | designers' estimate | bounty | published real cost |
|---|---:|---:|---:|---:|---|---|---|
| `EASY1` | **3** | 3 | 4 | 25 | `2^39` | $2 000 | **`2^43`, 4 days** |
| `EASY2` | **2** | 3 | 6 | 25 | `2^41` | $4 000 | est. `2^53` |
| `MEDIUM` | **2** | 3 | 7 | 29 | `2^49` | $6 000 | est. `2^62` |
| `HARD1` | **3** | 3 | 5 | 30 | `2^51` | $12 000 | est. `2^57` |
| `HARD2` | **2** | 3 | 8 | 33 | `2^56` | $26 000 | est. `2^72` |

Parameters from the reference; the rest from `hm2021`, read 2026-11-08 (`ef-cryptanalysis.md` §0).
**Only the `2^43`/4-day figure is an executed attack**; every other cost column is the designers'
own complexity formula from the Rescue-Prime specification §2.5 with `α, N, m` (or `α, 2N/3, m` for
the "level") substituted in. A formula is not a measurement and the two must not be tabulated
together without saying which is which.

## 3. Feistel-MiMC: two formulations, and they differ in kind

#203's research question 3, and the issue is right that the formulation choice is the whole
difficulty. `src/grobner/research/feistel_mimc_cico.rs` emits both.

Write the state entering round `j` as `(A_j, B_j)` with `(A_0, B_0) = (X, 0)`. A round is
`(x, y) ↦ (y + (x + c_j)^α, x)` — the Feistel swap is *after* the S-box — except the last, which
omits the swap. So `B_j = A_{j−1}`, the whole state is determined by the `A` sequence, and the
recurrence is

> `A_{j+1} = A_{j−1} + (A_j + c_j)^α`, with `A_{−1} = 0`.

### 3.1 `PerRound`: `r` cubics in `r` variables

One variable per round, `x_j = A_j`. Generators `x_{j+1} − x_{j−1} − (x_j + c_j)^α` for
`j = 0 … r−2`, and the objective `x_{r−2} + (x_{r−1} + c_{r−1})^α − target`. Every generator has
degree exactly `α`; nothing compounds.

`N − E = 0`. In `docs/research/structure-experiments.md` §1's bookkeeping that is `t − 2k = 2 − 2`,
so the system is **square and zero-dimensional with no slice** — which is the structural difference
from the `t = 3` Rescue-Prime instances in §4.

### 3.2 `Univariate`: one generator of degree `α^r`

The `r − 1` intermediate variables eliminated by substitution rather than by a Gröbner computation.
Exact, and it costs degree exponentially: `deg A_j = α^j`, so the objective polynomial has degree
`α^r`. That is 729 at `r = 6` and about `3.1 × 10^10` at the easiest *authoritative* rung `r = 22` —
so the univariate route is a real alternative at small `r` and not merely slow at the specified
instances, but impossible.

**This is what the absent MDS layer buys, stated precisely.** Poseidon has no such route: a dense
MDS layer couples every word of the state each round, so eliminating the intermediate variables
does not leave a polynomial in one unknown. `docs/research/poseidon.md` §6 names that coupling as
"the structural obstacle, not the variable count"; Feistel-MiMC is what the same problem looks like
with the obstacle removed, and the removal converts a Gröbner problem into a root-finding one.
`#68`'s and `#84`'s territory, not F4's.

### 3.3 They have the same solution set, and that is asserted before any cost is compared

#203's acceptance criterion, and `test_the_two_formulations_have_the_same_solution_set` is it. The
chain:

- `roots` is **exhaustive** over the base field, so the univariate's roots are the complete solution
  set and not a witness;
- every root is checked **through the permutation**, not through either polynomial system —
  `is_solution` runs `Perm(x, 0)` and reads the trailing word, which is the reference's own
  verifier;
- the per-round system is checked to vanish at each root's trace, so the two models agree on the
  whole set rather than at one point;
- at `r = 1` the answer is in closed form — `(X + c_0)^α = 0` forces `X = −c_0` — which is the one
  rung checkable without solving anything, and it comes out.

A second test, `test_both_models_reproduce_the_permutation_at_any_input`, makes the sharper
statement that the models are faithful at *every* input and not only where they vanish. It has to
separate two kinds of generator, and the distinction is worth stating because it is easy to get
backwards: the per-round system's first `r − 1` generators are **trace relations** and hold at any
input, while the last is the **objective** and holds only at a solution. So a vanishing check at an
arbitrary input *must* fail on exactly the last generator; a failure at an earlier index is the only
evidence of an unfaithful model. Both `verify_against_*_trace` functions document this.

### 3.4 An empty solution set is a fact about the rung

At the **stated** objective — target zero, which is what the bounty asks — a reduced round count
need not have any solution over `F_p`: the degree-`α^r` univariate does not have to split. `r = 2`
is such a rung. That is a property of the instance and not a failure of anything, and it is the same
discipline `docs/research/poseidon.md` §4 records for `EmptySlice` under M21-E. The measured ladder
therefore uses a **planted** target — the trailing word the permutation actually produces on a
chosen input — so a solution provably exists and "found nothing" is unambiguously a solver outcome.
`FeistelMimcCico::planted` records what it was planted from, because a planted instance's target
*is* a function of its plant.

## 4. Rescue-Prime: `y^α = x`, deliberately

### 4.1 Why `x^{1/α}` cannot be written down

A Rescue round is `x^α`, affine, `x^{1/α}`, affine. `1/α` means `α^{-1} mod (p − 1)`, which is
`12297829382473034371` here (§1.3), so `x ↦ x^{α^{-1}}` as a polynomial has degree about `2^64/3`.
#203's technical gap 2.

### 4.2 The relation, written backwards, and what that changes

`y = x^{1/α}` and `y^α = x` have the same solutions, because `x ↦ x^α` is a bijection when
`gcd(α, p − 1) = 1` — which `RescuePrime::new` checks rather than assumes. The second form is
degree `α`. So the model carries a variable for every **inverse** S-box output and states its
defining relation in the cheap direction.

Recorded as a deliberate choice because **it changes the generator set**: the ideal is generated by
`N·t` cubics and one linear form, not by anything of degree `α^{-1}`.
`test_the_inverse_sbox_relation_holds_on_the_trace` checks the substitution against the primitive —
trace index `4r + 3` cubed must equal index `4r + 2`, at every round of `HARD1`.

### 4.3 The variables are the inverse S-box outputs, not the round inputs

A second choice worth recording. Putting variables on the round *inputs* `u_r` requires `M^{-1}` to
read `u_{r+1} = M·z_r + c_{2r+1}` backwards. Putting them on the inverse S-box outputs `z_r` does
not: `u_r` is then an **affine** expression in `z_{r−1}`, the relation
`z_r^α = M·u_r^α + c_{2r}` is degree `α` in each, and no matrix inversion enters the construction.
One fewer transcribed quantity is one fewer thing that can be wrong — the §1 principle applied to
the model rather than to the parameters.

### 4.4 `t = 3` is underdetermined by one; `t = 2` is square

`N − E = t − 2k = t − 2`, with `k = 1`:

| instances | `t` | `N − E` | zero-dimensional without a slice? |
|---|---:|---:|---|
| `EASY2`, `MEDIUM`, `HARD2` | 2 | **0** | yes |
| `EASY1`, `HARD1` | 3 | **1** | **no** |

`test_the_excess_variable_count_is_t_minus_two` asserts it at every round count of every instance.
This matters for #203's acceptance criterion that any comparison against Poseidon's frontier be at
**matched algebraic dimension**: `docs/research/degree-profiles.md` §4 records that the nine-variable
`t = 3` and `t = 2` Poseidon instances do not have the same dimension, and the same trap is live
here. The two `t = 3` Rescue-Prime instances have a one-dimensional solution variety and need a
slice or a planted coordinate before any zero-dimensional solver will accept them — so they are not
comparable to a square Feistel-MiMC rung at matched variable count without that correction, and no
such comparison is made below.

## 5. MiMCSponge is **not** a polynomial-solving target

#203's research question 4, stated here rather than left to be rediscovered. The MiMC Hash
Challenge (<https://crypto.ethereum.org/bounties/mimc-hash-challenge>) is a **collision** objective
on a MiMC-Feistel sponge over BN254 and BLS12-381 `Fr`, 220 rounds, exponent **5**, `r = c = 1`, at
128-bit target security.

In the objective taxonomy of #67 as `ef-cryptanalysis.md` §2 tabulates it, a collision is
**birthday-bounded** — generically `O(p^{1/2})` — and a Gröbner basis has nothing to contribute to
it. It is not CICO, not a preimage through a prescribed mode, and not a root-finding condition. The
*primitive* is a good target and the *advertised challenge* is not, and these are different
statements.

Its value here is as a specification and an arithmetic exercise: 220 rounds of `x^5` over a 254-bit
field exercises `PrimeFieldElement256` and the wide `pow_mod_limbs` path. Both primes already match
`fields::Bn254Fr` and `fields::Bls12_381Fr` exactly. **Rejected as a solving target; not reopened.**
The page's claimability is `unverified` per `prize-ledger.md` §1 — a $20 000 reward with no window,
no deadline and no status — and the rejection does not depend on that.

## 6. Reinforced Concrete is not expressible at any useful degree

#203's research question 5, and `ef-cryptanalysis.md` §4.5 settles it. Its S-box decomposes a field
element into digits in mixed radices and applies `f(x) = (x == 0) ? 0 : x^{-1} mod v` per digit — a
lookup over a **different modulus** `v`. Digit decomposition is not a low-degree polynomial map over
`F_p`, and the per-digit inversion is modulo `v`, not `p`. The programme agrees from the other side:
`bounties21` says "The best attack we have found for these variants is exhaustive search" and that
Gröbner challenges "might be declared additionally" — they never were, and no real attack cost is
published for any of the three instances. **Rejected, and not for want of effort.**

No generator is written. Expect to reject was the right expectation.

## 7. The measured ladder

`cargo run --release --example feistel_mimc_cico`. Protocol: `tools/benchlock.sh`, per-worktree
`CARGO_TARGET_DIR`, `RUSTC_WRAPPER=""`, `RUSTFLAGS` unset, `taskset`-pinned, load gated inside the
lock per run and re-checked at the end.

MEASUREMENT_SECTION_PENDING

## 8. What is not done, and where it is tracked

- **`ChallengeParameters` has no variant for either family**, so neither primitive has registry
  rows and neither appears on the scoreboard. #203 lists registry entries as a deliverable; this is
  the one that did not land. The variants are mechanical — `FeistelMimcCico` and `RescuePrimeCico`
  both expose the identity-bearing fields a `canonical_lines` arm needs, including the model tag and
  the planted target — but `challenge.rs` is 3 500 lines with digest-frozen tests, and it is a
  contention magnet. Tracked as a follow-up.
- **No Rescue-Prime measurement.** The `t = 2` instances are square and measurable; the `t = 3`
  ones need a slice first (§4.4). The generator, its faithfulness checks and the dimension
  bookkeeping all land; the ladder does not.
- **The withdrawn Feistel-MiMC ladder is not measured at `r = 14` or `r = 18`**, the two rungs with
  published executed attacks. Those are the comparisons worth having — `2^33`/3 min and `2^40`/6 hr,
  with no hardware stated — and `r = 14` is already far past where the per-round ladder stops.

## 9. What nothing here says

- **No result above is a result about a specified instance.** The easiest authoritative Feistel-MiMC
  rung is `r = 22` and the easiest withdrawn one is `r = 6`; the easiest Rescue-Prime instance is
  `EASY1` at `N = 4`.
- A planted target is a **surrogate**. The bounty objective is the target *zero*, and the two are
  not interchangeable: §3.4.
- The designers' complexity estimates in §2 are not measurements, with the two exceptions marked in
  bold. `ef-cryptanalysis.md` §11 records which figures carry no hardware statement and are
  therefore a difficulty ladder rather than a comparand.
