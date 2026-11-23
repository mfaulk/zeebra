# Hilbert-count acceptance of randomized zero tests: soundness (#1038)

**Status:** proof note and harness complete, 2026-11-22. **Parent:** #1028. **Feeds:** #955
(research question 1). **Measured at:** branch base `0cabbad2` plus this note's harness
([`tests/hilbert_count_acceptance.rs`](../../tests/hilbert_count_acceptance.rs)). The §8 cost ratios
come from one untimed-protocol run of its ignored study `applicability_on_the_benchmark_rows`,
built with `--profile ci-release` on a macOS/arm64 laptop. That is not the bench host. Each ratio
is the check's cost over the same run's exact solve, taken in the same process. They are
order-of-magnitude estimates, not a timing campaign; the issue asks for none.

## Outcome

1. **Homogeneous input: sound, and self-certifying (Theorem 1).** Run degree by degree and keep
   only elements of `I`. If `C(e) = S(e)` holds at every degree `e ≤ d`, the computation is exactly
   right through `d`. Here `C(e)` counts the degree-`e` monomials outside the computed
   leading-monomial ideal, and `S = Π(1 − t^{d_i})/(1 − t)^n`. This needs **no a priori regularity**.
   `H_I` is lexicographically at least `S` for *every* homogeneous ideal (Lemma 2), so a run whose
   counts meet `S` has proved regularity through `d` itself. This holds for any field, any
   monomial order, and conventional or signature engines. Pairs skipped by a selection strategy
   do not matter, because the statement is about the computed set, not about how it was produced.
2. **Affine input: unsound as usually stated, sound under one observable condition (Theorem 3).**
   Degree falls make `C(e) < S_top(e)` possible, so the one-sided error is lost. §4.1 gives a basis
   built from ideal elements that matches `S_top` in every degree and is not a Gröbner basis. The
   rule is sound again when **no kept row fell in degree** during the run. For square systems,
   reaching `C = 0` then also certifies the final basis.
3. **Applicability on the named rows (§8).** The certificate accepts the exact run on **MQ11 /
   Goldilocks** (dense) and on **Katsura-11**. It refuses **Eco-12** and **MQ10 / GF(2³¹−1)**, whose
   top forms are not regular. MQ10 is the sparse ladder generator's row, and one of its equations is
   linear. A refusal is never a wrong answer. #714 measured grobx's 5.26× on MQ10 / GF(2³¹−1), so it is
   not on a row this certificate covers. The certified cost is 1.2–2.2% of the exact run, under the
   hypothesis's 5%.
4. **Signature route (§5).** The count certifies the signature engine's *unlabelled output*. It
   does not certify the syzygy signatures that randomized zeros insert, which agrees with #714.
   It does not need to, because the output contract is the reduced basis. A false syzygy is caught
   at the first degree it costs a pivot. What it costs is recovery: the degree where it was
   planted is not known, so recovery is a restart, or a log of the pairs each randomized syzygy
   rejected.
5. **Final certificate (§6).** `HS(⟨LM(G)⟩) = Π(1 − t^{d_i})/(1 − t)^n` as rational functions, or
   a count of zero at the degree of regularity, certifies ideal equality and the Gröbner property
   together for any `G ⊆ I`. It needs no reductions. On the rows above it costs one Hilbert series
   per degree.
6. **Decision (§9).** The hypothesis is **confirmed on the conventional route for homogeneous
   input and for no-fall affine input**. On the signature route it is **confirmed for soundness
   and refuted for cheap recovery**. The estimated net gain on the predeclared regular family
   (dense square MQ over wide primes) is about 18% against grobx's realized fraction of the
   zero-row ceiling. That clears the 15% bar only narrowly, and only on that family. §9 gives the
   bounded prototype proposal, which a deterministic variant (Design D) makes cheaper to test.

## 1. Setting and notation

`R = F[x_1, …, x_n]` over a field `F`, `I = (f_1, …, f_m)`, and `>` a monomial order (degree
compatible whenever input is affine). A **degree-by-degree** computation maintains a finite set
`G` and grows it in degree order. `L(G) = ⟨LM(g) : g ∈ G⟩` is its leading-monomial ideal, and

```text
C_G(e) = #{monomials of degree e not in L(G)},     H_I(e) = dim_F (R/I)_e,     S(t) = Π(1 − t^{d_i}) / (1 − t)^n
```

with `d_i = deg f_i`. `S` is untruncated, and its coefficients may go negative when `m > n`.
`SemiregularSeries::raw` computes it, and the harness's `regular_series` matches that expansion
(`the_regular_series_matches_the_crate_expansion`).

**The one assumption randomization cannot break.** Every kept element is an exact `F`-linear
combination of products `t · f_i`, so `G ⊆ I`. Declaring a row zero only *omits* an element.
Randomization never adds an element outside `I`. Everything below rests on this, and the harness
shows it is load-bearing: one element from outside `I` forges the count
(`an_element_outside_the_ideal_forges_the_count`).

## 2. The homogeneous case (Q1, Q2)

**Lemma 1 (one-sided error).** Let `I` be homogeneous and `G ⊆ I` be any set. Then
`C_G(e) ≥ H_I(e)` for every `e`. Equality at `e` holds iff `L(G)_e = LT(I)_e`.

*Proof.* `G ⊆ I` gives `L(G) ⊆ LT(I)`. For homogeneous `I` and any order, `|LT(I)_e| = dim I_e`:
Gaussian elimination on `I_e` gives a basis with distinct leading monomials. So
`dim R_e − |L(G)_e| ≥ dim R_e − dim I_e`. Two finite monomial sets, one inside the other, are equal
iff they have the same size. ∎

**Lemma 2 (lexicographic lower bound).** For homogeneous `f_1, …, f_m` of degrees `d_i`, over any
field, either `H_I = S` in every degree, or `H_I(e₀) > S(e₀)` at the least degree `e₀` where they
differ.

*Proof.* Induct on `m`. For `m = 0`, `H_R = 1/(1 − t)^n = S`. For the step, let `J = (f_1, …,
f_{m−1})`, `A = R/J`, `f = f_m` of degree `d`, and `B = A/fA = R/I`. The exact sequence

```text
0 → (0 :_A f)(−d) → A(−d) --·f--> A → B → 0
```

gives `H_B(k) = H_A(k) − H_A(k − d) + δ(k)` with `δ(k) = dim (0 :_A f)_{k−d} ≥ 0`. Also
`S_I(k) = S_J(k) − S_J(k − d)`. Subtracting,

```text
H_B(k) − S_I(k) = [H_A(k) − S_J(k)] − [H_A(k − d) − S_J(k − d)] + δ(k).
```

Let `a` be the least degree with `H_A ≠ S_J`, or `∞`. By induction `H_A(a) > S_J(a)`. For `k < a`
both brackets vanish, because `k − d < a`, so the difference is `δ(k) ≥ 0`. At `k = a`, the first
bracket is positive, the second vanishes, and `δ ≥ 0`. So the first nonzero difference, if any,
is positive. If `a = ∞`, the difference is `δ(k) ≥ 0` everywhere. ∎

Lemma 2 needs neither `m ≤ n` nor genericity. Fröberg's inequality is the coefficientwise statement
against the *truncated* series. That is a stronger claim than the one needed here, and this note does
not use it. Lemma 2 is all the acceptance test needs, and it is proved above in full.

**Theorem 1 (self-certifying count).** Let `I` be homogeneous and `G ⊆ I`. Suppose that for every
`e ≤ d`, either `C_G(e) = S(e)`, or `C_G(e') = 0` for some `e' ≤ e`. Then `L(G)_e = LT(I)_e` for
all `e ≤ d`, and `H_I(e) = S(e)` wherever the first alternative was used.

*Proof.* Once `C_G(e') = 0`, Lemma 1 gives `H_I(e') = 0`, and every higher degree of `L(G)` and
`LT(I)` is all of `R_e`. Below that, suppose some `e ≤ d` has `H_I(e) ≠ S(e)`, and take the
least. Lemma 2 gives `H_I(e) > S(e) = C_G(e) ≥ H_I(e)`, which is a contradiction. So `H_I = S = C_G`
through `d`, and Lemma 1 gives equality of the monomial sets. ∎

**Consequences, answering Q1 and Q2 directly.**

- *When is `H_I` known exactly?* It never needs to be known in advance. `S` is a lexicographic
  lower bound for every input, and a run that meets it has established regularity (through `d`)
  as a by-product. "Dense random MQ" is never assumed. An input that is not regular fails the
  count at its first non-regular degree, *including on an exact run* (Lemma 2). The rule is
  therefore sound on every input and complete only on regular (or semiregular) ones.
- *Overdetermined (`m > n`) and semiregular input* is covered as well. For `e` below the degree
  of regularity, `S(e) > 0`, and a semiregular sequence has `H_I(e) = S(e)`. At `D_reg`,
  `C(D_reg) = 0` certifies itself.
- *Is a matching count a sound certificate of no missed pivot?* Yes, by Lemma 1: a missed pivot
  raises `C_G`. The statement concerns the set `G` at the moment it is read. Truncation, sub-batch
  splitting and strategies that defer or skip pairs are irrelevant to its soundness. They affect
  only *when* the count can first match.
- *All degree-`e` work can stop once the count matches.* With `L(G)_e = LT(I)_e` and `G ⊆ I`, every
  element of `I_e` top-reduces to zero modulo `G` without leaving degree `e`. Every remaining
  degree-`e` pair is therefore a certified zero, randomized or not (Design D, §9).
- *Termination on the conventional route.* Gebauer–Möller pruning reads only leading monomials. A
  run with every processed degree certified, and an empty queue, satisfies Buchberger's criterion:
  every pair it generated reduces to zero (certified) or was pruned by an LM-only criterion. So the
  output is a Gröbner basis even when `S` never reaches zero (positive-dimensional input).

## 3. Failure handling (Q5)

A randomized degree `e` is accepted when the rule passes. Otherwise it is redone:

1. **Retry once, deterministically.** Discard degree `e`'s new elements, along with the pairs they
   created, all of which have degree `> e` in the homogeneous case. Restore that degree's pair
   list and reduce it exactly. Because every lower degree is certified, the exact redo is exactly
   right at `e`.
2. **If the exact count now equals `S(e)`**, the miss was randomization's. Continue with
   randomization at `e + 1`.
3. **If it still differs**, `H_I(e) = C(e) > S(e)` by Lemma 2, so the input is not regular at `e`,
   and no series is known from here on. Run deterministically for the rest of the computation.
   Exception: a later count of zero certifies itself.

**Cost.** One wasted randomized attempt per failing degree, at most once each, plus at most one
permanent switch. A fresh-seed randomized retry is legitimate too, because the count is checked
again, but over small fields it can fail repeatedly. The deterministic redo bounds the worst case
at about twice the degree's deterministic cost. The rollback state is the basis length and the
degree's pair list at the start of the degree.

`a_mismatch_is_retried_at_its_own_degree_and_then_certifies` runs this procedure with one
combination per degree over GF(2), GF(3) and GF(31). After a retry, every run certifies as far as
the exact run does.

## 4. The affine case (Q3)

The rule above is stated for homogeneous `I`. Zeebra's benchmark inputs are affine.

### 4.1 The obstruction

For a degree-compatible order, `LT(I) = LT(I_top)`, where `I_top` is the ideal of top forms of
*all* elements of `I`. `I_top` contains `T = (top(f_1), …, top(f_m))`, often strictly: degree falls
are exactly the elements whose top forms lie outside `T`. So `H_{LT(I)} ≤ H_T`, and this is the
wrong direction for the sandwich. Two things break.

- **The count can fall below the series.** `I = (x² + y, x²)` has `LT(I) = (x², y)`, so the counts
  are `1, 1, 0` against `S_top = 1, 2, 1, 0`. At the close of degree 1, before the degree-2 pair
  yields the fall `y`, `C(1) = 2 = S(1)`, and the rule would certify a degree that is wrong
  (`affine_degree_falls_break_the_one_sided_error`).
- **A full match certifies nothing.** `G = {x², xy, y³} ⊆ I` counts `1, 2, 1, 0 = S_top` in every
  degree and reaches zero, yet `y ∈ I` has no leading divisor in `G`
  (`affine_count_without_the_no_fall_witness_certifies_a_wrong_basis`). A miss compensated by a
  fall produces this. The exact run of the corpus's sparse MQ, `n = 5`, seed 4, is the real
  version: it falls, *and* its counts match `S_top` at every degree close. Its top forms are not
  regular (§8).

### 4.2 Theorem 3: sound under the no-fall witness

**Theorem 3.** Let `>` be degree compatible, and run degree by degree on affine `f_1, …, f_m`. Each
batch of degree `e` reduces rows `t · g` of degree `e`. Suppose:

- (a) no kept row has degree below its batch's degree ("no fall"); and
- (b) the counts of `L(G)` satisfy Theorem 1's hypothesis against `S_top = Π(1 − t^{d_i})/(1 − t)^n`
  through `d`.

Then `L(G)_e = LT(T)_e` for `e ≤ d`. If moreover `m = n` and `C(e) = 0` is reached, `G` is a
Gröbner basis of `I`, and `T` was a regular sequence.

*Proof.* (a) implies `top(g) ∈ T` for every kept `g`, by induction over the run. A kept row is a
combination of degree-`e` rows `t · g'` whose degree-`e` part does not cancel, so its top form is
the same combination of `t · top(g')`. Also `LM(g) = LM(top(g))`. So `top(G) ⊆ T` is a homogeneous
computation in `T` with the same leading monomials, and Theorem 1 applies to it. For the square
case, `C = 0` at some degree makes `R/T` Artinian. `n` homogeneous forms in `n` variables with an
Artinian quotient form a regular sequence (`R` is Cohen–Macaulay). Regular top forms admit no
degree fall in `I`: a representation `g = Σ a_i f_i` of excess degree cancels in its top degree,
which gives a syzygy of `T`. That syzygy is Koszul, because `T` is regular, so the representation
can be lowered (the standard argument; Lazard). Hence `I_top = T`, `LT(I) = LT(T) = L(G)`, and
`G ⊆ I` with `L(G) = LT(I)` is a Gröbner basis. ∎

Witness (a) is free to observe, since a kept row's degree is known when it is kept. When (a)
fails, the run falls back to deterministic reduction from that batch on. Homogenizing explicitly
is the other sound route, since it turns the input into Theorem 1's case. It gives up the degree
falls the affine engine exploits, and for square systems with regular tops there are none.

`the_affine_square_certificate_accepts_katsura_and_refuses_eco_and_cyclic` checks Theorem 3's
verdict against an independent regularity test of `T` (an exact basis of the top forms). That test
reads Zeebra's real F4 run through a `BatchObserver` and evaluates each degree at its close.

### 4.3 A second prime is Monte Carlo

For an integer system, rank over GF(p) is at most rank over **Q**, so `H_{GF(p)} ≥ H_Q` pointwise
(semicontinuity). `H_Q` would be a valid lower bound for the sandwich, but establishing it exactly is
as hard as the basis over **Q**. A second prime `p'` gives `H_{GF(p')} ≥ H_Q`, which bounds the
wrong side. So a second-prime Hilbert series is a *candidate* for `H_{GF(p)}`, not a bound on it,
and it stays Monte Carlo. Lemma 2 makes it unnecessary for regular inputs, and nothing makes it
exact for the rest.

## 5. The signature route (Q4)

`sigf4` uses shifted Schreyer signatures (`src/grobner/sigf4/signature.rs`). A row it finds to be
zero inserts a syzygy signature `s`, and every later pair whose signature `s` divides is rejected
(M33-G1 §8.2: 689,359 / 32,474 / 108,247 rejections on Eco-12 / Katsura-11 / MQ11).

**What the count certifies on this route.** Kept rows are still exact combinations of ideal
elements, so `G ⊆ I`, and Lemmas 1–2 and Theorem 1 apply to the *unlabelled* set. A per-degree
match certifies `L(G)_e = LT(I)_e` however the signatures were bookkept.

**What it does not certify.** A randomized zero in degree `e` claims that a row *signature-reduces*
to zero. That is stronger than lying in the span of the degree's rows. A row whose regular
reduction is nonzero, but whose leading monomial is already in `L(G)`, is singular or redundant:
the count cannot see it, and declaring it zero plants a false syzygy. So a match at `e` does not
justify the syzygies inserted at `e`, which agrees with #714's finding. It does not need to:

- A false syzygy `s` prunes pairs of signature degree `> e` (and equal signatures). If a pruned pair
  was needed, `L(G)` misses a leading monomial at some later degree `e'`, and the count at `e'`
  fails (Lemma 1). Soundness of the output is therefore unaffected.
- **Termination is not LM-only on this route.** Signature pruning, true or false, decides when the
  queue empties. Section 2's Buchberger argument does not apply, so the route's output is certified
  only by §6's final check: the counts must cover *every* degree. That holds when `S` reaches zero
  (square, Artinian) or `HS(L(G)) = S` as rational functions. For positive-dimensional input that
  is not regular, the route has no count certificate at all.
- **Recovery is the cost.** A mismatch at `e'` does not say which degree planted the syzygy that
  caused it. Recovery is a deterministic restart from the first randomized degree, or a log, kept
  per randomized syzygy, of the pairs it rejected, so they can be revived. M33-G1's rejection
  counts give the log's size. Over a 64-bit prime the miss probability per combination is about
  `1/p`, so the expected restart cost is negligible. Over small fields it is not.
- **A combination mixes signatures.** grobx's mechanism reduces `Σ c_i r_i`. On the signature route
  each row may be reduced only by rows of smaller signature, so the combination's reduction is not
  the combination of the rows' reductions. A per-row zero claim therefore does not follow from a
  zero combination. Making it follow needs combinations restricted to rows that share one reducer
  set. That is a design constraint, not an obstruction to soundness.

The conventional route has none of these costs. That is why §9's prototype targets it first.

## 6. Final-output certificate (Q6)

For any `G ⊆ I`, on homogeneous input or under Theorem 3's witness:

```text
HS(L(G)) = Π(1 − t^{d_i}) / (1 − t)^n   as rational functions,   or   the counts meet S up to a degree with C = 0
```

certifies `L(G) = LT(I)`. That is both **the Gröbner property and ideal equality**, because a subset
of `I` whose leading monomials generate `LT(I)` is a Gröbner basis of `I` and generates it. The
check needs no reductions. `HilbertSeries::of_monomial_ideal` computes the left side in closed
form from the final leading monomials. Compare `certify_f4_output`, which repeats the zero
reductions and costs 2–67× the solve (#955).

Where neither condition holds (Eco-12, MQ10/sparse, positive-dimensional non-regular input), no
certificate is cheaper than Buchberger's criterion. The count gives nothing there, and §3's
fallback is the answer.

## 7. The harness (deliverable 2)

[`tests/hilbert_count_acceptance.rs`](../../tests/hilbert_count_acceptance.rs) tests the acceptance
rule independently of any production randomization. It uses a dense, F4-shaped toy engine over
GF(2), GF(3) and GF(31). Degree `e`'s rows are `x_j · b` for the previous degree's basis plus the
degree-`e` generators. One row per leading monomial is a reducer and is always exact, and only
the remaining pair rows go through the policy under test. The engine computes the same Hilbert
function as Zeebra's F4 (`the_toy_engine_computes_the_hilbert_function_zeebra_does`).

| Test | What it establishes |
|---|---|
| `hilbert_function_is_lexicographically_at_least_the_regular_series` | Lemma 2's counterexample search over random, mixed-degree, overdetermined, repeated, multiple, common-factor, monomial and perturbed-square systems; asserts both outcomes occur (> 20 each) |
| `count_acceptance_never_certifies_a_short_random_reduction` | Theorem 1 under 0–13 random combinations per degree, over fields where they collapse; > 100 wrong runs rejected, > 10 shortcut runs certified to the end |
| `count_acceptance_rejects_every_dropped_pivot` | a pivot deliberately dropped at any degree is never certified at or above it |
| `a_mismatch_is_retried_at_its_own_degree_and_then_certifies` | §3's retry: changed pivots across degrees, and certification restored |
| `an_element_outside_the_ideal_forges_the_count` | `G ⊆ I` is load-bearing |
| `affine_degree_falls_break_the_one_sided_error`, `affine_count_without_the_no_fall_witness_certifies_a_wrong_basis` | §4.1 |
| `the_affine_square_certificate_accepts_katsura_and_refuses_eco_and_cyclic` | Theorem 3 on real F4 runs, against an independent regularity test |

The harness was checked against a mutant. Accepting `C(e) ≤ S(e) + 1` fails three tests: the
forged count, the short random reduction and the dropped pivot.

## 8. Applicability and cost on the named rows

From `applicability_on_the_benchmark_rows`, which loads each row as `examples/m29_cost_model.rs`
does. "Fell" and "counts match" are Theorem 3's (a) and (b), read on the exact run through a
`BatchObserver`. "Tops regular" is the independent test. The cost column is the check's cost
(one Hilbert series per closed degree over the leading monomials up to it) divided by the same
process's exact run (one worker, observer attached). The run that §8's ratios come from is
described in the header.

| Row | Degrees | Fell | Counts match | Tops regular | Certifies | Leads | Check ÷ run |
|---|---|---|---|---|---|---|---|
| MQ11 / Goldilocks (wide, dense) | 2 × 11 | no | yes | yes | **yes** | 767 | 1.2% |
| MQ10 / Goldilocks (wide, dense) | 2 × 10 | no | yes | yes | **yes** | 426 | 2.2% |
| Katsura-11 / 2³¹−1 | 2 × 10, 1 | no | yes | yes | **yes** | 537 | 1.6% |
| MQ10 / 2³¹−1 (ladder, sparse) | 2 × 9, **1** | yes | no | no | no | 247 | — |
| MQ10 / 32003 (ladder, sparse) | 2 × 9, **1** | yes | no | no | no | 247 | — |
| Eco-12 / wide64 | 3 × 10, 2, 1 | yes | no | no | no | 743 | — |

The small-seed study `applicability_on_small_square_mq` gives the same answer for the sparse
ladder generator at `n = 5, 6, 7`. Two of 18 seeds have regular top forms, and one of those only because a constant generator
makes the ideal the whole ring. The generator draws
each term's degree uniformly from `{0, 1, 2}` and at most `4n` terms. Its "MQ" rows therefore often
have a linear or even constant equation, and sparse quadratic parts with dependent top forms.
**The issue's MQ10 / GF(2³¹−1), where #714 measured grobx's 5.26×, is one of those.** The dense
wide-corpus rows, which are what M33-G1 called MQ11, are covered.

## 9. Decision and the bounded prototype proposal

**Hypothesis.** "For homogeneous inputs whose regularity is established exactly, per-degree
Hilbert-count acceptance is sound on both the conventional and the signature route, at a checking
cost under 5% of the degree's elimination time."

- *Soundness:* **proved** for the homogeneous conventional and signature routes (Theorem 1, §5).
  Regularity is established by the run itself, not in advance. For affine input it is proved
  under the no-fall witness (Theorem 3).
- *Regularity cheaply established:* **yes**, as a by-product of the count (Lemma 2).
- *Signature route needs more than the count:* **for recovery, yes**, and **for soundness, no** (§5).
- *Check cost:* 1.2–2.2% of the whole exact run on the certified rows. The rows' elimination is
  most of the run, so this is within 5% of elimination on these rows. It was measured on a laptop
  at one worker, so the bench host should confirm it at the deciding freeze.

**Net-gain estimate (predeclared family: dense square MQ over wide primes; MQ11 / Goldilocks as the
row).** These are historical figures from M33-G1 §§2 and 8, the bench host's `sig` arm at one
worker: wall 4,883 ms, zero-row products about 1,806 ms (37%), and grobx's elimination 992 ms
faster than Zeebra's (20% of wall). grobx therefore realizes about 55% of the zero-row ceiling.
Applying that fraction and subtracting the check gives **≈ 18–19%** on MQ11. Katsura-11 gives
≈ 0.55 × 21% − 1.6% ≈ 10%. It is outside the declared family and below the bar. This is ≥ 15% on
the declared family, so the decision criterion says **proceed**. It clears the bar only narrowly,
and it rests on two unmeasured transfers: that Zeebra can match grobx's realized fraction, and that
the conventional route can match the `sig` route's baseline. The prototype's gate exists to test
both.

**Bounded prototype (filed under #955).** Opt-in research option, conventional F4 only:

1. *Applicability predicate.* Homogeneous input, or affine input with every generator of degree
   `≥ 1`, while no kept row has fallen. Degree-compatible order. Evaluated online: the first fall
   or the first deterministic mismatch disables the route (§3).
2. *Per-degree check.* Bigatti's series of the current leading monomials at each degree close,
   compared with `S` (Theorem 1). A count of zero ends the run.
3. *Two designs, measured against each other.*
   - **Design D (deterministic, no randomness).** Split each degree into sub-batches and stop
     the degree once the count matches. The remaining pairs are certified zero (§2). This is
     `HilbertSelection::Deferred` with the deferred pairs *dropped* once the degree is certified,
     instead of promoted back. M29 measured the deferral without the drop. This refines
     `hilbert-driven.md`'s rule rather than breaking it: a prediction alone still may not discard
     work, but a prediction the count has met is a certificate.
   - **Design R (randomized, Las Vegas).** grobx-style random combinations of the degree's pair
     rows, `N_d = dim R_d − S(d) − |L(G_{<d})_d|` of them plus a slack, which is exactly the number
     of new leading monomials degree `d` must yield. Keep the nonzero results, then
     check. §3's single deterministic retry handles a mismatch.
4. *Gate.* ≥ 1.15× complete-task wall on MQ11-like dense square MQ rows (held-out supports and
   sizes per #1005) against the **best** Zeebra configuration for the row, which may be the `sig`
   route. There must be no regression on Eco-12, Katsura-11 or MQ10 / sparse, which the predicate
   must refuse at the cost of one count per degree.

Design D is the cheaper first experiment. It needs no rollback and no randomness, and if it
reaches the gate, Design R is unnecessary.

**Implementation (#1080).** Design D is `HilbertSelection::CertifiedZeros { slack }`
(`src/grobner/f4/count_route.rs`), opt-in and off by default. Two choices go beyond the text above.
On affine input a certified degree's pairs are deferred rather than discarded, and are discarded
only when the count reaches zero. Theorem 3 makes the output final only at that point, and the
deferred pairs are promoted back if the route turns off first. For the same reason, affine input
must also be square, since Theorem 3 concludes only for `m = n`. The gate measurement is the bench
host's and has not been taken.

## 10. Transfer limits

- Lemma 2 and Theorems 1 and 3 are proved here. The Lazard step in Theorem 3, that regular top
  forms admit no degree fall, and the Cohen–Macaulay characterization of regular sequences are
  standard and were not re-derived. Fröberg's coefficientwise inequality is deliberately **not**
  used.
- The harness's engine is a model of F4's batch structure, not F4. Real F4 runs enter only through
  `the_toy_engine_computes_the_hilbert_function_zeebra_does` and the observer-based affine tests.
  No production code was changed.
- §8's costs are one laptop run at one worker. The net-gain estimate combines that run with
  historical bench-host figures from a different session and is labelled as an estimate. Per the
  shared measurement rules, it must not be multiplied into a claim.
