# A `k = 3` family, and a hybrid: the arithmetic, and why both are dead

M25-D deliverable 2, for [#287](https://github.com/mfaulk/zeebra/issues/287). The issue frames the
two directions as "the only way left out of the `2^31` trade" and insists on a derivation before an
implementation. This is the derivation. **Both directions close, and the mechanisms that close them
are different from each other.**

The verdict is in §6. It is a **negative result**, which #287's acceptance criteria name as a
legitimate outcome: "If the answer is 'invariant, the direction is dead', that closes #67's
univariate branch and is worth stating as plainly as a success would be."

## 0. The criterion, stated before the numbers

A direction is a **go** only if its total work — families × per-family cost — is below the better of
the two known ends, by enough to matter. The two ends, from M24:

| route | `k` | families | per-family | total |
|---|---|---:|---|---|
| univariate | 1 | ≈`2^31` | **15.2 s** (M24, corrected) | ≈`3.3 × 10^10` core-s |
| bivariate + resultant | 2 | `O(1)` | `≈16·3^{5·rounds}` field ops | construction-bound past six rounds |

Each number below is labelled **measured**, **derived** (exact arithmetic on measured inputs), or
**extrapolated**. Where an assumption is load-bearing it is named, and §5 states how sensitive the
verdict is to it.

## 1. What M24 pinned, and what it left free

Three results from M24-A, all **measured** over 17 838 families
(`docs/research/graeffe-root-finding.md` §9.6), restated because the derivation stands on them:

1. **The family count is `p / E[roots per family]` and contains neither `R_F` nor `R_P`.** `δ` spans
   **6 561×** across the registered ladder and the mean root count never leaves **0.9997**. The root
   distribution tracks Poisson(1) — no-root share 0.3503 against `1/e = 0.3679`. So round reduction
   cannot change the family count, and `E[roots] = 1` is not an assumption but an observation on a
   polynomial that behaves like a random one of its degree.
2. **The two output constraints are not coupled.** `χ²` on the second constraint's residual is
   inside ±3σ on **every** row. The parametrisation does not correlate them.
3. **The per-family cost is 15.2 s**, decomposing (M24 §9.2, with §5.4's correction) as roughly
   **12 s** to build the degree-`3^13` univariate by evaluation at `2^21` points (*estimated* from
   measured permutation throughput), **0.09 s** to interpolate (*measured*, post-#161), and
   **3.11 s** of Graeffe root finding (*measured*). Peak memory a few tens of MB.

The `1/p` filter rate is **not measurable on this hardware**: 0 hits in 17 901 roots bounds it only
by `3/n ≈ 1.7 × 10^{-4}`. Nothing below estimates it; where it appears it is carried as the model
value `1/p` with that caveat attached.

What M24 left free is exactly what #287 asks: the family's **dimension** `k`, and whether partial
information about the second constraint can be traded for family count.

## 2. The general trade, in one equation

Let the family have `k` free parameters and let there be `c = 2` output constraints, each of degree
`D = d^R` in each parameter. Over `F̄_p` the solution set in `A^k` has dimension `k − c`, so by the
Lang–Weil heuristic the expected number of `F_p`-points of one family is

```
E[solutions per family]  ≈  p^{k−c}  =  p^{k−2}
```

and therefore

```
families needed  ≈  max(1, p^{2−k}).
```

This reproduces M24's two measured ends and is the reason to trust it as a model:

- `k = 1`: `p^{1}` families. **`p = 2.13 × 10^9 ≈ 2^31`** — M24's measured-and-confirmed count.
- `k = 2`: `p^{0} = 1` family. `docs/research/resultant-elimination.md` §2 found **three** base-field
  witnesses on a single two-round slice, which is that `O(1)` observed.
- `k = 3`: `p^{1} ≈ 2^31` solutions **per family**.

Read naively, `k = 3` looks spectacular: one family, two billion solutions in it. §3 is why that is
an illusion, and the reason is not probabilistic.

## 3. `k = 3`: there is no univariate equation to find

### 3.1 The elimination ideal is zero

Every route Zeebra has — F4 then FGLM, the resultant, the Graeffe descent — ends by finding the
roots of a **univariate polynomial in the ideal**. For the `k = 3` family that polynomial does not
exist.

Let `f, g ∈ F_p[x, y, z]` be the two constrained output words. The variety `V(f, g)` is a curve:
one-dimensional, and it projects **dominantly** onto the `x`-line (a `k = 3` family is chosen
generically, so no constraint forces `x` into a proper subvariety). Hence

```
⟨f, g⟩ ∩ F_p[x]  =  (0).
```

**There is no nonzero univariate polynomial in the ideal, so there is nothing to root-find.** This is
not a cost statement; it is a statement that the method's final stage has no input. It follows from
`dim V = k − c = 1 > 0` and nothing else, and it holds for every `k > 2`.

Iterated resultants do not rescue it, for the same counting reason. `Res_z(f, g)` is **one** equation
in **two** unknowns — still positive-dimensional. Eliminating two variables needs two independent
bivariate consequences, which needs at least three original equations. CICO-2 supplies two. So:

> **For a `c`-constraint CICO problem, the largest usable family dimension is `k = c`.** Above it the
> elimination ideal in any single variable vanishes.

### 3.2 So `k = 3` is not a route, it is a reparametrisation of `k = 2`

The only way to use a `k = 3` family is to cut it down to `k = 2` by imposing one more equation. Two
candidates, and both land back where they started:

- **Slice with a linear form** `λ(x, y, z) = const`. The result **is** a `k = 2` family. Its cost is
  the `k = 2` cost exactly, and by genericity every slice is equivalent, so the choice buys nothing.
  Families needed: `O(1)`, i.e. the `k = 2` number.
- **Guess one parameter outright**, say `z = z_0`. That gives a `k = 2` family per guess, so families
  needed becomes `p` instead of `O(1)` — **`p` times worse than `k = 2`**, at the same per-family
  cost. This is the `k = 3` "hybrid", and it is strictly dominated.

So the answer to #287's question 3 — "is the product `families × per-family` invariant across `k`?" —
is **no, and it is not even defined for `k > 2`.** The trade is not a continuous dial. Only `k ∈
{1, 2}` are realisable, and the product is **minimised at `k = 2`**, which is the value that matches
the constraint count. The intuition behind that is worth stating because it generalises: `k < c` pays
a *probability* penalty of `p^{c−k}` families; `k > c` pays a *dimension* penalty that destroys the
final stage. Matching `k` to `c` is optimal, and the two known ends are already the two sides of the
optimum.

### 3.3 The one thing `k = 3` could buy, and it is a different issue

The extra dimension is not useless in principle — it is just not useful for *more solutions*. It can
be spent on a **non-generic slice chosen to lower the degree** rather than a generic one. That is
precisely the shape of FreeLunch's Appendix B bypass for Griffin (choose the affine input so the
degree growth is suppressed for three rounds — see `docs/research/griffin-freelunch.md` §1.2, where
the line is recovered from published witnesses) and of 2026/1254 §2.2's `(1,[1])` round-skipping
parametrisation, which `docs/research/elimination-beyond-grobner.md` §5 item 3 already lists as "new
mathematics for the crate".

**That is a different research direction with a different cost model, and it is where the useful part
of #287 should be redirected.** It is not "a `k = 3` family"; it is "a degree-lowering choice of
`k = 2` family". The distinction matters because the first is dead on the counting argument of §3.1
and the second is not touched by it.

## 4. The hybrid: invariant, and the invariance is measured

### 4.1 What "guess `b` bits of the second condition" can mean

In the `k = 1` route each family yields `E[roots] ≈ 1` candidate satisfying constraint 1, and that
candidate satisfies constraint 2 with probability ≈`1/p`. A hybrid proposes to buy family count with
partial information: filter candidates on `b` bits of constraint 2, and pay only `2^b` families per
partial hit instead of `p` families per full hit.

Write `W(b)` for total work. The hybrid helps only if `dW/db < 0`. Two things have to be true for
that, and **both fail, each for a reason M24 already measured.**

### 4.2 Failure 1: the filter is free, so there is nothing to save

The `b`-bit filter is applied to the value of constraint 2 at a candidate. Computing that value
**is** the verification step, and M24 §9.2 measures it at **µs** against a per-family cost of
**15.2 s**. So verification is `~10^{-7}` of the per-family work, **measured**:

```
verification share  ≈  10^{-6} s / 15.2 s  ≈  7 × 10^{-8}
```

A hybrid's entire mechanism is to *skip* full verifications it can rule out cheaply. The maximum
conceivable saving is therefore **one part in `1.4 × 10^7`**, and that is an upper bound, not an
estimate. `W(b) = W(0)` to seven significant figures for every `b`.

This is the invariance #287 asks about, and it is **exact rather than asymptotic**: the family loop's
cost is the family *construction*, not the family *test*, so nothing that reorganises the test can
move the total.

### 4.3 Failure 2: a partial hit carries no information

Even granting a hypothetical where verification were expensive, a hybrid needs partial hits to
*localise* full hits. They do not. M24's second measured result (§1 item 2) is that the two
constraints are **independent** — `χ²` on the second constraint's residual inside ±3σ on every row —
so matching `b` bits of constraint 2 says nothing about the remaining `log₂ p − b` bits, and nothing
about which nearby family to try next. A permutation's input→output-word map is a degree-`3^R`
polynomial with no locality to exploit; the measurement is the empirical confirmation of that.

So the hybrid's expected families to a full hit is `2^b · (p / 2^b) = p`, for every `b`. Written out,
because #287 asks for the arithmetic rather than the conclusion:

| `b` | families per partial hit | partial hits per full hit | families per full hit | total work |
|---:|---:|---:|---:|---|
| 0 | 1 | `p` | `p` | `p · 15.2 s` |
| 8 | `2^8` | `p / 2^8` | `p` | `p · 15.2 s` |
| 16 | `2^16` | `p / 2^16` | `p` | `p · 15.2 s` |
| 31 | `≈p` | `≈1` | `p` | `p · 15.2 s` |

**Derived**, exactly, from §1's measured independence. The column that would have to vary does not.

### 4.4 The floor on per-family cost, which closes the `k = 1` branch independently

Since the family count is pinned at `p` by a measured distributional fact, the only remaining lever
on the `k = 1` route is the per-family cost. It has a hard floor, and the floor is close.

A degree-`3^13` univariate is pinned by no fewer than `3^13 + 1 = 1 594 324` evaluations. M24's
**12 s** build figure is for `2^21 = 2 097 152` evaluations, so the irreducible build is

```
12 s · 1 594 324 / 2 097 152  ≈  9.1 s   (derived from an estimated rate)
```

and the Graeffe root finding on that degree is a **measured 3.11 s** which some algorithm must pay.
So:

| | per-family | total, 1 core | total, 64 cores |
|---|---:|---:|---:|
| measured today | 15.2 s | 1 035 core-years | **16.2 years** |
| floor, Graeffe retained | 12.2 s | 831 core-years | 13.0 years |
| floor, Graeffe free (not achievable) | 9.1 s | 620 core-years | 9.7 years |

**Every conceivable per-family optimisation is worth at most 1.7×, and 1.25× realistically.** Memory
is not a constraint at any point: a few tens of MB per family, so 64 concurrent families fit in a few
GB. The `k = 1` route is not 2–3 orders of magnitude from an attack; it is **9 orders**, and the
per-family axis has 0.2 of an order in it.

## 5. Sensitivity

The verdict rests on five things. Four are measured and one is structural.

| input | kind | if it were wrong |
|---|---|---|
| `E[roots] ≈ 1`, Poisson(1), invariant in rounds | **measured**, 17 838 families | Family count is `p/E[roots]`. Even `E[roots] = 10^3` — a thousandfold departure from a measured Poisson(1) — leaves `2^21` families × 15.2 s = **1.0 core-years**. Still not an attack, and nothing in the corpus suggests any departure at all. |
| constraints independent | **measured**, `χ²` ±3σ every row | §4.3's hybrid becomes arguable. But §4.2 kills it independently, and §4.2 needs only the verification/construction cost ratio. |
| verification ≈ µs vs 15.2 s construction | **measured** | §4.2's bound loosens proportionally. It would have to loosen by `10^7` for the hybrid to matter. |
| per-family 15.2 s | **measured/estimated mix** | §4.4's floor scales with it; the ratio 1.25–1.7× does not. |
| `⟨f,g⟩ ∩ F_p[x] = 0` for `dim V > 0` | **structural**, not measured | This is the `k = 3` argument and it is a theorem, not an estimate. It cannot be wrong; it can only be sidestepped by adding a third constraint, which CICO-2 does not have. |

The one place a complexity-formula argument is doing work is §2's Lang–Weil point count, and it is
load-bearing only for the *optimistic* reading of `k = 3` that §3 then refutes on exact grounds. The
negative verdict does not depend on it. Per the M25 research gate, §2 is labelled a **hypothesis**
and §3.1 is not.

## 6. Verdict

**No-go, and record the negative result. #287's univariate branch of #67 closes.**

- **A `k = 3` family is not an intermediate point between `k = 1` and `k = 2`.** It does not exist as
  a route: with two constraints and three parameters the variety is a curve, the elimination ideal in
  any single variable is `(0)`, and every root-finding stage Zeebra has takes a univariate polynomial
  as input. Cut it down and it *is* the `k = 2` route; guess a parameter instead and it is `p` times
  worse than `k = 2`. The product `families × per-family` is therefore **not invariant across `k` —
  it is minimised at `k = c = 2`**, which is where the resultant route already sits.
- **The hybrid is invariant in `b`, exactly.** The thing it reorganises — candidate verification — is
  a **measured** `~7 × 10^{-8}` of the per-family cost, so its maximum possible saving is one part in
  `1.4 × 10^7`; and the measured independence of the two constraints means a partial hit localises
  nothing. `W(b) = W(0)` for every `b`.
- **The `k = 1` route's remaining axis is worth 1.25×.** The family count is `p` by a measured
  distributional property that round reduction cannot touch, and the per-family cost has a floor at
  12.2 s against a measured 15.2 s. 16.2 years on 64 cores becomes 13.0.

Three numbers decided it: `⟨f,g⟩ ∩ F_p[x] = (0)` for `k = 3` (so the route has no final stage); the
verification-to-construction ratio of `7 × 10^{-8}` (so the hybrid is invariant); and the per-family
floor of 12.2 s against 15.2 s (so the `k = 1` end has 0.2 of an order left in it against a 9-order
gap).

**No prototype was authorised, and none was built.** #287's acceptance criterion — "No implementation
unless the derivation says it wins" — is met by the derivation saying it loses. This is the second
time in M24/M25 that the useful artefact was the cost model rather than the code
(`graeffe-root-finding.md` §10.1).

## 7. What should be done instead

Not as scope creep — as the redirect #287's closure leaves owing.

1. **The degree-lowering parametrisation (§3.3) is the live question, and it is not this one.** The
   extra freedom in a family is worth something only if spent on lowering the elimination degree,
   not on adding solutions. 2026/1254 §2.2's `(1,[1])` round skip and Griffin's Appendix B bypass are
   two instances of it; `elimination-beyond-grobner.md` §5 item 3 already has the first on the books.
   Worth filing as its own issue: *"Degree-lowering CICO parametrisations: price the `(1,[1])` round
   skip against the measured resultant degree `d^{2R_F+R_P}`"*.
2. **The resultant route's per-sample determinant is the axis with an exponent in it.** Since `k = 2`
   is the optimum and its cost is construction-bound, the way to make the `k = 2` route reach further
   is to make its elimination cheaper. `docs/research/structured-sylvester.md` (M25-D deliverable 3)
   derives that, and finds a genuine exponent reduction there — which is the one place in this
   workstream where the arithmetic says *build*.
3. **Do not reopen round reduction.** M24 negative result 1 settles it, and §2's equation shows
   structurally why: the family count has no `R_F` or `R_P` in it.
