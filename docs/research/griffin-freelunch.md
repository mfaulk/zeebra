# Griffin and the Algebraic FreeLunch: what a free Gröbner basis costs Zeebra

**Measured at:** publication bound `63180dcf`…`5ebb5165` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).

M25-D deliverable 1, for [#202](https://github.com/mfaulk/zeebra/issues/202). The question is
architectural rather than competitive: FreeLunch chooses a monomial order in which the natural
Griffin CICO system **already is** a Gröbner basis, so there is no F4 step at all. Zeebra is an
F4-and-FGLM crate. If that claim holds on an instance with published witnesses, then the parts of
Zeebra that matter for this instance class are not the parts Zeebra has invested in.

Everything below is on the instance Griffin `(t, α) = (12, 3)` over
`p = 28407454060060787` (55 bits), reduced to `r ∈ {3, 4, 5, 6}` rounds, with the five published
CICO witnesses of the FreeLunch appendix as the oracle.

## 0. The criterion, stated before the numbers

Three gates, in order. A **no** at any gate stops the work there, and recording the **no** is the
deliverable.

1. **Faithfulness.** The polynomial system must vanish at a published witness. Nothing downstream
   means anything otherwise, and this is the cheapest possible check.
2. **Expressibility.** The FreeLunch order must be writable down as a mathematical object, and
   Zeebra's `MonomialOrder` must either support it or the gap must be costed. #202 states this as
   its question 1 and says a negative answer is an acceptable deliverable.
3. **Worth.** Implementing the method in Zeebra is a **go** only if the stages Zeebra would have to
   add (a weighted order and a normal form against a given basis) are cheaper than the
   *mathematical* ground they buy — a larger solvable `r` on an instance class Zeebra cares about —
   and not merely a faster route to an `r` that is already reachable. Per the M25 research gates,
   mathematical progress and implementation performance are scored separately.

The verdict is in §8. It is **no-go for M25, defer the capability to #306**, and the gate it fails
is gate 3, not gate 1 or 2 — which is the opposite of what #202 expected.

## 1. Gate 1: the system vanishes at the published witnesses, and the bypass line falls out

`tools/check-griffin-reconstruction.py` already reproduced the five published witnesses through the
*permutation* (`docs/research/additional-benchmarks.md` §2). That is not the same as reproducing the
*system*, and M25-D extends the tool to the second thing:

```
tools/check-griffin-reconstruction.py --witness-system
tools/check-griffin-reconstruction.py --build-system 5
```

### 1.1 The modelling equations, checked at all five witnesses — PASS

The FreeLunch modelling introduces one variable `x_i` per round for the `α`-th root taken on branch
0, with `p_i = x_i^α − L_i(z_{i−1})`, and takes `g` to be the first output coordinate. Eq. (4) of
the paper makes `G_i` agree with the round function exactly on the locus `x_i^α = L_i(z_{i−1})`, so
the check is field arithmetic only: run the permutation, record the roots it actually takes, and
confirm every `p_i` and `g` vanish there. **Measured**, five of five:

| rounds | `x_0` | permutation | `[input]_0 = 0` | every `p_i = 0` | `g = 0` |
|---|---|---|---|---|---|
| 5 | 3490692521816093 | ✓ | ✓ | ✓ | ✓ |
| 5 | 20508905520120247 | ✓ | ✓ | ✓ | ✓ |
| 6 | 15940424764849354 | ✓ | ✓ | ✓ | ✓ |
| 6 | 13453267118668680 | ✓ | ✓ | ✓ | ✓ |
| 7 | 471901030567494 | ✓ | ✓ | ✓ | ✓ |

### 1.2 A result the paper does not publish: the Appendix B bypass line, recovered out of sample

Printing the roots exposes something the published data was not advertised as containing. The first
three `α`-th roots are **the same three constants at every witness and every round count**, so they
do not depend on `x_0` at all:

```
x_1 = 0
x_2 = 7898304148958718
x_3 = 17258885674050987
```

That is exactly Appendix B's three-round bypass for `t ≥ 12`: an affine input
`z_0(x_0) = a·x_0 + b` chosen so the `x^{1/α}` input is a known constant for three rounds. The
paper describes how `a` and `b` are determined but **does not publish them**, and the construction
has free choices in it (an arbitrary nonzero `a_1`, a root choice for `c_3(a_0) = 0`), so they are
not recomputable from the text.

They are recoverable from the witnesses. Two points determine an affine line. Parametrising by input
word 1 — i.e. fixing `a_1 = 1, b_1 = 0`, which is a choice of coordinate on the line and not an
assumption — the two `r = 5` witnesses give

```
a = [0, 1, 15574108527865654, 12833345532195127, 4498928985879348, 4105373726431084,
     19825928247982741, 22768475630095724, 26722396606122532, 12957014625648710,
     1575165728387576, 12645338513655545]
b = [0, 0, 3315691270431207, 25091762789629580, 10771750388583441, 26319868554931350,
     1195670321669144, 25057749274895288, 12201570747891186, 15179492140873806,
     10205561023577940, 20355927499979202]
```

**The confirmation is out of sample, which is what makes this a recovery rather than a consistency
check.** The fit uses two points and has two degrees of freedom per coordinate, so it is
*unfalsifiable* on those two: any two witnesses lie on some line. The claim rests on the three
witnesses that were **not** used to build it:

| witness | used in the fit | lies on the recovered line |
|---|---|---|
| `r = 5`, `x_0 = 3490692521816093` | yes (fit point) | — |
| `r = 5`, `x_0 = 20508905520120247` | yes (fit point) | — |
| `r = 6`, `x_0 = 15940424764849354` | **no** | ✓ |
| `r = 6`, `x_0 = 13453267118668680` | **no** | ✓ |
| `r = 7`, `x_0 = 471901030567494` | **no** | ✓ |

Each out-of-sample test is 11 independent coordinate agreements: solving
`x_0 = (w_j − b_j)·a_j^{-1}` in each of the 10 branches with `a_j ≠ 0` must give one common value,
and branch 0 must satisfy `w_0 = b_0 = 0` separately. So the evidence is 3 witnesses × 11
coordinates = **33 agreements over a 55-bit field against a 2-parameter fit**, and the two round
counts tested were not the round count fitted. The probability of that by chance is `p^{-30}`-ish.
Anyone can re-derive it: the arithmetic is in §9's `--witness-system`.

`a_0 = b_0 = 0`, which is Appendix B's `l_0(a) = l_0(b) = 0` constraint, and branch 0 is the only
`x_0`-independent branch of the input.

So the Griffin FreeLunch instance is now pinned **including the attack's input parametrisation**,
not only the permutation. `docs/research/additional-benchmarks.md` §4's note that "the published
witness is a 12-coordinate permutation input, while the polynomial system's variables are `x₀ … x_r`
— those are different coordinate systems" is now resolved constructively: the map between them is
this line, and `x_0 = [input]_1`.

### 1.3 The system itself, built and checked — PASS

`--build-system R` builds the FreeLunch system over the recovered line, reducing modulo the `p_i`
as Appendix A prescribes, and derives the monomial order by Construction 1 rather than quoting it.
A variable is introduced only for a round whose root actually depends on `x_0`; the bypass is
**detected**, not assumed. All figures **measured** in CPython on this box:

| `r` | vars | sysGen | `α_0 = deg_{x_0} g` | `D_H` | `D_I` | paper's `(6α+3)(α(2α+1))^{r−3}` | monomials in `g` |
|---|---|---|---|---|---|---|---|
| 3 | 1 | 0.00 s | 21 | 1 | 21 | 21 | 22 |
| 4 | 2 | 0.07 s | 147 | 3 | 441 | 441 | 255 |
| 5 | 3 | 15.0–16.8 s | 1029 | 9 | 9261 | 9261 | 4734 |

`D_I` reproduces the paper's closed form at every rung. Two further checks, both **measured**:

- **Faithfulness against the permutation oracle**: 8 random `x_0` on the line, every `p_i` vanishes
  and symbolic `g` equals the numeric `[output]_0`. PASS at `r = 3, 4, 5`.
- **The published witnesses are roots of this very system**: at `r = 5`, the whole system vanishes
  at both published witnesses. PASS.

Gate 1 is passed, and it is passed on the *system*, which is more than #202's acceptance criterion
asked for.

### 1.4 Proposition 6's hypothesis holds locally, which answers #202's question 2

#202's question 2 asks whether the Griffin CICO system really is a Gröbner basis under the
FreeLunch order, verifiably and locally, because eprint **2025/2040** (*The Algebraic CheapLunch*)
Table 1 marks the genericity assumptions **✗ for Griffin**.

Two separate things were conflated there, and separating them is the answer.

- **2025/2040's ✗ is about CICO-`k` for `k ≥ 2`.** That paper's contribution is extending FreeLunch
  *beyond CICO-1*, and Griffin is where the extension's assumptions fail. It says nothing against
  FreeLunch's own CICO-1 result, which is the one with witnesses.
- **For CICO-1 the only hypothesis is Proposition 6's**: `g` must contain the monomial
  `x_0^{d_{≤r}}`. Everything else in the proposition is structural. That hypothesis is now
  **verified locally**: `LM_{≺_G}(g) = x_0^{α_0}` with a nonzero coefficient at `r = 3, 4, 5`
  (**measured**, §1.3). So the delicate assumption is **verified locally at `r = 3, 4, 5`** --
  which is what was measured. It is not shown to *hold* in the sense the paper's proof needs,
  because that would be a statement about every `r` and about generic parameters; `r = 6` and
  `r = 7` are not checked here (§11). The distinction matters precisely because 2025/2040 flags
  this hypothesis as delicate for Griffin.

And the Gröbner-basis property itself needs **no computation at all** — which also means it needs
no Zeebra capability. The leading monomials are `x_1^α, …, x_{n−1}^α, x_0^{α_0}`: pure powers of
*distinct* variables, hence **pairwise coprime**. Buchberger's first criterion disposes of every
S-pair in the system without reducing anything. #202's plan to "verify this with
`src/grobner/buchberger.rs`'s criterion" would therefore confirm a one-line argument at the cost of
a new capability, and that is **not worth building**. This is the correct resolution of #202's
"no way to assert that input generators already form a Gröbner basis" gap: for FreeLunch systems
specifically, coprimality of the leading terms is the assertion, and it is checkable by inspection
once the leading terms are known.

## 2. Gate 2: the order, specified exactly

### 2.1 As a mathematical object

Definition 2 of the FreeLunch paper, with the weight vector of Construction 1. For a weight vector
`w = (w_0, …, w_{n−1})`:

```
x^A ≺ x^B  ⟺  Σ w_i A_i < Σ w_i B_i
              or  (Σ w_i A_i = Σ w_i B_i  and  ∃k: A_j = B_j ∀ j > k, and A_k < B_k)
```

So it is a **weighted graded lexicographic order whose tie-break reads the variables from the
*last* index down**, with `x_0 ≺ x_1 ≺ … ≺ x_{n−1}`. Two components, both of which Zeebra lacks:

1. **Non-unit integer weights** in the grading. Construction 1 sets `wt(x_0) = 1` and
   `wt(x_i) = wt(LM(q_i))/α_i`, which for Griffin with `α_i = α = 3` and round degree
   `d_i = 2α + 1 = 7` gives `wt(x_i) = 7^{i−1}/3` in the naive modelling. Over the recovered bypass
   line the denominators clear and the tool **derives** the weight vector as exact integers:

   | `r` | weight vector of `≺_G` |
   |---|---|
   | 3 | `(1)` |
   | 4 | `(1, 7)` |
   | 5 | `(1, 7, 49)` |

   This is not reachable by relabelling variables under any of Zeebra's three orders: the weighted
   degree is a genuinely different grading from total degree.
2. **The reversed variable order** in the tie-break. This *is* reachable for free: reversing the
   exponent indices in the problem encoding turns the paper's tie-break into Zeebra's
   `GradedLexicographic` tie-break. It is a labelling convention, not a capability.

Note what the order is **not**. It is not grevlex (grevlex favours the *smaller* exponent on the
right-most variable; this order favours the larger). It is not a block or elimination order. It is
not a general matrix order — a single weight row plus a lex tie-break suffices, which is the
cheapest point in the weighted-order design space.

### 2.2 What Zeebra has, and the gap

`src/poly/multivariate/monomial_order.rs` is the whole of it:
`MonomialOrder::{Lexicographic, GradedLexicographic, GradedReverseLexicographic}`, dispatched
through one `cmp<const N: usize>(&Monomial<N>, &Monomial<N>) -> Ordering`. Nothing is weighted;
nothing is parameterised. So **#202's question 1 answers negative: `≺_G` is not expressible in
`MonomialOrder` today.**

One thing that is *not* a blocker, contrary to what the degrees suggest.
`Monomial<const N: usize>` stores `exponents: [u32; N]` and `degree()` returns `u64`, so
`x_0^{1029}` at `r = 5` and `x_0^{7203}` at `r = 6` are representable with room to spare. The
exponent magnitudes are fine; it is the comparison function that is missing.

### 2.3 The capability, and what it would cost

The minimum addition is one enum variant and one comparison arm:

```rust
MonomialOrder::WeightedGradedLexicographic { weights: [u64; N], reverse_variables: bool }
```

`MonomialOrder` is `Copy` and not generic in `N`, so a `[u64; N]` payload does not fit it as
written — the variant has to carry a reference, or `MonomialOrder` has to become generic in `N`, or
the weights have to live beside the order in the structures that hold it. **That is the real cost,
and it is a cost in blast radius rather than in algorithmic work**: `MonomialOrder` is threaded
through `src/poly/multivariate/`, `src/grobner/f4/`, and `src/grobner/fglm/`, and making it generic
or reference-carrying touches all three. The comparison itself is ten lines. An honest estimate is
**a day of mechanical refactoring plus a day of test repair**, dominated by the signature change,
and it is shared with #201 (`ACICO` for `α > 3`) -- one capability serving two consumers, which is
why **#306** carries it and costs it once.

A weighted order alone is not sufficient for the method, though. §4 explains what else is needed.

**Landed in #306, and the cost estimate above was wrong** — the blast radius turned out to be five
`match` arms rather than a signature change. See §10.1.

## 3. Gate 2b: the grevlex comparand, measured

The paper asserts that the same system in grevlex "well exceeds the security level" and Griffin's
own designers estimated the same. #202's question 6 says a measured wall beats a quotation. Here it
is.

### 3.1 Two engines, same machine

Neither is Zeebra's F4. Running Zeebra's F4 would require a Griffin generator in `src/`, which
M25-D's analysis does not authorise (§8), so this is a third-party stand-in for the grevlex route
and is labelled as one everywhere.

**Both engines' prime fields stop below `2^31`** — msolve says so explicitly
(`Warning: characteristic must be 0 or < 2^31`, **measured** by feeding it the real field) — so the
comparand runs over Zeebra's own 31-bit prime `2147483647` with the Griffin coefficients reduced
into it. That is a **surrogate**: grevlex's degree of regularity and matrix dimensions are set by
the monomial support, which reduction preserves, but the field is not Griffin's, and no third-party
engine available here can take the real field at all. Recording that limit is part of the result.

The comparand is also **generous to grevlex**: the system fed in is the FreeLunch-*reduced* system
over the three-round bypass line, the smallest and best-behaved presentation there is. Without the
bypass the naive system has `r + 1` variables and `D_I = 21^r` and grevlex is strictly worse.

| `r` | vars | `D_I` | **msolve 0.11.0** `-g 2`, 1 thread | peak RSS | **Singular 4.x** `groebner` | peak RSS | `vdim` |
|---|---|---|---|---|---|---|---|
| 3 | 1 | 21 | 0.00 s | 5 MB | 0 ms | — | 21 |
| 4 | 2 | 441 | 0.01 s | 5 MB | 11 ms | — | 441 |
| 5 | 3 | 9 261 | **13.9 s** | **255 MB** | **199.4 s** | **483 MB** | 9 261 |

All **measured** on this box, single-threaded, degrevlex, reduced basis in both cases.
`vdim` agrees with `D_I` at every rung, which is an independent confirmation of §1.3's symbolic
construction by a second engine. msolve returns 470 basis elements against Singular's 463.

**The two engines differ by 14× at `r = 5`, which is why one of them was not enough.** An earlier
draft of this section quoted Singular alone and reported a 277x gap; msolve's 13.9 s shows that
figure was mostly a statement about Singular. The honest comparand is the faster engine, and the
correction is recorded rather than quietly applied.

### 3.2 What the number is, and what it is not

Against FreeLunch's Table 3 at `r = 5` — `sysGen 0.17 + matGen 0.02 + polyDet 0.53 = 0.72 s`, 14 MB,
on one core of an AMD EPYC 7352 @ 2.3 GHz — msolve's 13.9 s / 255 MB is **roughly one order of
magnitude in time and in memory**.

That comparison is asymmetric in **four** ways at once, and it is quoted to one significant figure
for exactly that reason:

1. **Different machines.** Their EPYC 7352 core against this workstation's.
2. **Different fields.** Their 55-bit `p` against this surrogate's 31-bit `q`. Narrower field
   arithmetic favours the surrogate, so the gap is if anything understated.
3. **Different implementations.** msolve's F4 against SageMath/Magma/NTL/FLINT/PML.
4. **Different objects.** A full reduced degrevlex Gröbner basis against a single univariate
   polynomial in the ideal. These are not two algorithms for one task.

So: a recorded outcome against a competitor figure, **not a speedup**, and "about an order of
magnitude" rather than a ratio. It is still the first number this repository has for a claim the
literature only gestures at.

### 3.3 The per-round scaling is NOT determined by this data

`0.00 → 0.01 → 13.9 s` is a factor of ~1 400 from `r = 4` to `r = 5` under msolve and ~18 000 under
Singular. **Both ratios are unusable**: the `r = 3` and `r = 4` points are at or below the engines'
timing floor, and the two engines disagree by an order of magnitude on the one ratio they can both
form. Extrapolating a round-count wall from them would be exactly the complexity-formula reasoning
`docs/research/elimination-beyond-grobner.md` retracted two conclusions for.

What can be said without extrapolation: at `r = 5`, where FreeLunch spends 0.72 s, a
state-of-the-art grevlex engine spends 13.9 s on a *smaller* object than the attack needs, from the
most favourable presentation of the system that exists. The `r = 6` rung would settle the scaling and
is **open** — it needs the `r = 6` system, which §11 records as beyond this tool's CPython reach.

Griffin's designers' claim that grevlex "well exceeds the security level" at the suggested round
count is therefore **neither confirmed nor refuted here**. It is made checkable: §9 reproduces the
system, and one `r = 6` build away from an answer.

## 4. Gate 3: what Zeebra would still have to build, and what it would not

The attack is `sysGen → matGen → polyDet → uniSol`. There is no F4 anywhere in it. Taking the
stages in turn, with the exact objects now known from §1.3.

### 4.1 `polyDet` is not the blocker — Zeebra can already do it

#202's question 4 expected "nothing, and building it is a separate decision", and #202's own plan
says to file a polynomial-matrix determinant issue if it turns out to be the next blocker.
**It does not, and the issue should not be filed.** Here is why.

Lemma 2 reduces `det(x_0 I_{D_I} − T_0)`, nominally a `D_I × D_I` determinant, to

```
det( x_0^{α_0} · I_{D_H}  +  Σ_{i=0}^{α_0−1} x_0^i M_i )
```

a determinant of a **`D_H × D_H` matrix over `F_p[x_0]`** with entries of degree `< α_0`, whose
output is a univariate polynomial of degree `D_I = α_0 · D_H`. And `D_H = α^{r−3} = 3^{r−3}` is
**tiny**:

| `r` | matrix order `D_H` | entry degree `< α_0` | output degree `D_I` |
|---|---|---|---|
| 5 | 9 | 1029 | 9 261 |
| 6 | 27 | 7 203 | 194 481 |
| 7 | 81 | 50 421 | 4 084 101 |

At those orders, **evaluation–interpolation over the scalar field is the right algorithm**: evaluate
the matrix at `D_I + 1` points of `F_p`, take `D_I + 1` ordinary scalar determinants, interpolate.
That is `O(D_I · D_H^3)` field operations, against PML's `Õ(D_I · D_H^{ω−1})`. Asymptotically worse
by `D_H^{4−ω}` — but `D_H ≤ 81`, and the fast algorithm carries `log(α_0)^2` factors that the naive
one does not.

**Zeebra already has every piece of this, and has measured them.** `Matrix::determinant`
(`src/linalg/matrix/mod.rs:359-387` → `src/linalg/crout.rs:135`, Crout LU with partial pivoting) is
the scalar determinant, and `src/grobner/research/resultant.rs:376-403` already runs exactly this
shape of computation — a large sweep of independent scalar determinants over an evaluation domain,
followed by interpolation — in parallel at **92–95% efficiency to 32 cores** (measured,
`docs/research/resultant-elimination.md` §6.6). `polyDet` and the resultant route's determinant
sweep are **the same computation**.

Projected from Zeebra's **measured** determinant cost of 8.5 µs at order 18 (`docs/research/`
`resultant-elimination.md`), scaling the cubic term:

| `r` | per-determinant (extrapolated) | sweep, one core (extrapolated) | FreeLunch's `polyDet` (their measurement) |
|---|---|---|---|
| 5 | ~1.1 µs | ~10 ms | 0.53 s |
| 6 | ~29 µs | ~5.6 s | 50.78 s |
| 7 | ~775 µs | ~3 170 s | 5 727 s |

Those three are **extrapolated** from one measured point by an `n³` law, and the order-18 point sits
in the overhead-dominated regime of a curve the brief records as concave in log–log, so treat them
as order-of-magnitude only; the interpolation cost (`O(D_I log^2 D_I)` with Zeebra's fast univariate
machinery, or `O(D_I^2)` naively, which at `r = 7` would dominate) is **not** included. The claim
being supported is modest and robust to all of that: **`polyDet` is within reach of code Zeebra has
already written and already parallelised.** It is not a missing subsystem.

So #202's technical gap 2 ("no polynomial-matrix determinant") is **misdirected for this instance
class**. A general `Matrix<T>`-over-a-polynomial-ring determinant, with #132's `SquareMatrix<T>`
`Ring` instance and #128's multivariate GCD behind it, is a large subsystem — and it is not what
Griffin needs. Griffin needs a univariate evaluation sweep, which exists.

### 4.2 `matGen` is the blocker, and it is the stage that blows up

`matGen` produces `M_0, …, M_{α_0−1}`, which Lemma 1 describes as "a representation of the reduction
of `x_0^{α_0} B^H_≺` modulo `I`". Concretely: `D_H` normal-form computations, one per element of
`B^H_≺ = {x_1^{a_1} … x_{n−1}^{a_{n−1}} : 0 ≤ a_j < α}`, each producing a dense coefficient block of
`α_0 · D_H` field elements. Sizes, **derived** from §1.3's measured `α_0` and `D_H`:

| `r` | normal forms | coefficients in `T_0` | at 8 bytes | FreeLunch's `matGen` (their measurement) | their peak memory |
|---|---|---|---|---|---|
| 5 | 9 | 83 349 | 0.65 MB | 0.02 s | 14 MB |
| 6 | 27 | 5 250 987 | 42 MB | 6.67 s | 471 MB |
| 7 | 81 | 330 812 181 | 2.6 GB | 3 361 s | 27.6 GB |

The `r = 7` column is why the paper writes that "the `matGen` step can sometimes be costlier than
`polyDet`" — and it is, by 4 300× from `r = 5` to `r = 7` against `polyDet`'s 10 800×, on a stage
whose complexity the authors say they cannot estimate precisely.

**This is the stage that needs the new capability, and it needs more than the order.** A normal form
against `{g, p_1, …, p_{n−1}}` requires reducing `x_0^{α_0}` by `g` (which reintroduces `x_1 … x_{n−1}`
at degree `< α`) and reducing `x_j^α` by `p_j` (which reintroduces `x_0` at high degree), alternately,
until nothing is reducible. Termination is by strict decrease in the **weighted** degree — so the
order is load-bearing for correctness even though no pair reduction ever happens. Zeebra has no
"reduce against this given basis, in this given order" entry point exposed for a basis it did not
compute; `src/grobner/fglm/` builds multiplication operators from a basis *it* produced under
grevlex. (**Overstated**: `normal_form(divisors, order)` always did reduce against a supplied
divisor set, and what was missing was the contract rather than the loop. See §10.2.)

And the FGLM machinery that looks applicable mostly is not. The paper is explicit that **FreeLunch
systems do not satisfy the stability property**, which is what the fast change-of-order algorithms
assume, and that the fast variants' assumptions "do not generally hold" here. Zeebra's FGLM is
grevlex → lex throughout (`src/grobner/fglm/mod.rs:5`, and every conversion test fixes
`MonomialOrder::GradedReverseLexicographic` as the source order). Its 14× improvement and its
shape-position detector live on the grevlex side of a boundary FreeLunch sits on the other side of.
**Zeebra's FGLM investment does not transfer to this instance class** — and that, not the order, is
the architectural answer #202 asked for.

### 4.3 `sysGen`, for completeness

`sysGen` is composing the round functions with reduction after every multiplication (Appendix A).
Measured here at 15.0–16.8 s in CPython at `r = 5` against FreeLunch's 0.17 s in
SageMath/Magma/NTL/FLINT — a ~90× interpreter penalty, which says nothing interesting. The
structural fact is that `sysGen` is `O(D_I)`-sized output and needs the same weighted normal form
as `matGen`. It is the same capability, used earlier.

## 5. Shape position (#202's question 5)

Not applicable, and the paper says why. `src/grobner/fglm/shape.rs` produces a lex basis from a
Krylov sequence when a single variable's powers span `R/I`. For a FreeLunch system that condition is
*almost* met by construction — `x_0` has `α_0 = D_I/D_H` powers in the basis — but `α_0 < D_I`
whenever `D_H > 1`, i.e. at every `r > 3`. The ideal is in shape position only at `r = 3`, where
`D_H = 1` and the system is already univariate of degree 21 (§1.3), which needs no FGLM at all.
At `r ≥ 4` the quotient is *not* spanned by powers of one variable, and `det(x_0 I − T_0)` is
precisely the substitute the paper constructs for that reason. So the third route #202 hoped to
compare does not exist here.

## 6. The architectural answer

**Does a known-Gröbner-basis formulation make Zeebra's F4 irrelevant for this instance class?**
Yes, and more completely than #202 framed it. The attack contains no Gröbner basis computation at
all — not a cheap one, none — so `src/grobner/f4/` is not slow here, it is *unused*. The grevlex
route is a different algorithm that computes a different object, and §3 measures it at about an
order of magnitude above the whole FreeLunch pipeline at `r = 5` -- on a smaller object, from the
most favourable presentation of the system, with the per-round scaling left open.

**What in Zeebra is still load-bearing?** Narrower than #202 hoped:

- `src/linalg/` and `src/grobner/research/resultant.rs`'s parallel evaluation sweep — these carry
  `polyDet` directly (§4.1), and that is a real and somewhat surprising asset.
- `src/fields/prime_field_64.rs` — the 55-bit prime needs no new arithmetic.
- Fast univariate root finding — `uniSol`, on a degree-`D_I` polynomial, which the paper calls
  negligible and which `docs/research/fast-univariate.md` and `graeffe-root-finding.md` cover.
- **Not** `src/grobner/f4/`, which is bypassed entirely.
- **Not** `src/grobner/fglm/`'s 14× improvement or its shape detector, for the stability and
  shape-position reasons of §4.2 and §5.

## 7. Issues this suggests, and one it argues against

**Argue against filing:** a polynomial-matrix determinant issue. §4.1 shows `polyDet` at `D_H ≤ 81`
is an evaluation sweep over code Zeebra has and has parallelised, not a new subsystem. Filing
"implement a polynomial-matrix determinant" would commit Zeebra to #132 + #128 + #126 for a stage
that is not the bottleneck at any rung of this ladder. If a future instance needs `D_H` in the
thousands the decision changes — and the evidence that would change it is a target whose `D_H` makes
`D_H^{4−ω}` exceed the fast algorithm's log factors, which is roughly `D_H > 10^3`.

**Filed as #306:** the weighted-order capability of §2.3, costed at about
two days and dominated by `MonomialOrder`'s signature change rather than by the comparison, shared
with #201. Plus the second half of the same capability, which #202 does not currently name: a
**normal form against an externally supplied Gröbner basis** in that order (§4.2). The order alone
buys nothing; the pair is what `sysGen` and `matGen` need.

**Worth filing, if anyone wants the instance:** "Register Griffin `r ∈ {3,4,5,6,7}` with the five
published witnesses and the recovered bypass line." §1.2's `(a, b)` makes
`CicoTarget::PlantedFrom { inputs, free }` instantiable at `k = 1` with `x_0 = [input]_1`, and §1.3
gives three self-checking rungs. This is cheap and it is the only fully witnessed CICO family in the
corpus. It is a registry entry, not an attack.

## 8. Verdict

**No-go for M25. Capability deferred to #306. Do not file a polynomial-matrix determinant issue.**

Scored against §0's gates:

- **Gate 1, faithfulness: PASS**, and overachieved. The system vanishes at both `r = 5` witnesses,
  `D_I` reproduces the paper's closed form at `r = 3, 4, 5`, Proposition 6's hypothesis -- the one
  2025/2040 flags -- is verified locally on those three rungs, and the unpublished Appendix B bypass line is recovered and
  confirmed 3 of 3 on witnesses not used to build it.
- **Gate 2, expressibility: FAIL as asked, but cheaply.** `≺_G` is a weighted graded lex with
  reversed variables and integer weights `(1, 7, 49)` at `r = 5`; `MonomialOrder` has no weighted
  variant and cannot express it. The fix is small in algorithm and medium in blast radius (§2.3).
  This is #202's question 1 answered negative, which #202 accepts as a deliverable.
- **Gate 3, worth: FAIL, and this is the decisive one.** The capability is affordable and the
  blocker is not where #202 expected it, but building the pair (weighted order + external-basis
  normal form) buys Zeebra **no mathematical ground**. It would let Zeebra recompute, on an
  instance whose witnesses are already published, a result the literature already has — and
  full-round Griffin was broken independently in eprint **2026/1281** (*Resultants Meet Resultant*,
  CICO-2, resultant-based, finishing with Villard's algorithm), so even the security statement is
  superseded. Per the M25 gate separating mathematical progress from implementation performance,
  this is at best the second kind, on an instance already solved.

The three numbers that decided it: `D_H ≤ 81` (so `polyDet` is not a missing subsystem and the
expected blocker evaporates); **13.9 s** measured for msolve's degrevlex basis at `r = 5` against
FreeLunch's **0.72 s** on a smaller object (so the architectural claim is real at about an order of
magnitude, with its four asymmetries stated and its scaling open);
and `matGen` at `3 361 s` / `27.6 GB` at `r = 7` *in the authors' own optimised implementation*
(so the stage Zeebra would have to build from nothing is the one that already dominates for the
people who built it).

What M25-D keeps from this: the bypass line, the witness-level system validation, the exactly
specified order, and the finding that Zeebra's parallel determinant sweep — built for the resultant
route — is structurally the right engine for `polyDet`. That last one is the transferable result,
and §4.1 and `docs/research/structured-sylvester.md` are where it goes.

## 9. Reproduce

```bash
# the permutation, and the (delta, mu) convention the witnesses select
tools/check-griffin-reconstruction.py

# the modelling equations at all five witnesses, and the Appendix B bypass line
tools/check-griffin-reconstruction.py --witness-system

# the system at r rounds, its order by Construction 1, D_I, and the witness check
tools/check-griffin-reconstruction.py --build-system 5

# the degrevlex comparand (Singular, surrogate prime 2^31-1)
tools/check-griffin-reconstruction.py --build-system 5 --singular /tmp/griffin-r5.sing
timeout --signal=INT --kill-after=30s 480 Singular -q /tmp/griffin-r5.sing

# regenerate the checked-in fixtures the Rust-side checks of section 10.3 read
tools/check-griffin-reconstruction.py --build-system 4 --fixture research/griffin/freelunch-r4.txt
tools/check-griffin-reconstruction.py --build-system 5 --fixture research/griffin/freelunch-r5.txt
cargo test -p zeebra griffin
```

Standard library only, no new Rust, nothing under `src/` touched. `r = 5` takes about 17 s to build
and the degrevlex comparand about 200 s; `r = 6` exceeds CPython's practical reach in this tool
(§11).

## 10. What #306 landed, and the one thing §2.3 got wrong

The capability §2.3 costed is implemented. Three things are worth recording, two of them
corrections to this document.

### 10.1 The blast radius §2.3 predicted did not happen

§2.3 priced the weighted order at "a day of mechanical refactoring plus a day of test repair,
dominated by the signature change", and a later comment on #306 measured the signature in question:
678 mentions of `MonomialOrder` and 134 functions taking one by value. Both of the routes considered
there — making `MonomialOrder` generic in `N`, or threading the weights beside it — touch all of
them.

**Neither was necessary.** `MonomialOrder::Weighted(&'static WeightedOrder)` keeps the type `Copy`,
keeps it non-generic, and keeps it two words wide, so every one of those 134 signatures accepts a
weighted order **unchanged**. The weight vector's arity cannot be checked by the type system that
way, so `cmp` asserts it at run time — and the assertion stays in release builds for the reason
`&Monomial * &Monomial`'s `checked_add` does: a weight vector zipped short against an exponent
vector is a consistent order on a *different* ring, which is wrong without being obviously wrong.

What actually changed outside `src/poly/multivariate/monomial_order.rs` was five `match` arms the
compiler demanded, all in `src/grobner/external/`, plus one guard per adapter. **Weighted orders are
refused by every external comparand**, because no engine here has a weighted spelling whose
ordering and coefficient conventions have been verified the way `tools/reference_bases.sing`
verifies the unweighted ones — the hazard §"Correctness oracle" of #306 names. `order_tag` is
deliberately non-injective for weighted orders and `order_from_tag` refuses the tag back, which is
what makes a weighted instance unconstructible from a textual contract.

### 10.2 The second half of the capability was mostly already there

§4.2 says "Zeebra has no 'reduce against this given basis, in this given order' entry point exposed
for a basis it did not compute". That overstates it:
`MultivariatePolynomial::normal_form(divisors, order)` has always reduced against a caller-supplied
divisor set under a caller-supplied order, and once the order is weighted it is already the
operation `matGen` needs. What was genuinely missing was the **contract**, not the loop.

`normal_form_modulo` is the entry point that states it: given a Gröbner basis under `order`, the
result is *the* normal form — independent of the basis permutation, zero exactly on ideal members,
linear in the dividend — and it refuses the two preconditions that can be checked cheaply (an
all-zero basis, and a weighted order whose arity is not the ring's). Alongside it,
`grobner::leading_monomials_are_pairwise_coprime` turns §1.4's one-line argument into a function:
pairwise coprime leading monomials make Buchberger's first criterion dispose of every S-pair, so the
set is a Gröbner basis with **no reduction performed**. That is the resolution of #202's "no way to
assert that input generators already form a Gröbner basis" gap, and it is `O(k²N)`.

### 10.3 The tie-break, and why the published witnesses were the test that mattered

§2.1 records that `≺_G` is "not grevlex (grevlex favours the *smaller* exponent on the right-most
variable; this order favours the larger)". That sentence turns out to be the whole correctness
surface, because of something §2.1 does not spell out: Construction 1 sets
`wt(x_i) = wt(LM(q_i))/α` **exactly**, so in every modelling equation `p_i = x_i^α − q_i` the pure
power and the tail have the *same* weighted degree. At `r = 5`, `wt(x_1^3) = wt(x_0^21) = 21`, and
both monomials are present in `p_1`. The grading decides nothing there; the tie-break decides
everything.

So choosing grevlex's tie-break by mistake does not fail — it returns a different leading ideal from
the same polynomials. `research/griffin/freelunch-r{4,5}.txt` are the systems this document's
§1.3 built, checked in by `tools/check-griffin-reconstruction.py --build-system R --fixture PATH`,
and `src/grobner/research/griffin.rs` reads them back and asserts, under the derived weight vector:

| check | `r = 4` | `r = 5` |
|---|---|---|
| weight vector from Construction 1 | `(1, 7)` | `(1, 7, 49)` |
| leading monomials under `≺_G` | `x_1^3`, `x_0^147` | `x_1^3`, `x_2^3`, `x_0^1029` |
| pairwise coprime, so a Gröbner basis by inspection | ✓ | ✓ |
| `D_I` from Zeebra's standard-monomial enumeration | **441** | **9261** |
| whole system vanishes at every published witness | — (none published) | **2 of 2** |

The `D_I` column is a fourth independent route to the same number: the paper's closed form,
`α_0 · D_H` from the symbolic build, Singular's `vdim` (§3.1), and now
`QuotientBasis::new(generators, weighted_order)`. Substituting grevlex's tie-break in the fixture's
order makes **four** of those tests fail, including both `D_I` checks — which is the only reason to
trust the tie-break at all.

What this does **not** change is §8's verdict. The capability existing does not make the attack
worth building: `matGen` at `r = 7` is still 3 361 s and 27.6 GB in the authors' own
implementation, full-round Griffin is still broken independently in eprint 2026/1281, and the
instance's witnesses are still published. #306 delivers the capability and the published-witness
regression tests; `sysGen`, `matGen`, `polyDet` and `uniSol` remain unbuilt and unscheduled.

## 11. Marked unverified, and open

- **`r = 6` and `r = 7` were not built symbolically here.** The reduced state carries up to
  `α_0 · D_H` monomials, so `r = 6` is 194 508 and `r = 7` is 4 084 182, and CPython dict-based
  multivariate multiplication does not reach them in a bounded run. `α_0` and `D_H` for those rungs
  in §4.1 and §4.2 are **derived** from the paper's closed form, which §1.3 confirms **measured** at
  `r = 3, 4, 5`. A Kronecker-substitution representation (dense in `x_0`, sparse in the tail,
  packed into Python integers) would likely reach `r = 6`; it was not written.
- **The degrevlex comparand is Singular on a surrogate prime**, not Zeebra's F4 on `p`. Both labels
  are on every number in §3. Measuring Zeebra's F4 would need a Griffin generator in `src/`, which
  §8's verdict does not authorise.
- **The `polyDet` projections in §4.1 are extrapolated** from one measured determinant point by an
  `n³` law, exclude interpolation, and ignore the concavity the M25 brief records in the measured
  determinant curve. They support "within reach", not a timing.
- **Appendix A's claim that the reduced system is the *unique* reduced Gröbner basis** was not
  checked. §1.3 confirms the leading monomials and the faithfulness, which is what gate 1 needs;
  uniqueness is not load-bearing for any conclusion here.
- **Attribution of FreeLunch's stage timings is theirs, not observed.** `sysGen`/`matGen`/`polyDet`
  splits in §4 are the paper's Table 3; the stages are not independently observable from here, so
  any attribution of *where their time goes* is a **hypothesis**.
