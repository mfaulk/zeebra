# Order conversion: eight alternatives, and a no-go narrowed rather than reversed

**Implementation update (#368):** the library now provides certified scalar Wiedemann conversion
with explicit adaptive selection and classical fallback. See
[`certified-wiedemann.md`](certified-wiedemann.md) for the algorithm, public paired measurements
and limits. The discussion below preserves the earlier decision and its historical measurements.


Decision record for [#224](https://github.com/mfaulk/zeebra/issues/224) (D5), in the style of
[`wiedemann-krylov.md`](wiedemann-krylov.md). #224 asked what the alternatives to this crate's FGLM
conversion are, what each would cost **here**, and whether
[`MILESTONE-FGLM-SCALABILITY.md`](../MILESTONE-FGLM-SCALABILITY.md) §8.5's recorded no-go on a
sparse-FGLM milestone should stand, narrow, or reverse.

**Measured at:** `a0ddb56d` for §6.2.1 only, the one table timed here (#614). Every other timing
and memory figure is quoted from the document cited beside it, and that document declares its own
era. §4's shape position on Anemoi is an algebraic fact (a minimal-polynomial degree against a
quotient dimension) and carries no clock. The audit that re-read every other figure below is pinned
to `741c85d9`.

`anemoi.md` and `additional-benchmarks.md`, cited throughout, were moved out with the cryptanalysis
research in #668; they are preserved at commit 9532a9a2, and the section numbers cited below refer to
that commit. The same holds for the `anemoi_ladder` example and the `anemoi_shape_position` test §4
names.

**The verdict, up front.**

| # | alternative | verdict | the figure that settles it |
|---|---|---|---|
| A | shape position via a dense Krylov span (`fglm::shape`) | **keep public; not a strategy on its own merits.** It is route E's reconstruction half. | §8.3: **0.37x** on the route at `D = 64`, 0.97x–1.04x end to end. It replaces the monomial *frontier* and keeps the dense span — and the span is what an 82.8% stage is. |
| B | sparse FGLM as a milestone (Faugère–Mou) | **no-go stands, narrowed.** Not re-scoped, not opened. | `additional-benchmarks.md` §3.4.1 Table 7: on a proven-shape-position family **SparseFGLM fails at `d_I = 5^8` where Wiedemann returns in 1 212.9 s**. Building B instead of E builds the route that fails first. |
| C | stop at a univariate polynomial, no lex basis | **not an independent alternative** — it is the *output specification* that E, B and `polyDet` are three algorithms for. Recorded so it is not scoped as a seventh route. | Table 7 times all three against the same objective; `T_GB` is 0.0005–0.0013 s on every row, so the basis really is free and the univariate step really is the whole cost. |
| D | force shape position by a change of coordinates | **no, for want of a workload.** | §4: Anemoi is in shape position **natively**, so the transform has no customer there; and on cyclic/planted §8.5(3) says one should not be converting at all. |
| E | Krylov/Wiedemann on the multiplication operator | **ranks first, and it is already [#368](https://github.com/mfaulk/zeebra/issues/368).** Nothing new is authorized here. | Table 7 again — Wiedemann is the only one of three routes that survives past `d_I = 5^6` — plus §4, which satisfies the shape-position half of #58's trigger on a real family for the first time. |
| F | FreeLunch-style known bases, no conversion at all | **no, and already recorded.** | [`griffin-freelunch.md`](griffin-freelunch.md) §4.2: FreeLunch systems do not satisfy the stability property the fast change-of-order algorithms assume, and §1.3's instance is already univariate of degree 21. |
| G | the Gröbner *walk* (not FGLM's monomial walk) | **no, and it was never on the list.** Recorded because the word collides with "lex walk" and the collision is a trap. | [`singular-engine-notes.md`](singular-engine-notes.md) §7: usually slower than FGLM where FGLM applies. Its value is the positive-dimensional case, which is a capability question and not this one. |
| H | compute the lex basis directly with F4, skipping conversion | **already the default where it wins; the headroom argument against widening it is superseded** — the shipped ratio is 1.8x–6.0x on the classical corpus, not 110x. See §6.2.1. | §8.5(3): planted-8's lex basis takes F4 **0.04 ms** against a 2.8 ms conversion. Against widening it, §6.2.1 — not `MILESTONE-F4-OPTIMIZATION.md` §6.2 — is the current lex:grevlex figure. |

And the item #224 was required to defer to:

| | | |
|---|---|---|
| I | parallel border reduction ([#167](https://github.com/mfaulk/zeebra/issues/167)) | **moot twice over.** | §6.8 closed it won't-do; and border reduction does not bind on the cryptanalytic family anyway — 16.7% and *falling* with the rung (`anemoi.md` §8a.4). |

**§8.5's no-go on a full sparse-FGLM milestone stands.** What changes is its scope, not its
direction: §7 states exactly which of its three measurements survives as written, which narrows to
the katsura family, and which is now silent rather than decisive. **Three of the citations this
issue and its sources rest on do not hold as written**, and §6 is the audit — one of them reverses
the direction of the argument it is used to support.

---

## 1. What moved under this issue, and what it was filed believing

#224 was filed with three pillars and a dependency. All four have moved, and the issue's own thread
records most of it. Collected here because a reader arriving at the issue body alone would be
working from a 2026-10 picture.

| #224 said | what is true at `741c85d9` |
|---|---|
| **Q1**: does the published 2 400x conversion wall reproduce in Zeebra? `FCICO` `N = 4` decides it. | **No, and the premise was the reference's.** `anemoi.md` §8a.3: Zeebra's conversion/basis ratio is **1.40** at `N = 4` against Magma's 242. Zeebra's conversion is cheaper than its own basis. |
| pillar 2: "FGLM costs 2 400x the F4 that preceded it" is "the single most useful fact in this issue" | **Retired as a fact about FGLM.** `additional-benchmarks.md` §3.2's own correction: the same ratio is **124.6 at `p = 65537`** and 33.1 at `N = 4` there. The mechanism is Magma's `Generic finite field` arithmetic above `p = 2^32`, named in the reference's own log headers. |
| the wall is conversion | **Replaced by a real deficit pointing the same way.** `competitive-baseline.md` §1: msolve 0.11.0 does `n5-fcico` in **1.81 s** against Zeebra's 63.71 s, same machine, byte-identical generators, both under `benchlock` — **~30x on the conversion stage alone**, and msolve's route is a Wiedemann scalar sequence. |
| **Q3**: is the lex walk or border reduction binding on cryptanalytic systems? "Unknown today, because no cryptanalytic system has been profiled through `fglm_profile.rs`." | **Answered; the gap is closed.** `anemoi.md` §8a.4: at `D = 3 125` the lex walk and dependence test are **82.8%** (`FCICO`) and **92.3%** (`PCICO`), rising monotonically with the rung — 56.7% → 74.2% → 82.8% at `N = 3, 4, 5`. |
| **Q5**: measure operator sparsity before arguing | **Reported, and it is not where the cost is.** §8a.4: 3 444 of `N·D = 31 250` columns are dense (11.0%), operator bytes 0.150 GiB against the dense blocks' 0.146 GiB. See §6.3 for the one figure here that does not check out. |
| **Q6**: if border reduction binds, defer to #167 | **Both halves gone.** It does not bind (16.7%), and §6.8 closed #167 won't-do: at the default batch size one worker is the fastest row on every system in the corpus, and the splittable half of katsura-7's border stage is **24%**, not 52%. |
| **Q2**: does shape position hold on the cryptanalytic families? "the single most concrete question in the issue" | **Answered for `FCICO`/`PCICO` in §4 below, and it does.** `ACICO` has since been answered by #201 — and it also found that the "proof" behind it is incomplete; see `anemoi.md` §10.5. |
| depends on #201 for an instance that reaches conversion | **No longer.** `FCICO`/`PCICO` are registered at three characteristics and `N = 1..6`, and the ladder runner exists. #201 has since landed `ACICO` — but **not** as a proved shape-position family: `anemoi.md` §10.5 shows eprint 2025/814's Theorem 8 omits the hypothesis its own proof invokes, and exhibits an in-crate counterexample to the hypotheses as printed. |

Two things arrived that #224 did not anticipate, and both are load-bearing below:

- **`additional-benchmarks.md` §3.4.1** — the eprint 2025/814 tables that time **three** routes to the
  univariate polynomial against each other on `ACICO`. That section's own heading is "Table 7 is the
  measurement #224 (D5) was waiting for", and it is: it is the only published head-to-head between
  sparse FGLM and Wiedemann on a family of this shape.
- **`msolve-implementation.md` §3** — what msolve's `src/fglm/` actually is, from source, with the
  licensing position. It is where the "reimplement from Faugère–Mou, do not transliterate
  `invert_hankel_matrix`" line is drawn.

---

## 2. The reversal criterion, and the honest status of "written down in advance"

#224's first acceptance criterion is that the measurement which would overturn §8.5 be written down
**before** it is taken. That is the right discipline and it must not be claimed retroactively here.
What actually happened:

- A criterion **was** stated in advance, in #224's own thread: *if operator sparsity `Z` is low
  enough that `(n−k)·log(d_I) ≥ (k−1)·Z`, the Krylov route is predicted to win.* It is **not
  evaluable**, and that is this record's finding on it rather than a complaint: `n`, `k` and `Z` are
  undefined in the thread, no source is cited for the inequality, and no instrument in this crate
  reports a quantity named `Z`. `examples/fglm_operators.rs` reports entries, cells, dense columns
  and mean column density — four candidate readings of "sparsity", which is three too many for a
  one-symbol inequality.
- The criterion that *was* met in advance is **#368 stage 1's**: "profile a second Anemoi rung and
  confirm the 82.8% split is a property of the family rather than of one rung. If it does not
  reproduce, the stage-1 negative result is the deliverable." It reproduced — 56.7% → 74.2% → 82.8%
  across three rungs, `anemoi.md` §8a.4 — so #368 stage 1 is **passed on its stage-split half**.

**The criterion for reversing §8.5 specifically**, i.e. for opening a sparse-FGLM milestone, stated
here as three conditions that must all hold. The first is recorded as already satisfied; the point of
writing the other two down is that neither can be read off anything measured today.

1. **The dependence test must be the binding stage on a registered instance.** *Satisfied* —
   82.8% / 92.3% on Anemoi at `D = 3 125`, §8a.4. Recorded as satisfied rather than claimed as
   prospective.
2. **F4 must not reach the lex basis directly inside the budget that reaches the grevlex one.**
   **Unmeasured on any cryptanalytic instance.** §8.5's third measurement is that on the planted
   family one should not be converting at all, and nobody has tried F4 in lex on an Anemoi row. The
   measurement is one `f4` call per rung and needs no new code; see §8.
3. **#368 stage 2 must exist and be measured insufficient.** A scalar Krylov sequence plus
   Berlekamp–Massey is the *cheap subset* of sparse FGLM — §8.5 answer 5 and `shape.rs`' module doc
   both say so — and Table 7 says the cheap subset is the route that survives furthest on the target
   family. Opening a milestone for the expensive superset before the subset exists would be
   building the slower route first.

Conditions 2 and 3 are open, so **§8.5 is not reversed.** §7 records what it narrows to.

---

## 3. Where the cost is, by family — and the dominant stage is an input property

This is the one table the whole survey turns on, because an alternative that attacks the wrong stage
is refuted before it is costed. Shares of a whole conversion, `measure_stages` on.

| family | `D` | border reduction | lex walk / dependence | source |
|---|---:|---:|---:|---|
| katsura-5 | 16 | 43% | 29% | §9.4 |
| katsura-6 | 32 | 46% | 30% | §9.4 |
| katsura-7 | 64 | 52% | 31% | §9.4 |
| cyclic-6 | 156 | 37% | 46% | §9.4 |
| planted-8 | 256 | 31% | 49% | §9.4 |
| planted-10 | 1 024 | 15% | **69%** | §9.4 |
| Anemoi `FCICO` | 3 125 | 16.7% | **82.8%** | `anemoi.md` §8a.4 |
| Anemoi `PCICO` | 3 125 | 7.5% | **92.3%** | `anemoi.md` §8a.4 |

**The dominant stage is an input property, and it moves with `D` inside every family measured** —
katsura 29 → 30 → 31% and Anemoi `FCICO` 56.7 → 74.2 → 82.8% across their own rungs, which is what an
`O(D^3)` dependence test against an `O(D^2)`-ish border construction has to do. So "border reduction
dominates" is not a fact about FGLM; it is a fact about small `D`, and the crossover in this table
falls between `D = 64` and `D = 156`.

And **§3.4 must not be quoted here.** `wiedemann-krylov.md` §2.4 is explicit: `MILESTONE-FGLM-SCALABILITY.md`
§3 is the M17 baseline and §9.4 is the shipped configuration, M18 took katsura-7's border work from
36.60 ms to 1.44 ms without touching the walk, and the walk's share consequently went **up** — 29% /
30% / 31% where §3.4 reports 9.4% / 4.9% / 2.6%. Every row above is from §9.4 or later for that
reason.

One constraint on any proposal, from `anemoi.md` §8a.2: Zeebra's conversion at `D: 625 → 3 125`
grew **114x** against a `D^3` model's 125x. Whatever binds inside this conversion is already well
described by `D^3` on this family, which is what the dependence test is and what the border
construction is not.

### 3.1 Three engines, three dominant stages, one specification

The single most transferable thing #283 produced, and it bounds what any ratio in this record can
mean (`competitive-baseline.md` §2, `anemoi.md` §8a.7):

| engine | dominant conversion stage | share |
|---|---|---:|
| Zeebra | lex walk / dependence test | 82.8% (`FCICO`, `N = 5`) |
| Magma V2.26-2 | `Get rep mat` + Keller-Gehrig spin | 96.6% (`FCICO`, `N = 6`, `p = 65537`) |
| msolve 0.11.0 | scalar sequence (Wiedemann) | 1.45 s of 1.6 s (`FCICO`, `N = 5`) |

> **A conversion ratio between any two of them is not a measurement of FGLM.** They are not on the
> same cost curve, so the ~30x has no denominator a Zeebra Krylov route would inherit. #368 restates
> this limit and this record does not weaken it.

---

## 4. New: shape position holds on Anemoi `FCICO` and `PCICO`

#224's question 2, and the gap was real — `MILESTONE-FGLM-SCALABILITY.md` §8.3's measured reach is
the katsura family, nothing else in the benchmark corpus, and 76 of 120 differential fixtures.
`fglm::shape` had never been pointed at a cryptanalytic system.

It is now, by the `anemoi_ladder` example's `shape` subcommand and by the `anemoi_shape_position`
test, which pinned the low rungs in the suite (both moved out in #668). The probe is
**machine-independent** for the same reason the `dimensions` subcommand is: what it reports is the
degree of the lex-last variable's minimal polynomial against `dim F_p[x]/I`, and shape position is
exactly their equality. No environment is pinned and no clock is read.

A notation note, because the two models disagree about it: `N` below is the **round count**, and the
variable count is `2N` for `FCICO` and `N + 1` for `PCICO`. Where a variable index is needed it is
written `x_{n-1}` with `n` the variable count, which is what `shape_lex_basis` uses.

**24 rows — `N = 1..4`, three characteristics (`65537`, `2^32 − 209`, `2^64 − 353`), both models — and
every one is in shape position.** One `anemoi_ladder shape` filter per rung:

| rung | `D` | variables | deg of `x_{n-1}` | separating variables | shape basis equals the classical conversion's |
|---|---:|---|---:|---|---|
| `n1` `FCICO` / `PCICO` | 5 | 2 / 2 | **5** | **all** | yes |
| `n2` `FCICO` / `PCICO` | 25 | 4 / 3 | **25** | **all** | yes |
| `n3` `FCICO` / `PCICO` | 125 | 6 / 4 | **125** | **all** | yes |
| `n4` `FCICO` / `PCICO` | 625 | 8 / 5 | **625** | **all** | yes |

Each row is identical at all three primes, which is the expected shape of the result and is worth
having: the three fields are const-generic instantiations of one Montgomery path, so a prime-dependent
answer here would have been a defect rather than a finding.

Two things are stronger than #224 asked for:

- **`deg x_{n-1} = D` exactly, at every rung.** Shape position is that equality, so this is not a
  near miss anywhere.
- **Every variable separates, not just the last.** `separating_variables` returns the whole index
  range on all 24 rows. §8.3's corpus has nothing like this — katsura's separating set is its first
  and last variables only, cyclic's is empty, and planted's last variable has a degree-4 minimal polynomial at
  `D = 1 024`. On Anemoi *any* coordinate generates the quotient algebra, so the shape form is
  available in whichever variable a route finds convenient and route D has nothing left to force.

The equality in the last column is the correctness statement and is asserted rather than reported:
the reduced lex basis is unique, so a shape basis that differs from the classical conversion's is
simply wrong. That is how `examples/fglm_ablation.rs` validates every other FGLM strategy.
`anemoi_shape_position` pinned the `N = 1, 2` rows in the suite, where the whole probe costs
0.06 s.

**Three things follow, and one of them does not.**

1. **The detector does not miss.** #224 asked for a detector miss on a provable family to be
   reported as a defect. `FCICO`/`PCICO` carry no shape-position proof — eprint 2025/814's
   syntactic condition is `ACICO`'s — so this is not the proving instance #201 owns. But it is the
   first cryptanalytic family the detector has been offered, and it fires.

   > **Updated by #201.** `ACICO` is not the proving instance either, and the reason is not about
   > this crate: `anemoi.md` §10.5 reads Theorem 8's printed hypotheses, shows they are implied by
   > zero-dimensionality alone under a graded order, and exhibits a zero-dimensional ideal in this
   > crate's own corpus that discharges all of them and is **not** in shape position. The
   > hypothesis that does the work — injectivity of the projection onto the target coordinate — is
   > carried by Theorem 7 and omitted by Theorem 8, and it is exactly what `shape.rs` measures. So
   > "a detector miss on a provable family would be a defect" has no instance to be tested on, and
   > the syntactic condition is a cheap *pre-filter* rather than a decision procedure.
2. **#58's trigger has its shape-position half satisfied on a real family.** `wiedemann-krylov.md`
   §2.2 defers FGLM-Krylov until the corpus reaches large `D` **and** those instances are in shape
   position. Anemoi reaches `D = 15 625` at `N = 6` and is in shape position at every rung tested.
   The memory half of the trigger — `D` large enough that the span does not fit, crossing at
   `D = 3 162` per §9.7 — is reached at `N = 6` and not below.
3. **It does not make `fglm::shape` worth selecting.** See §5.A: the route is 0.37x at `D = 64`
   because it replaces the frontier and keeps the dense span, and the dense span is what an 82.8%
   stage *is*.

**What is not established.** Nothing above is measured at `N = 5` or `N = 6`; `N = 5` costs a ~47 s
conversion per model and `N = 6` does not reach a grevlex basis at all
([#323](https://github.com/mfaulk/zeebra/issues/323)). Shape position at `D = 3 125` and `D = 15 625`
is **unmeasured**, and the reference's `unideg = D` is evidence about the reference's output, not
about this crate's detector.

---

## 5. The eight alternatives, assessed

Each is marked as a *strategy* (an option on an existing route), a *new algorithm* (a milestone), or
a *recorded no*.

### A. Shape position via a dense Krylov span — `fglm::shape`

**Status: built, public, tested, deliberately unwired. A strategy, and the recommendation is still
not to wire it for its own sake.**

#224's deliverable includes a decision on whether `shape.rs` should become an `FglmOptions`
strategy. It should not — not on performance grounds, and §4's positive result does not change that.

The measurement is §8.3's and it is counter-intuitive, which is why `wiedemann-krylov.md` §2.1 keeps
it as a fourth measurement: the Krylov shape route is **0.37x** on the route at `D = 64` (2.018 ms
against the walk's 0.749 ms) and 0.97x–1.04x end to end. §8.3 states the mechanism: the walk's
vectors are *classes of monomials*, sparse early, and `IncrementalSpan::reduce` skips a row whose
pivot column is zero in the input; the powers of a single variable densify immediately and pay close
to the full `D^3 / 2`.

So on a family where the dependence test is 82.8% of the conversion, route A would replace the
cheaper way of driving that same span with the more expensive one. What it buys is **memory**: 1.65x
fewer dense cells at `D = 64`, and 1.95x after §8.6 took the span to `D (D + 1)`. §8.5 answer 5 is
the sentence that scopes it — "The shape route removes the accepted-vector block and nothing else, so
it is still `O(D^2)`. Only replacing the echelon form — a scalar Krylov sequence of length `2D` plus
Berlekamp–Massey — gets to `O(D)`."

**Where it is worth something is as route E's second half.** `shape.rs` already contains the
detector, the reconstruction of `x_i - h_i(t)` from `t`'s powers, and — §8.4 — the verification that
makes the whole thing certified rather than conjectural. Berlekamp–Massey replaces the span it
currently drives; nothing else in it needs to change. That is #368 stage 2 and it is costed there.

**One narrow thing worth wiring, and it is not this issue's.** `competitive-baseline.md` §9
recommends keeping [#273](https://github.com/mfaulk/zeebra/issues/273) (H17) "at low cost" on exactly
this ground: "`fglm::shape` already ships a tested detector that is deliberately unwired, so this is
connecting two existing pieces." Route selection belongs to the planner, and §4 is the first evidence
the detector would ever fire outside katsura. Routed to #273, not duplicated here.

### B. Sparse FGLM as a milestone — Faugère–Mou

**Status: recorded no. It stands, for a reason §8.5 did not give and against an argument that got
reversed in transit.**

What sparse FGLM *is*, from this repository's own source reading and from `shape.rs`' module doc:
Faugère and Mou replace the **dense dependence test** with a scalar Krylov sequence `l(t^k)` of
length `2D` and recover the minimal polynomial from it by Berlekamp–Massey. `msolve-implementation.md`
§3 confirms it against msolve's C: Krylov iteration at `fglm/fglm_core.c:662-741`, Berlekamp–Massey
at `:745-752`, and **Hankel solving instead of Gaussian elimination** at `invert_hankel_matrix`
`:203-367`. It does not make the multiplication operator cheaper to *build*; it makes it cheaper to
*use*, and it replaces the dense solve that follows.

**One qualification, and it is the grain of truth in the sentence §6.1 corrects.** msolve *does* get
part of its operator cheaply, and from a different mechanism: `msolve-implementation.md` §3.2's
free/non-free split (`hilbert.c:3489-3854`) reads a row straight off the Gröbner basis when `m · x_n`
lands exactly on a leading monomial, and computes a normal form only for proper multiples. On
katsura-5 at `p = 1073741827` the verbose output reads `#normal forms 0` — the staircase was generic
and every one of the 11 dense rows came free. That is a construction-side win, but it is **not** what
"sparse FGLM" names in Faugère–Mou, and it is orthogonal to the dependence test either engine then
runs.

That matters because **`anemoi.md` §8a.4 and #224's own thread both state the opposite**, and the
mistake points in the direction that falsely reinforces the no-go. §6.1 is the correction. The
correct reading of the same data is that on Anemoi sparse FGLM would be attacking the **82.8%**, not
the 16.7% — which is precisely why #368 exists and why `wiedemann-krylov.md` §2.3 calls the Anemoi
split "the opposite split, and the only reason this family qualifies at all".

**So why does the no-go still stand?** Because the alternative to a sparse-FGLM milestone is not
"do nothing", and the measured comparison between the two is published.
`additional-benchmarks.md` §3.4.1, from eprint 2025/814's Table 7, times three routes to the
univariate polynomial on `ACICO` at `q = 1481823929`, seconds:

| `α` | `N` | `d_I` | SparseFGLM | polyDet | **Wiedemann** | factoring |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 4 | `5^4` | 0.287 | 1045.4 | 6.85 | 0.41 |
| 3 | 6 | `5^6` | 1008.2 | — | **110.5** | 128.2 |
| 3 | 8 | `5^8` | *fails* | *fails* | **1212.9** | 14567.5 |
| 5 | 5 | `7^5` | *fails* | *fails* | **131.0** | 278.1 |
| 7 | 4 | `9^4` | *fails* | *fails* | **47.0** | 61.7 |

SparseFGLM wins at `d_I = 5^4`, loses by **9.1x** at `5^6`, and **fails** at `5^8` where Wiedemann
returns. On the family this issue is aimed at, sparse FGLM is the route that gives out first. A
milestone for it would be a milestone for the slower of two algorithms that share a reconstruction
step, and the faster one is already scoped as #368.

Two further constraints on anyone who reopens this:

- **The win is `nrows << D`, and it is measured.** `msolve-implementation.md` §3.2: nothing about
  msolve's coefficients is sparse — `dense_mat` is a plain row-major block — and only `nrows` of the
  `ncols` rows are stored at all, the rest being unit vectors encoded as index pairs. On katsura-5 at
  `p = 1073741827`, `degree of ideal 32` and `#dense rows 11`. msolve's own operation count is
  `2·nrows·ncols^2`, so the advantage over dense FGLM is entirely that ratio.
- **It is not a parallelism story.** `msolve-implementation.md` §3: two `#pragma omp` directives in
  all of `src/fglm/`, the Krylov iteration is inherently serial, Berlekamp–Massey is serial,
  `msolve/msolve.c:1851-1854` runs the whole thing single-threaded, and msolve's own block-Wiedemann
  variant is unfinished and `exit(1)`s. Zeebra's conversion is single-threaded too
  (`competitive-baseline.md` §1), so the ~30x is not a core-count artefact in either direction.

And the licensing position, from `msolve-implementation.md` §3.7 and H3: reimplementable from Faugère
and Mou (2017) and nothing is gained by adapting the code — there are **no paper citations and no
complexity statements anywhere in `src/fglm/`**, and the two engineering details worth having
(Berlekamp–Massey via half-GCD, and the structured Hankel solve) are independently published.
**What must not happen** is transliterating `invert_hankel_matrix` or `solve_hankel`; those are GPL C
and a Rust rendering of them is a derivative work.

### C. A univariate polynomial in the ideal, without a full lex basis

**Status: not an alternative. It is the objective, and B, E and `polyDet` are three algorithms for
it.** Recorded so it is not scoped as a separate route.

#224 ranked this "probably the most promising item here", on the correct observation that a full lex
basis is more than the question asks — the same slack argument #66 makes about F4. The sources agree
that this is where the cost sits: [ABM23], via `elimination-beyond-grobner.md` §1.1, has the
bottleneck shifting "from the Gröbner basis computation step to finding an univariate polynomial in
the ideal", and 2026/1905 confirms it in practice.

What #224 could not know is that §3.4.1's Table 7 **is exactly this comparison**. All three of its
timed columns produce the univariate polynomial and none produces a lex basis, and `T_GB` is
0.0005–0.0013 s on every row — the basis really is free, and the univariate step really is the whole
cost. So "stop at a univariate polynomial" does not name a route; it names the output, and the
question of which algorithm computes it is B against E, answered above.

One caution that travels with it, from §3.4.1's own closing note: at `α = 3, N = 8` **factoring
overtakes conversion** — 14 567.5 s against Wiedemann's 1 212.9 s. The wall moves off conversion and
onto root finding, which is `src/poly/univariate/` and `fast-univariate.md` §4.4's "quadratic, and it
is the binding stage". Fixing conversion on this family buys one or two rounds before a different
stage binds, and any ranking that ignores that is ranking against a wall that will have moved.

### D. Force shape position — separating variables, or a random linear change of coordinates

**Status: no, for want of a workload. Not refuted.**

`fglm::separating_variables` reports which variables generate the quotient algebra; it is a
diagnostic, not a transform. There is no change-of-coordinates path in the crate, which is #224's
technical gap 3 and it is still open.

It has no customer. §4 measures Anemoi in shape position **natively** at every rung tested, so the
family that motivated the question does not need the transform. The families that fail the test are
cyclic (§8.3: no separating variable at all) and planted (§8.3: last variable of degree 4 in a
1 024-dimensional quotient) — and §8.5's third measurement is that on planted one should not be
converting at all, because F4 reaches the lex basis directly in 0.04 ms against a 2.8 ms conversion.

There is also a hypothesis worth recording **as unmeasured**, because it is the kind of thing that
gets asserted from a formula: a dense random linear change of coordinates would be expected to
destroy the multiplication operator's sparsity, which is route E's precondition. Zeebra has the
instrument to check it — `examples/fglm_operators.rs` reports entries, cells, dense columns and mean
column density — and nobody has. Until someone does, the cost of D *to E* is unknown rather than
prohibitive.

### E. Krylov/Wiedemann on the multiplication operator

**Status: ranks first; a new algorithm; already scoped as #368 (M26-B). Nothing new is authorized
here, and this record adds no scope to it.**

The shoe fits, and `wiedemann-krylov.md` §2 says why in four lines:
`MultiplicationOperator::apply` **is** the sparse matvec and the operator is a **fixed** black box
applied `N·D` times — exactly the model Wiedemann needs and exactly what F4's elimination is not;
`IncrementalSpan` is a genuine `O(D^3)`-time dense echelon form in `O(D^2)` memory; Krylov plus
Berlekamp–Massey would replace it with `2D` matvecs and `O(D)` memory; and only Berlekamp–Massey is
missing, which `shape.rs`' module doc says outright.

What this record adds to #368's case is two things, neither of which is a reason to widen it:

- **Table 7 (§5.B above) is an external head-to-head on the target family**, and Wiedemann is the
  only one of three routes that survives past `d_I = 5^6`. #368's stage 2 is the scalar version of
  the winning column.
- **§4 satisfies the shape-position half of #58's trigger** on a registered cryptanalytic family for
  the first time. §8.5's "the systems where memory is the problem are exactly the systems the shape
  route cannot convert" was the decisive finding of the M18 spike; Anemoi is a family where the
  shape route *can* convert, at `D` up to 625 measured and 3 125 reachable.

And the three limits #368 already carries, restated because this record must not be read as lifting
them: the ~30x has no denominator a Zeebra implementation inherits (§3.1); everything is at
`p = 65537` because msolve refuses `p = 2^64 - 353`, so the deficit at 64-bit characteristic is
**unmeasured**; and it is **parity work, not frontier work** — #323 measured F4 refusing at Anemoi
`N = 6` before FGLM was reached, by 112 live nonzeros in 20 million, so F4's entry budget is the
first gate.

### F. FreeLunch-style known bases — no conversion at all

**Status: recorded no, and the record is already written. Cross-referenced, not duplicated.**

[#202](https://github.com/mfaulk/zeebra/issues/202) owns it and `griffin-freelunch.md` §4.2 is the
answer: the paper is explicit that **FreeLunch systems do not satisfy the stability property**, which
is what the fast change-of-order algorithms assume, and that the fast variants' assumptions "do not
generally hold" there. Zeebra's FGLM is grevlex → lex throughout. "**Zeebra's FGLM investment does
not transfer to this instance class** — and that, not the order, is the architectural answer #202
asked for."

`griffin-freelunch.md` §5 answers the shape-position half directly, and it is the sharper answer:
`x_0` has `α_0 = D_I/D_H` powers in the basis, so `α_0 < D_I` whenever `D_H > 1`, i.e. **at every
`r > 3`**. The ideal is in shape position only at `r = 3`, where `D_H = 1` and the system is already
univariate of degree 21 and needs no FGLM at all. At `r ≥ 4` the quotient is not spanned by one
variable's powers, and **`det(x_0 I − T_0)` is the substitute the paper constructs for exactly that
reason**.

Worth noting where that lands: a determinant of `x_0 I − T_0` is the same shape of object as Table 7's
`polyDet` column, which is the **worst** of its three routes — 1 045.4 s at `d_I = 5^4` against
Wiedemann's 6.85 s, and failing at every larger rung. The two are not asserted to be the same
implementation, and §3.4.1 does not describe `polyDet`'s; but the route FreeLunch is forced onto when
shape position fails is the route that was measured slowest on the family where all three were timed.

### G. The Gröbner walk — and the name collision that hides it

**Status: recorded no. It was never on #224's list and it should be on the record anyway.**

`singular-engine-notes.md` §7 is the only other place the term appears in this repository, and it
says so itself: `kernel/groebner_walk/` is a whole module for order conversion that, unlike FGLM,
**does not require zero-dimensionality**; "it is usually slower than FGLM where FGLM applies, so this
is a note about a structural gap, not a proposal." Its value is the positive-dimensional case, which
FGLM structurally cannot serve — a capability question, not this one.

The reason it is worth a section at all is the collision: this crate's FGLM has a stage it calls the
**lex walk**, which is the monomial walk inside classical FGLM — the `O(D^3)` dependence test of §3 —
and has nothing to do with the Gröbner walk. Every "82.8% is the lex walk" figure in this record is
the former. A reader who reads "walk" and reaches for the Gröbner-walk literature will cost
themselves a day.

### H. Compute the lex basis directly with F4

**Status: already the default where it wins. The argument against widening it is superseded, and
the current figure is unmeasured.**

M17 made the direct route the default where F4 reaches lex cheaply, on §8.5's third measurement:
planted-8's lex basis takes F4 **0.04 ms** against a 2.8 ms conversion. So this is not a proposal; it
is the status quo for part of the corpus, and the only question is how far it should widen.

The argument against widening it has been the lex:grevlex cost ratio, and **the figure usually quoted
for it is superseded.** The audit is in §6.2 below; the short form is that
`MILESTONE-F4-OPTIMIZATION.md` §6.2's katsura-6 lex figure is an M16-0 baseline, 84% of it was the
final interreduction, and §7.3.2 re-measures the same instance with the pair criteria that are now
`F4Options::recommended()`'s at **23.36 ms against grevlex's 7.66 ms — 3.05x, not 110x.** The
shipped configuration, measured in §6.2.1, is **4.70 ms against 0.78 ms — 6.0x** at katsura-6 and
1.8x–3.4x on the rest of the classical corpus.

What that does **not** license is a claim that direct lex is now affordable on a cryptanalytic
instance. Nobody has tried. It is one `f4` call per rung and §8 files it.

Two mechanisms that would make the direct path affordable at scale are recorded as not-worth-doing
*for the grevlex + FGLM pipeline specifically*, in `singular-engine-notes.md` §1 and §3 — Singular's
`stdhilb` (a Hilbert series that is a theorem rather than a prediction, driving the expensive order
from a cheap one) and `clearS` (deleting basis elements as they become redundant). §0.4 is explicit
that both become worth having the moment an ordering is wanted *directly*, and names the decisive
measurement for the first: time a grevlex Gröbner basis of a **homogenized** instance against the
inhomogeneous original. **Unmeasured.**

### I. Parallel border reduction — #167

**Status: closed won't-do, and #224's deferral to it has no referent.**

#224's item 6 required this record to defer to #167 if border reduction turned out to bind. It does
not bind — 16.7% on `FCICO` and 7.5% on `PCICO`, falling with the rung — and #167 was closed anyway.
`MILESTONE-FGLM-SCALABILITY.md` §6.8 is the refutation, and two of its figures correct numbers this
issue's framing used:

- **The splittable part of the border stage is 24%, not 52%.** At katsura-7's default batch the
  closure is 0.392 ms and the target loop 0.412 ms of a 1.74 ms conversion — 46% between them, and
  only the target loop can be split.
- **The unit available to parallelize is a batch, and a batch is small.** At the default size of 64
  the largest single batch's target loop is 210 µs on katsura-7 and 8–69 µs on everything else, against
  a measured dispatch floor of ~21 µs *per worker*, linear in the worker count. **At the default
  batch size one worker is the fastest row on every system in the corpus.**

The obstacle #167 named — the `dirty_from` carry — was measured at 1.00x–1.02x of the cells on the
only two systems whose batches are large enough to parallelize, and is not measurable in time at all.
So the obstacle was the dispatch, which the issue did not name.

---

## 6. Citation audit

Every figure this record relies on was re-read out of the document that published it at `741c85d9`.
**Three do not hold as written**, and all three are load-bearing somewhere.

### 6.1 `anemoi.md` §8a.4 has sparse FGLM attacking the wrong stage — and the error reverses the argument

§8a.4's closing paragraph reads, verbatim:

> This is also the measurement that settles §8.5's sparse-FGLM no-go for this family rather than
> overturning it. Sparse FGLM attacks the operator construction; here the operator construction is
> 16.7% and falling. Nothing in §8.5's three measurements is contradicted.

**Sparse FGLM does not attack the operator construction.** It replaces the dense dependence test —
the 82.8%. Three places in this repository say so:

- `src/grobner/fglm/shape.rs`' module doc: "It is not sparse FGLM. Faugère and Mou's algorithms
  replace the dense dependence test with a *scalar* Krylov sequence `l(t^k)` of length `2D` ... That
  is where the asymptotic win is".
- `MILESTONE-FGLM-SCALABILITY.md` §8.5 answer 5: "Only replacing the echelon form — a scalar Krylov
  sequence of length `2D` plus Berlekamp–Massey — gets to `O(D)`."
- `msolve-implementation.md` §3: the Hankel solve is "**instead of Gaussian elimination**", and the
  Krylov iteration *consumes* the multiplication matrix rather than building it.

§8.5's own first measurement is the same statement from the other side — 96% of katsura-7's
conversion is border reduction, "which sparse FGLM does not touch", i.e. sparse FGLM touches the
other 4%. On Anemoi the 4% becomes 82.8%, which is exactly why `wiedemann-krylov.md` §2.3 and #368
call this family's split "the opposite split, and the only reason this family qualifies at all".

The error is recorded here rather than silently dropped because it was repeated into #224's thread
("Sparse FGLM attacks the operator construction, so it would be attacking the small half") and used
there to conclude that no sparse-FGLM issue should be filed. **The conclusion survives the
correction** — §5.B reaches it from Table 7 instead — but it no longer rests on this sentence.
§8a.4's paragraph is corrected in place.

**Where the sentence probably came from**, since it is not an arbitrary slip: msolve *does* have a
construction-side economy, the free/non-free split of `msolve-implementation.md` §3.2, and that one
genuinely attacks the operator. It is a separate mechanism from Faugère–Mou's and §5.B records it
beside the correction rather than behind it.

### 6.2 The lex:grevlex ratio quoted against a direct lex basis is an M16-0 baseline

`singular-engine-notes.md` §0.4 reads: "the §6.2 table shows that ratio is real here too — katsura-6
is 27 ms in grevlex against 2 963 ms in lex, katsura-5 is 1.87 against 15.64", and the comment that
routed these findings into #224 quotes "the 8x–110x lex:grevlex ratios above are the headroom they
would be working against".

Both figures are in `MILESTONE-F4-OPTIMIZATION.md` §6.2 verbatim, so the quotation is accurate. **It
is also the M16-0 baseline**, and the same document supersedes it twice over:

- §6.2 itself: "**The final interreduction is 84% of katsura-6 under lex.** 2479 ms of 2963."
- §7.3.2's combined table: katsura-6 lex goes **2963.26 ms → 23.36 ms (127x)** and katsura-6 grevlex
  **27.01 → 7.66**, under the pair criteria that §7.3.2 recommends adopting. `F4Options::recommended()`
  at `741c85d9` sets `criteria: PairCriteria::ALL`, so those criteria *are* the shipped default —
  and `recommended()`'s own doc comment says "On katsura-6 under lex, the criteria have already
  reduced elimination to 9% of the total."

So the current ratio at katsura-6 is **3.05x at M16-C**, not 110x. It is not 3.05x under
`recommended()` either, which adds `Adaptive`, `Structured`, `reduce_batch_rows` and
`InterreductionRoute::ByOrder` on top. §6.2.1 measures the shipped ratio.

This matters to this survey because the 110x is the number that makes route H look hopeless, and it
is not a current number.

#### 6.2.1 The shipped ratio, measured (#614)

`cargo run --release --example f4_profile -- shipped`, which is `F4Options::recommended()` — what
`F4Options::default()` returns — with `measure_stages` on. The example's older `recommended` row is
*not* the shipped configuration: it starts from `baseline()` and so lacks #575's
`reduce_batch_rows` and `InterreductionRoute::ByOrder`; it is shown as the M16 control. Built at
`a0ddb56d` plus the `shipped` row itself, `F = Zp2147483647`, `taskset -c 6`, under
`tools/benchlock.sh` at load 1.4. One computation per cell per session, two sessions per
configuration interleaved; every total below agreed across sessions within 3%, and the ratios to
two figures. Totals in milliseconds.

| system | lex | grlex | grevlex | **lex:grevlex, shipped** | lex:grevlex, M16 `recommended` | §6.2 (M16-0) |
|---|---:|---:|---:|---:|---:|---:|
| cyclic-4 | 0.10 | 0.06 | 0.04 | — (sub-0.1 ms) | — | — |
| cyclic-5 | 0.98 | 0.76 | 0.56 | **1.8x** | 1.6x | 1.2x |
| katsura-4 | 0.08 | 0.06 | 0.06 | — (sub-0.1 ms) | — | — |
| katsura-5 | 0.45 | 0.23 | 0.21 | **2.1x** | 1.3x | 8.4x |
| katsura-6 | 4.70 | 1.05 | 0.78 | **6.0x** | 4.3x | 110x |
| random-4 | 0.54 | 0.17 | 0.16 | **3.4x** | — | — |
| planted-6 | 0.03 | 0.03 | 0.02 | — (sub-0.1 ms) | — | — |

katsura-7 is graded-only in the instrument, as it was in §6.2.

Three readings:

- **The 110x is gone, and so is the 3.05x.** The shipped lex:grevlex ratio on the classical corpus
  is **1.8x–6.0x**, largest at katsura-6. The final interreduction that was 84% of katsura-6 lex is
  now 0.52 of 4.70 ms (11%); symbolic preprocessing is the largest lex stage at 2.32 ms (49%).
- **The lex cost is batch count, not matrix cost.** katsura-6 lex runs 65 batches against grevlex's
  6, with the maximum pair degree at 37 against 7 (the example's degree-sequence table). Every
  per-batch stage is small; there are just ten times as many of them. That is the shape a direct lex
  route will scale with, and it is why this table does not license extrapolating 6x to a larger
  instance.
- **#575's pair widened the ratio it was not aimed at.** Against the M16 `recommended` control,
  grevlex falls 3.0x on katsura-6 (2.34 → 0.78 ms) and lex 2.1x (9.95 → 4.70; 107 → 65 batches),
  so the ratio rose from 4.3x to 6.0x even as both orders got faster.

None of this measures the case route H is for — F4 in lex on a cryptanalytic rung — which moved out
of this repository with the research (#668).

### 6.3 The operator-sparsity table in #224's thread is not in the sections it cites

The Q5 answer posted into #224 reports, for `D = 3 125`, `FCICO`: operator entries 12 602 286,
operator **cells 15 461 205**, cells/entries **1.23**, mean column density **12.9%**, operator bytes
**0.151 GiB**; and for `PCICO` entries 3 814 795, cells 4 183 385, density 6.5%, 0.056 GiB. It cites
"Full tables: `docs/research/anemoi.md` §8a.3 and §8a.4".

**Those figures are not in either section.** §8a.4's table at the same `D` and model publishes
operator entries 12 602 286, operator **cells 12 602 286** — equal to the entries — and operator
bytes **0.150 GiB**. The dense-column count and share agree exactly (3 444 of 31 250, 11.0%), so the
run is the same run; the cells column is not. Neither `15 461 205` nor `3 814 795` appears anywhere
in `docs/`, nor in any commit reachable from `741c85d9`.

Not re-derived, per #224's instruction. What survives for this survey is the part that is published
and checks out: **3 444 of `N·D = 31 250` columns are dense (11.0%) and operator bytes are 0.150 GiB
against the dense blocks' 0.146 GiB**, §8a.4. That is enough for the one conclusion drawn from it —
operator storage is not where the memory is — and the cells/entries ratio is not relied on anywhere
above. The PCICO column has no published counterpart at all and is not used.

### 6.4 Verified as written

| citation | status |
|---|---|
| §9.4's stage shares — katsura 29/30/31%, cyclic-6 46%, planted-8 49%, planted-10 69% | holds, verbatim |
| §3.4's superseded shares — 9.4% / 4.9% / 2.6% at `D = 16/32/64` | holds as the M17 baseline, which §3.4 labels as such; §9.4 supersedes it, per `wiedemann-krylov.md` §2.4. **Quote the 9.4%, not the 1.4%** — #58's body had 1.4% and `wiedemann-krylov.md` §6.2 found it arithmetically wrong (0.05 ms of 0.53) |
| §8.3 — katsura family in shape position and nothing else in the corpus; 76 of 120 fixtures; cyclic has no separating variable; planted-10's last variable has degree 4 at `D = 1 024` | holds |
| §8.3 — the Krylov shape route is 0.37x on the route at `D = 64`, 2.018 ms against 0.749 ms | holds |
| §8.5 — all three measurements, and answers 4 and 5 | holds |
| §6.8 — splittable half 24%; dispatch floor ~21 µs per worker; one worker fastest at the default batch on every system; carry 1.00x–1.02x | holds |
| §9.7 — `max_span_entries` crossing at `D = 3 162`; the three recommendations | holds |
| `anemoi.md` §8a.3 — Zeebra's conv/basis 1.40 at `N = 4` against Magma's 242; characteristic-flat to 12% | holds |
| `anemoi.md` §8a.2 — the conversion's own growth 114x at `D: 625 → 3 125` against `D^3`'s 125x | holds |
| `anemoi.md` §8a.4 — 82.8% / 92.3%; 56.7% → 74.2% → 82.8%; 3 444 of 31 250 dense columns | holds (but see §6.1 and §6.3 for the same section's prose and cells column) |
| `anemoi.md` §8a.7, `competitive-baseline.md` §1 — msolve 1.81 s against Zeebra 63.71 s, 35x; ~30x on the conversion stage | holds |
| `additional-benchmarks.md` §3.2 — the 2 400x and its two #283 corrections | holds |
| `additional-benchmarks.md` §3.4.1 — Table 7's five rows; `T_GB` 0.0005–0.0013 s; factoring 14 567.5 s at `N = 8` | holds |
| `msolve-implementation.md` §3.1–§3.2 — Krylov at `fglm_core.c:662-741`, BM at `:745-752`, Hankel at `:203-367`; `2·nrows·ncols^2` at `:1628`; katsura-5 `degree of ideal 32`, `#dense rows 11`, `#normal forms 0` | holds |
| `msolve-implementation.md` §3.7 and H3 — no citation and no complexity statement in `src/fglm/`; the licensing verdict and the transliteration prohibition | holds |
| `msolve-implementation.md` §3 — two `#pragma omp` in `src/fglm/`; single-threaded at `msolve.c:1851-1854`; block-Wiedemann unfinished and `exit(1)`s at `fglm_core.c:1414-1423` | holds |
| `griffin-freelunch.md` §4.2 — FreeLunch systems do not satisfy the stability property | holds |
| `griffin-freelunch.md` §5 — shape position only at `r = 3`, where `D_H = 1` and the system is already univariate of degree 21; `det(x_0 I − T_0)` is the substitute at `r ≥ 4` | holds |
| `singular-engine-notes.md` §7 — `kernel/groebner_walk/` is order conversion without zero-dimensionality, usually slower than FGLM | holds |
| `elimination-beyond-grobner.md` §1.1 — [ABM23] and 2026/1905 on the bottleneck | holds |
| `fast-univariate.md` §4.4 — root finding is quadratic and is the binding stage | holds |

Line numbers are not cited for Rust above; symbol names and file paths are, per
`wiedemann-krylov.md` §6.2's note that #58's three line citations had all drifted by one or two.

---

## 7. The verdict on §8.5

**The no-go stands. It is narrowed, and one of its three measurements is no longer decisive.**

| §8.5's measurement | status at `741c85d9` |
|---|---|
| 1. "Where conversion is the only route, the cost is not the dependence algorithm" — 96% of katsura-7's conversion is border reduction | **Narrowed to the small-`D` regime it was measured on.** Unrefuted on katsura; false on Anemoi, where border reduction is 16.7% and *falling* with the rung while the dependence test is 82.8% and rising. §3's table puts the crossover between `D = 64` (katsura-7, border ahead 52:31) and `D = 156` (cyclic-6, walk ahead 46:37), so it is a function of `D` and not of FGLM. Its parenthetical about what sparse FGLM touches is correct and was reversed downstream — §6.1. |
| 2. "Where the dense blocks dominate, the ideal is not in shape position" — planted-10's blocks are 54x its operators and its last variable has degree 4 at `D = 1 024` | **Holds as written, and is no longer decisive.** It was §8.5's "decisive finding", a claimed disjointness between shape position and memory pressure. Anemoi is in shape position (§4) and its blocks are 0.146 GiB against the operators' 0.150 — **0.97x, not 54x** — so it is neither a counterexample nor covered. The disjointness is now a property of the corpus rather than a demonstrated law. |
| 3. "On those systems one should not be converting at all" — planted-8's lex basis takes F4 0.04 ms against a 2.8 ms conversion | **Holds, and is untested where it would matter.** Nobody has run F4 in lex on a cryptanalytic instance, and the lex:grevlex headroom usually quoted against trying is a superseded baseline (§6.2). This is condition 2 of §2's reversal criterion and it is the cheapest open measurement in this record. |

**What is explicitly not recommended, unchanged from §9.7: a sparse-FGLM milestone.** §2's
conditions 2 and 3 are open, and Table 7 says the cheap subset of sparse FGLM — a scalar Krylov
sequence plus Berlekamp–Massey, which is #368 stage 2 — is the route that survives furthest on the
family that motivated the question. The expensive superset is not the first thing to build.

**What this record does recommend, and all of it is already scoped elsewhere:**

- **#368 (M26-B)** stays as it is, and its stage-1 stage-split gate is **passed** (§2). §4 passes the
  shape-position half of #58's trigger too. Nothing here widens its scope and its three limits stand.
- **#273 (H17)** is where `fglm::shape` becomes selectable, per `competitive-baseline.md` §9.
- **#201 (C5)** has landed `ACICO`. Its shape position is **not** proved syntactically — see
  `anemoi.md` §10.5 — so §4's result is not the weaker of two kinds after all; both families rest on
  the same computed separating condition, and only `ACICO` also has the syntactic half discharged
  deductively. `grobner::shape_position_hypotheses` is that half, and #201 routes the
  pre-filter-in-the-planner idea here and to #273.
- **#202 (C6)** keeps FreeLunch, answered in the negative by `griffin-freelunch.md` §4.2.

---

## 8. What this does not settle

Stated as measurements rather than as topics, because each is small and none is authorized here.

1. **F4 in lex on an Anemoi rung.** §2's condition 2 and §5.H's open question, in one `f4` call per
   rung against the existing grevlex + FGLM path. Decides whether route H widens to the family that
   matters. Filed as [#614](https://github.com/mfaulk/zeebra/issues/614).
2. **The shipped lex:grevlex ratio.** §6.2: the 110x is an M16-0 baseline and M16-C is 3.05x.
   **Measured in §6.2.1 (#614): 1.8x–6.0x on the classical corpus, 6.0x at katsura-6.**
3. **Shape position at `D = 3 125` and `D = 15 625`.** §4 reaches `D = 625`. `N = 5` is a ~47 s
   conversion per model and wants `benchlock`; `N = 6` needs #322's budgets first. Belongs to #368
   stage 1.
4. **Whether a random change of coordinates destroys operator sparsity.** §5.D's unmeasured
   hypothesis, and `examples/fglm_operators.rs` is the instrument. Only worth taking if a workload
   for route D ever appears.
5. **Whether the ~30x holds at 64-bit characteristic.** msolve refuses `p = 2^64 - 353`, so every
   comparative figure in this record is at `p = 65537`. #368 and `competitive-baseline.md` §1 both
   carry this limit; it is repeated here because it bounds route E's whole justification.
6. **The `15 461 205` operator-cells figure of §6.3.** Either a run that was not committed or a
   reporting artefact. Not re-derived.

---

## 9. References

- Faugère, J.-C., Gianni, P., Lazard, D., Mora, T. (1993). *Efficient computation of
  zero-dimensional Gröbner bases by change of ordering.* J. Symbolic Computation 16(4), 329–344.
- Faugère, J.-C., Mou, C. (2017). *Sparse FGLM algorithms.* J. Symbolic Computation 80, 538–569.
- Wiedemann, D. (1986). *Solving sparse linear equations over finite fields.* IEEE Trans. Inform.
  Theory 32(1), 54–62.
- Campa, L., Roy, A. (2025). *Gröbner Basis Cryptanalysis of Anemoi.* EUROCRYPT 2025, eprint
  2025/814 — `ACICO`, the shape-position proof (§5, applied in §6.2), and Tables 7–9.
  Read via `additional-benchmarks.md` §3.4, §3.4.1.
- Koschatko, Lüftenegger, Rechberger (2024). *Exploring the Six Worlds of Gröbner Basis
  Cryptanalysis: Application to Anemoi.* ToSC 2024 №4, 138–190 — the published ladder.
- Bak, Hostettler, eprint 2026/1905, and [ABM23] — the change-of-ordering bottleneck claim, via
  `elimination-beyond-grobner.md` §1.1.
