# Crossbred: admissible parameters, the total work across every guess, and what it would cost Zeebra

**Measured at:** not measured here — every crossbred figure below is exact integer arithmetic and
reproduces at any commit (`cargo run --release --example crossbred_dimensions`). The F4 comparands
are transcribed from [`mq-comparison-methodology.md`](mq-comparison-methodology.md) §7, which
carries their provenance; nothing in this document was timed for it.

Deliverable for **#75 (B2)**, the last open child of epic #66. #75 was blocked on source access —
`eprint.iacr.org` PDFs are 403 from this machine — and #590 was filed to say so. The owner supplied
the four papers on **2026-11-08**, which is what makes the half of #75 that needed them writable.

**What this document is.** The complexity accounting #75 asks for, stated as total work across all
guesses, with every published parameter choice this repository could find checked against it in
code. Where the literature does not reconcile — and in five places it does not — §6 says so and
names the readings, rather than picking one silently.

**What it is not.** A recommendation to implement crossbred. §8 declines, on figures.

---

## 1. The sources, and how they were read

Four PDFs, owner-supplied under #590 and read locally with `pdftotext -layout`. **None is
redistributed**: this repository contains no copy of any of them, by the same rule
[`external-provenance-policy.md`](external-provenance-policy.md) applies to the Fukuoka challenge
data — the files were read, and what is kept is understanding.

| ref | paper | what it settles |
|---|---|---|
| **2017/372** | Joux, Vitse, *A Crossbred Algorithm for Solving Boolean Polynomial Systems* | the algorithm, the `d = 1` admissibility arithmetic, and the Fukuoka type I records |
| **2024/758** | Baena, Cabarcas, Tiwari, Verbel, Villota, *Admissible Parameters for the Crossbred Algorithm and Semi-regular Sequences over Finite Fields* | `q`-semi-regularity, where the admissibility series comes from, and a **second** necessary condition |
| **2022/708** | Bellini, Makarim, Sanna, Verbel, *An Estimator for the Hardness of the MQ Problem* | the cost model the MQ estimator implements, and crossbred's place among the alternatives per Fukuoka type |
| **2026/360** | Vidal, Delaplace, Ionica, *Improved preprocessing for the Crossbred algorithm and application to the MQ problem* | the full complexity analysis, two corrections to the published estimators, and a bound that cuts the retained polynomial count by `2^45` at MQOM size |

These close the gap #75 was stopped by. The reachable source at the time was a JNCF 2024
presentation that ended "**In progress:** Theoretical complexity" and asked whether the block and
Joux–Vitse quantities agree; 2024/758 §4 and 2026/360 §2.4 both answer it, and §3 below states the
answer.

The implementation behind the hpXbred credits on [mqchallenge.org](https://www.mqchallenge.org/) is
**Bouillaguet and Sauvage, *High-Performance Xbred*,
<https://gitlab.lip6.fr/almasty/hpXbred> (2023)** — 2026/360 ref. [11]. #75 asked for it to be
located; it is not read here and nothing below depends on it.

## 2. The algorithm, in this repository's terms

`m` quadratics in `n` variables over `F_q`, parameters `(D, d, k)`, and optionally `h` further
variables fixed by an outer loop.

1. **Preprocessing.** Take the degree-`D` Macaulay matrix, keep the rows `u·f_i` with
   `deg(u) <= D - 2` and `deg_k(u) >= d - 1` (`Mac^k`), and within those the columns of monomials
   whose degree in the first `k` variables exceeds `d` (`M^k`). A left-kernel vector of `M^k` that
   is not one of `Mac^k` gives a polynomial of total degree `<= D` and degree `<= d` **in the kept
   variables**. Call the number of them `r`.
2. **Enumeration.** For each of the `q^(n-k)` assignments of the other variables, specialize those
   `r` polynomials (and, when `d > 1`, the original system), and test the consistency of the
   result by linearization at degree `d`.

Zeebra already has the pieces this is built from: `src/grobner/f4/macaulay.rs` for the
construction, `src/linalg/sparse/` for the kernel, `src/poly/multivariate/` and
`research::specialization` for step 2. What it does not have is a reason to assemble them — §7.

## 3. Admissibility is two conditions, and the three papers' series are one series

A triple is **admissible** when the inner consistency test can actually be done by linearization.
2024/758 Definition 5 gives two necessary conditions, with

```text
M_{n,q}(z)     = ((1 - z^q)/(1 - z))^n                       monomials the field equations leave
H_{n,m,q}(z)   = M_{n,q}(z) ((1 - z^2)/(1 - z^{2q}))^m       a q-semi-regular sequence's Hilbert series
S_{k,q}(w, z)  = [H_{k,m,q}(wz) M_{n-k,q}(w) - H_{n,m,q}(w) - H_{k,m,q}(z)] / ((1 - z)(1 - w))
```

- **i)** `[w^D z^d] S_{k,q}(w, z) >= 0`
- **ii)** `[z^D] (H_{k,m,q}(z) / (1 - z))_+ = 0`

and 2024/758 Theorem 2 additionally assumes `D < D_reg(F)` and `d < d_reg(F|b)`. Condition i) is
Joux–Vitse's series, generalized to `q > 2` by 2022/708 eq. (6); 2026/360 Definition 7 calls i)
plus the two degree bounds *potentially admissible* and conjectures that is already enough.
**Neither condition implies the other** (2024/758 Example 2).

The useful way to read condition i) is as a surplus. Writing `T` for the series without the last
term —

```text
T_{k,q}(w, z) = [H_{k,m,q}(wz) M_{n-k,q}(w) - H_{n,m,q}(w)] / ((1 - z)(1 - w))
```

— the three papers' quantities are the same family:

| object | this repository | 2024/758 | 2026/360 | meaning |
|---|---|---|---|---|
| `[w^D z^d] T` | `CrossbredSeries::polynomials` | `T_{k,q}`, in the proof of Theorem 2 | `G^k_{m,n}`, Proposition 3 | polynomials preprocessing produces, `r` |
| `[w^D z^d] S` | `CrossbredSeries::surplus` | `S_{k,q}`, Definition 5 i) | `J^k_{m,n}`, Proposition 4 | surplus over what linearization needs |
| `T - S` | `CrossbredSeries::specialized_corank` | `corank(Mac_d(F|b))` | — | what the specialized system is short by |

so `S = T - corank(Mac_d(F|b))`, and condition i) says "preprocessing produces at least as many
polynomials as the specialized system is missing". That identity is a committed test
(`test_the_surplus_is_the_polynomials_minus_what_linearization_needs`) rather than a remark,
because it is the only thing tying the three notations together. **This answers the open question
the JNCF presentation left:** the "block" quantity and the Joux–Vitse quantity are both real and
differ by exactly that corank, so they are not two estimates of one number.

Over `F_2` at the published parameters, **condition ii) is never the binding one.** With `m >= 2k`
the specialized system is so overdetermined that `H_{k,m,2}/(1 - z)` goes non-positive at degree 3,
so any `D >= 3` passes; 2024/758's own counterexamples are `q = 16`, and its Table 1 — where the
narrowing costs UOV up to four bits of claimed security — is `q = 16` and `q = 256`. The Fukuoka
type I records stay admissible under the stricter definition, which is pinned as a test.

## 4. The accounting: total work is a sum over guesses

```text
work(D, d, k, h) = q^h · [ T_1 + T_2 + T_3 ]            preprocessing, repeated per outer guess
                 + q^(n-k) · per_guess                   enumeration
```

with the preprocessing terms evaluated on `n - h` variables (2026/360 §4):

| term | formula | what it is |
|---|---|---|
| `T_1` | `n^3 · Σ_{D'=2}^{D-1} [z^{D'}]M_{n,q} + Σ_{D'=2}^{D-2} ([z^{D'}]M_{n,q})^ω` | generating `Mac^k`, including the General and Frobenius criteria |
| `T_2` | `(r / W) · c^2 · max(n^2/W, 1)` | the cokernel by block Lanczos, with `c` the **rows** of `M^k` |
| `T_3` | `r · n^2 · c` | multiplying the kernel basis back through `Mac^k` |
| `per_guess` | `m · N^ω`, `N = Σ_{t<=d} [z^t]M_{k,q}` | one specialized consistency test |

**The guess count is `q^(n-k)` and `h` does not change it.** That is the arithmetic behind #75's
warning, and it is a committed test. The `n = 74` type I record ran `k = 23` with `h = 12`, so
`2^51` guesses in total — the `h` only decided that they were spread over `2^12` jobs. Two
consequences worth stating:

- **Outer hybridation costs work rather than saving it.** At `(D, d, k) = (6, 1, 28)` on type I,
  preprocessing is `2^75.7` at `h = 0` and `2^85.6` at `h = 10`: dropping ten variables raises `r`
  by as much as it lowers `c^2`, so the whole `2^h` repetition is paid. What hybridation buys is
  parallelism — Joux and Vitse say exactly that — and **admissibility**: `(4, 1, 23)` generates no
  polynomials at all on 74 variables (the coefficient is negative) and 878 on 62.
- **`r` is wildly larger than needed, and that is where 2026/360's contribution lands.**
  Linearization at `d = 1` needs `k + 1` polynomials; preprocessing at type-I size produces `878`
  to `2·10^6`, and at MQOM level I `2^52`. Their Corollary 1 bounds what must be generated by
  `N + n - k - 1` — **161 polynomials against `2^52`** at MQOM level I.

Three corrections to the published estimators, all from 2026/360 §2.3, all of which change a
Zeebra-side decision:

1. **The cokernel cost is driven by rows, not columns.** 2022/708 eq. (3), Nakamura's eq. (4) and
   Chen et al. all state it in `#Col(M^k)`. The cokernel is a left-kernel computation; its cost is
   in the rows.
2. **Nobody counts the cost of building `Mac^k`.** `T_1` is absent from every prior estimate, and
   2026/360's Proposition 10 shows the criteria term dominates the cokernel for `D > 6` at `d = 1`.
3. **The retained polynomial count can be cut to `N + n - k - 1`** (their Corollary 1), which is
   the single largest term in the accounting at cryptographic sizes.

## 5. What reproduces

`src/grobner/research/crossbred.rs` computes the series and the shapes; its tests assert the
published integers, and `examples/crossbred_dimensions.rs` re-checks a subset before printing
anything. Every row below is an equality, not an approximation, unless it says `log2`.

| source | parameters | published | computed |
|---|---|---|---|
| 2017/372 Table 1, 5 rows | `n` 35–62, `k` 9–23, `D` 3–4, `d = 1` | columns `N`, polynomials `R - N` | identical, all ten integers |
| 2017/372 Table 1 row 5 | the `n = 74` record, `h = 12` | 277 288 columns, 878 polynomials | identical |
| 2026/360 Table 1, 9 rows | `m` 43–83, `d` 1–3 | `r` | identical, all nine |
| 2026/360 Table 2, 2 rows | `m = 49`, `k` 15 and 16 | `r` = 3003, 2568 | identical |
| 2026/360 Example 2 | `m = 45, n = 21, k = 13` | `g_{3,1} = 2`, `g_{4,1} = 3230` | identical, including the degree that is **not** enough |
| 2026/360 Table 6, MQOM level I | `(13, 1, 31)`, `h = 3` | `log2 #Row = 61.91`, `log2 #Col = 61.69`, `log2 r = 60.34`, `log2 t = 7.3` | 61.91, 61.69, 60.34, 7.30 |
| 2024/758 Example 2 | `q = 16, n = m = 8, k = 7, D = 7` | i) holds and ii) fails at `d = 4`; i) fails at `d = 2` | both reproduce |

That the `d > 1` rows of 2026/360's Table 1 land is what makes this more than a re-derivation of
Joux–Vitse: `d = 1` is the only case their paper's closed forms cover, and `d = 2, 3` is where the
later literature lives.

## 6. What does not reconcile

Five findings. None is fatal to the accounting; each is a place where a harness that trusted one
sentence would be wrong.

**6a. 2026/360's MQOM figures are criteria-free counts, and its Table 1 figures are not.** Their §6
says so — "number of rows (without applying the General and the Frobenius criteria)" — and the
arithmetic confirms it: `log2 #Row = 61.91` is exactly `m · Σ_{t<=D-2} binomial(157, t)`, and their
`log2 r = 60.34` is that minus the columns of `M^k`. Their own Proposition 3 series, which
reproduces their Table 1 exactly, gives **`2^52.42`** at the same parameters — `2^7.9` fewer
polynomials, because it accounts for the dependencies the criteria remove. Both numbers are
correct as stated and they are not the same quantity. A harness must not mix them, which is why
`PreprocessingShape` carries `naive_rows` and `rows` as separate fields.

**6b. 2024/758's Example 2 cannot be read so that both halves hold.** Condition ii) is a function
of `(D, d, k, m, q)` with **no `d` in it**. The example's two halves differ only in `d` — `d = 4`
and `d = 2` at the same `q = 16, n = m = 8, k = 7, D = 7` — yet the first is said to violate ii)
and the second to satisfy it. Under the only reading of `[·]_+` that makes the first half come out
as printed (truncate the quotient `H_{k,m,q}/(1 - z)`, not `H` before dividing — cumulating a
truncated `H` is non-decreasing from 1 and can never be zero), ii) fails in both. The example's
*point* is condition i), which fails at `d = 2` as printed and reproduces here; the ii) claim in
its second half appears to be a slip.

**6c. Three small internal inconsistencies in 2026/360.** The displayed sum in its eq. (6) runs
`d_2` to `D - 2`, while its Example 2 and its §6.1 both run `d_2` to `D' - 1`; the latter is the
one consistent with the published values. Its Corollary 1 says `r = N + n - k - 1` and the proof of
its Corollary 2 writes `N + n - k`; §6.1 then uses `t = 161 = N + n - k` with `n = 160` rather than
the `n - h = 157` the rest of the section uses. All three are `±1`-scale and none changes a
conclusion; `log2 t` is `7.30` against their `7.3` under any of them.

**6d. The published totals are not reproducible from the published formulas.** At MQOM level I the
accounting here gives `2^180.6` against 2026/360 Table 7's `2^177.64` for the same "original
preprocessing" — a 3-bit gap, within reach of their `T_1` constant handling and of which `r` is
fed to `T_2`. The larger gap is 2022/708 Table 1: for Fukuoka type I it reports `2^67.1` time and
`2^46.7` memory at `(D, d, k) = (6, 1, 28)`, where the column count of `M^k` at those parameters is
`2^27.14` and their own space formula `O(n_cols^2)` would then be `2^54.3`. Both of their figures
are consistent with `n_cols ~= 2^23.35`, which is not the count their §3.4 defines. **Not
adjudicated here**: their units are bit operations with a separate memory exponent `θ = 2`, and
there are enough unknowns in the model that only the authors can say. It is flagged because
`2^67` and `2^76` are different answers to "should Zeebra do this", and because 2026/360
independently argues the estimators understate preprocessing.

**6e. The per-guess term is a ceiling, not an estimate, for a bitsliced implementation.** The model
charges `m · N^ω = 2^20.1` field operations per guess at the record's parameters, so `2^71.1`
overall. The record's own published budget is 360 000 CPU-hours for the full space, which over
`2^51` guesses is **576 ns, or about 1600 cycles, per guess** on their 2.6–2.8 GHz machines.
Packing 64 `F_2` operations into a word accounts for a factor of 64 of the gap; the remaining ~10×
is the Gray-code/Möbius enumeration not redoing a solve per point at all (2017/372 Algorithm 2).
So the formula over-predicts the one crossbred cost anyone has measured by roughly `2^9.4`, all of
it in the enumeration, and all of it attributable to a representation Zeebra does not have.

## 7. What this costs Zeebra

`cargo run --release --example crossbred_dimensions`, cheapest admissible triple by total work,
against F4's measured figures on the same instances. The seconds column is a **bound, not a
measurement**: `10^9` field operations per second is above anything this repository has measured
over GF(31), chosen so the conclusion survives being wrong by orders of magnitude.

### Fukuoka type III, `m = 2n` over GF(31) — the rungs Zeebra has

| n | best `(D, d, k)` | `r` | log2 guesses | log2 per guess | log2 total | crossbred matrix | F4 measured peak | crossbred at 1e9 ops/s | F4 measured |
|---|---|---|---|---|---|---|---|---|---|
| 10 | (3, 1, 7) | 24 | 14.9 | 12.7 | 27.6 | 227 KiB | 2.6 MiB | 205 ms | **0.114 s** to a witness |
| 15 | (3, 2, 10) | 80 | 24.8 | 21.9 | 46.6 | 638 KiB | 32.7 MiB | 30.6 h | **7.8 s** to a witness |
| 20 | (4, 3, 17) | 495 | 14.9 | 33.8 | 48.7 | 18.8 MiB | 186.3 MiB | 5 days | no solution: hit the 20 M-entry cap |

Two things to read off it.

**On GF(31) crossbred loses, and not narrowly.** At `n = 15` the generous bound is 30.6 hours
against F4's measured 7.8 seconds — four orders of magnitude, with every modelling choice made in
crossbred's favour. The reason is the one #75 anticipated: with `q = 31` the enumeration branching
factor is so large that the optimum pushes `k` up to shrink `q^(n-k)`, which makes the per-guess
system big (`N = 1140` monomials at `n = 20`), and the product is still worse than one F4 run.
2022/708's own Table 1 agrees that crossbred is the best *known* algorithm for types II and III at
cryptographic size — but those are `n = 37` and `n = 38`, where F4 does not finish at all.

**The one interesting row is `n = 20`, and it is a memory-versus-time trade.** F4 did not solve it:
it stopped at the entry cap having reached degree 5, with a 186 MiB peak. Crossbred's preprocessing
matrix there is **18.8 MiB, a tenth of F4's peak**, and its total is `2^48.7` operations — days,
not seconds, but *bounded*, where F4's requirement is unbounded in the direction Zeebra ran out of.
So crossbred trades the memory wall for a time wall. That is a real property of the family and the
only argument for it on reachable instances.

**The Boolean-representation question is already answered and does not need re-doing.** #218
measured it: a sparse entry is 16 bytes at any field width, so over GF(2) it carries one bit — a
factor of 128 against a bitset — and, measured, GF(2) needs about *half* the entries and half the
row operations of a wide field on the same system because `a + a = 0` makes cancellation frequent
([`boolean-solving.md`](boolean-solving.md) §15.2, `examples/boolean_density.rs`). §6e is the same
fact from the other end: the `2^9.4` the record beats the model by is exactly what a bitsliced
Boolean representation buys, and Zeebra does not have one. Zeebra also cannot import type I at all
(`research::mq::MqField` says why), so the field where crossbred wins is the field where Zeebra has
neither the instances nor the representation.

## 8. Recommendation: decline, and keep the estimator

**No-go on implementing crossbred**, on #75's own go/no-go: "No-go if the estimated total work on
reachable instance sizes does not beat the measured plain-F4 time." On every type III rung Zeebra
has, it does not — by four orders of magnitude at `n = 15`, under a bound that favours crossbred
throughout. The partial-go clause ("if it wins only on GF(2), the Boolean representation becomes a
separate costed decision") is not reached either, because Zeebra cannot import the GF(2) types.

**Keep what was built.** `research::crossbred` is an estimator, not an algorithm: ~900 lines of
series arithmetic with no solver in it, which answers "what would this cost" for any
`(q, n, m, D, d, k)` and is checked against twenty-odd published integers. That is the artifact
that makes the decision auditable and re-decidable if the inputs change — a Boolean representation
landing, type I becoming importable, or a GF(2^8)/GF(31) instance at `n ~= 37` entering reach,
which is where 2022/708 says the family starts winning.

**What is still open**, and is a follow-up rather than a gap in this document:

- The seconds in §7 are a bound at an assumed rate, not a measured one. Converting the operation
  counts to time properly needs a measured field-operation rate for the specialized solve on this
  machine — deliverable 2 of #75 in its strict reading, and the one thing here that needs the
  bench queue.
- §6d is unresolved and belongs with the authors of 2022/708 and 2026/360, not here.

## 9. Where the model is a model

Everything in §3 to §5 is exact arithmetic over the `q`-semi-regularity assumption and the
`γ`-strong semi-regularity of its specializations (2024/758 §3, 2026/360 Definition 4). 2024/758 §5
sampled it: the full sequence was `q`-semi-regular in 99.99% of instances, the specialized sequence
in 100%, the corank prediction held in 99%, and on admissible parameters the inner consistency test
behaved as required in 100% of solution-bearing specializations and 98% otherwise — all at
`n <= 16`, which is the size where the check is affordable. Fröberg's conjecture is still a
conjecture, [`hilbert-functions.md`](hilbert-functions.md) §3 records where this repository's own
semiregular model disagrees with measurement and in which direction, and nothing in
`research::crossbred` may gate a correctness decision.
