# Monte Carlo zero skipping in conventional F4: bound, contract, development counts (#1184)

**Status:** laptop-dev stage, 2026-11-27. Opt-in implementation on conventional F4, its error bound,
differential and fault-injection tests, and deterministic screening counts. The deciding
one-worker walls against the exact route and grobx default are the bench host's (§7).
**Measured at:** `8abf1b4e` plus this branch (`feat/1184-probabilistic-zero-skip`), built with
`--release`, `CARGO_PROFILE_RELEASE_LTO=thin`, `CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16`, on a
macOS/arm64 laptop (M4 Pro) with other builds running. Every wall below is an **unpinned
development figure**. None satisfies a deciding-measurement protocol. The counts are deterministic
and do not depend on the machine.
**Related:** #955, #1080 (exact Hilbert-count skipping, a separate option that this work does not
touch), #714 ([`grobx-randomization.md`](grobx-randomization.md)), and
[`m33-grobx-attribution.md`](m33-grobx-attribution.md) §3.

## 1. Mechanism

`F4Options::monte_carlo = Some(MonteCarloZeros { seed, zero_tests, block_rows, max_blocks })`,
accepted only by `f4_monte_carlo` (code: `src/grobner/f4/monte_carlo.rs`). For each batch matrix,
after construction and before any elimination backend runs:

1. Reducer rows seed a pivot table, one per leading column. A reducer that repeats a column, or is
   not monic, is left in place for exact elimination. Neither has been observed.
2. The remaining rows are cut into blocks of `block_rows` rows, `ceil(sqrt(rows))` by default
   (Monagan–Pearce 2017 §2).
3. For each block, repeat: draw `λ_i` independently and uniformly from `F` (`FiniteField::random`).
   Reduce `Σ λ_i v_i` fully against the current pivots. A nonzero residual is normalized and becomes
   a pivot. Stop after `zero_tests` zero residuals in total (not consecutive; Demin 2026, Remark 2),
   or when the block has given as many pivots as it has rows.
4. Write the block's pivots over its first rows and zero the rest.

Then the unchanged elimination path (structured, Faugère–Lachartre, parallel, packed and the rest)
runs on the screened matrix. Every screened row is a combination of the original rows, so the
screened row space is contained in the original. It equals it unless a block was discarded while
it still held a row outside the pivot span. When the spaces are equal, the reduced row echelon form
is the same, the candidates are the same, and so is every later batch and the final basis. The
tests check this (§5).

Batch `k` draws from ChaCha12 (`rand::rngs::StdRng`) seeded with `splitmix(seed ^ splitmix(k))`, so
a call is a deterministic function of the input, the options and `seed`. The stream is fixed by the
locked `rand` version.

## 2. Error bound

**Setting.** Take one block `v_1..v_b` and the pivot span `P` when the block starts. Write `r` for
the residual rank `dim(span(P, v_1..v_b)/P)`. A test reduces `c = Σ λ_i v_i`. The residual is zero
exactly when `c ∈ P`. A nonzero residual joins `P`, so `r` drops by one. A zero residual leaves `r`
unchanged.

**Lemma (one test).** Let `α` be the largest probability `F::random` gives one element. If `r ≥ 1`,
then `Pr[c ∈ P] ≤ α^r`, conditioned on everything drawn before the test.

*Proof.* The map `λ ↦ c mod P` is linear onto an `r`-dimensional space, so some `r` coordinates form
an invertible `r × r` minor. Fix the other coordinates. At most one assignment of those `r`
coordinates lands in the kernel coset. They are drawn independently with atom `α`, so that
assignment has probability at most `α^r`. ∎

**Proposition (one block).** With `t = zero_tests`, a block is discarded while `r ≥ 1` with
probability at most

    β_t(α) = Σ_{r_1 ≥ … ≥ r_t ≥ 1} α^(r_1 + … + r_t) = α^t / Π_{k=1..t} (1 − α^k).

*Proof.* `r` never increases. On a wrong discard, every one of the `t` zero tests happened while
`r ≥ 1`. List the residual ranks at the zero tests. They form a non-increasing sequence
`r_1 ≥ … ≥ r_t ≥ 1`, and different sequences are disjoint events. By the lemma and the chain rule,
the probability of any one sequence is at most `Π α^{r_j}`. The nonzero tests in between have
probability at most 1. Summing over the sequences gives the partitions of an integer into exactly
`t` parts, whose generating function is the closed form. ∎

For `t = 2` this is the `B2` of [`grobx-randomization.md`](grobx-randomization.md), there taken
under grobx's sampler. `α = 1/q` for every prime field and for characteristic two. An odd-
characteristic extension reduces each of its `k` words mod `p`, so its atom is
`(⌈2^64/p⌉/2^64)^k` (`monte_carlo::atom`).

**Whole call.** Every screened block uses up one unit of the deterministic cap `max_blocks`
(default 2^20). Blocks beyond the cap are left for exact elimination. Each block, conditioned on the
history before it, fails with probability at most `β_t`. So

    Pr[the call drops a relation] ≤ max_blocks · β_t(α).

The cap must be fixed in advance. The observed block count is a random variable that depends on
earlier outcomes, so it does not give a union bound (#1184, item 4). An exhausted block, one that
gave a pivot for every row, carries no risk, but it still counts against the cap. That keeps the
argument a plain sum.

| Field | `β_2` per block | Whole call, `max_blocks = 2^20` | Whole call, `max_blocks = 4096` |
|---|---:|---:|---:|
| 32003 | 9.76e-10 | 1.02e-3 | 4.0e-6 |
| 2^31 − 1 | 2.17e-19 | 2.27e-13 | 8.9e-16 |
| Goldilocks, 2^64 − 59 | 2.94e-39 | 3.08e-33 | 1.2e-35 |

**Assumption, stated plainly.** These are bounds under **ideal independent uniform draws**.
ChaCha12 is a cryptographic generator, not an ideal source. Under a fixed seed every outcome is
determined, so for a given seed, input and option set the bound is a statement about the
generator, not a probability. `MonteCarloGuarantee` reports `atom`, `per_block_bound` and
`whole_call_bound`, and sets `certified` when certification discharged them.

## 3. Output contract, detection and repair

- **Always:** every returned element lies in the input ideal. Rows are monomial multiples of basis
  elements and their combinations, the same derivation invariant `Provenance::F4Output` rests on.
- **With probability at least `1 − whole_call_bound`:** the result is the reduced Gröbner basis. It
  is identical to `f4`'s.
- **On a wrong discard:** the relation that row would have given is lost. Its pair has been used
  up, so the loop need not find it again. The returned set may then fail Buchberger's criterion.
  Final minimization can also drop an element that a Gröbner basis would have made redundant, so
  the set may generate a smaller ideal.
- **Detection:** `F4Options::certify = true` runs `certify_f4_output`. It checks that every input
  generator reduces to zero and that every S-polynomial reduces to zero. Either failure is
  `F4Error::CertificationFailed`, and no basis is returned. A certified result is exact. This turns
  the mode into Las Vegas, at the price of the certificate.
- **Repair:** rerun with a fresh seed, which is an independent attempt, or on the exact route.
  Nothing retries automatically at this stage.
- **API separation:** the exact entry points (`f4`, `f4_with_options`, `f4_reported`,
  `f4_observed`, `f4_observed_reported`) return `F4Error::InvalidOptions` when `monte_carlo` is set.
  So does `GradedEngine::Adaptive`, because the mode is conventional-only. `f4_monte_carlo` returns
  `MonteCarloBasis`, a distinct type that carries the guarantee. The default (`None`) is unchanged
  at every preset.

The issue's other priced checks are not implemented here: solution substitution, a Hilbert-count
check where the series is known (#1080's machinery), and a second-prime or second-seed run.

## 4. Signature F4: not covered

The mode screens conventional F4's matrices only. In the signature engine a wrong zero inserts a
false syzygy signature, and that signature prunes later pairs: Eco-12 has 689,359 such prunings.
The lost work does not show as a missing row of one matrix. A final span check cannot certify
signature-prefix syzygies ([`grobx-randomization.md`](grobx-randomization.md), *Work and
exact-acceptance cost*), and random combinations mix signatures. That route needs its own design:
a test of `s` combinations per signature group against unchanged pivots, with bound `α^s`, plus a
signature-aware validator. That is #1184 item 2, left open. `f4_monte_carlo` never dispatches to it.

## 5. Tests

In `src/grobner/f4/monte_carlo.rs`:

- **Identity with the exact route.** Eleven corpus systems × three orders × five option presets
  (default, baseline, unstructured sparse, Faugère–Lachartre, echelon batch rows) × three seeds ×
  four block sizes (`sqrt`, 1, 3, 1000). Also Katsura-4/5, Cyclic-4/5 and Eco-6 under grevlex and
  grlex × three seeds. Every basis equals `f4_with_options`'s.
- **Counts.** On the benchmark families, `rows_ruled_zero` equals the exact route's `zero_rows`.
- **Reproducibility.** Equal seeds give equal statistics and guarantees. Different seeds give the
  same basis and the same blocks, pivots and rows ruled zero.
- **Cap.** `max_blocks ∈ {0, 1, 3, 17}` bounds the blocks screened, and the rest is reduced
  exactly. At 0 nothing is screened.
- **Bound arithmetic.** The partition sum, the 2^31 − 1 figure, `t = 0 ⇒ 1`, and the atoms.
- **Refusal.** The exact entry points and the adaptive engine refuse the option.
  `f4_monte_carlo` without it is refused.
- **Fault injection.** `zero_tests = 0` discards every block untested. On Katsura-4 the basis
  differs from the exact one, `whole_call_bound = 1`, and with `certify` the call is
  `CertificationFailed`. The same call with `zero_tests = 2` certifies.

## 6. Development counts and walls

`cargo run --release --example monte_carlo_zeros -- --target T --seeds 1,2,3`. One worker, conventional
F4, default options otherwise. Counts are identical across seeds 1, 2 and 3 on every row, and every
basis equals the exact one by digest. Walls are single unpinned laptop runs.

| Target | Exact zero rows | Rows screened | Blocks (discarded) | Zero combinations reduced | Rows ruled zero | Exact wall | MC wall (3 seeds) |
|---|---:|---:|---:|---:|---:|---:|---:|
| MQ11 / Goldilocks | 6,293 | 10,365 | 297 (248) | 496 | 6,293 | 24.1 s | 11.5 / 11.5 / 11.9 s |
| Eco-12 / 2^64 − 59 | 6,331 | 12,990 | 381 (348) | 696 | 6,331 | 11.5 s | 10.5 / 9.3 / 9.1 s |
| Katsura-11 / 2^31 − 1 | 3,936 | 7,438 | 235 (220) | 440 | 3,936 | 6.3 s | 4.4 / 4.3 / 4.3 s |
| MQ10 / 2^31 − 1 | 1,528 | 3,215 | 147 (131) | 262 | 1,528 | 0.70 s | 0.77 / 0.68 / 0.61 s |
| MQ10 / 32003 | 1,528 | 3,215 | 147 (131) | 262 | 1,528 | 0.92 s | 0.90 / 0.91 / 0.96 s |
| Cyclic-7 / 2^31 − 1 | 2,106 | 4,511 | 295 (188) | 376 | 2,106 | 0.18 s | 0.18 / 0.19 / 0.17 s |

**Reading.**

- The zero rows are the conventional route's: 6,293, 6,331 and 3,936, matching
  [`m33-grobx-attribution.md`](m33-grobx-attribution.md) §3. The issue's 540 is the *signature*
  route's count on MQ11, which §4 leaves out.
- Of 6,293 zero rows on MQ11, the mode reduces 496 combinations to zero (two per discarded block)
  and rules out the rest. grobx's signature run reduces 26 and rules out 562.
- Screening costs are real. MQ11 does 11.9 G coefficient products while screening, against the
  exact conventional route's 20.4 G in total (M33 §3). On MQ10 the walls are flat. Building each
  combination costs a block's worth of rows, so this cost grows with rank × block size.
- **Block size** on MQ11, seed 1, one run each: 4 rows → 42.2 s, 8 → 17.5 s, 16 → 13.5 s,
  `sqrt` → 11.5 s, 64 → 27.2 s. The default stays `sqrt`.
- **Against the best configuration.** On MQ11 the bench-host signature arm ran in 4.9 s (M33-G1,
  historical). That is far below either conventional figure here, so this stage gives no evidence
  that conventional + Monte Carlo beats the best qualified Zeebra configuration on that row. The
  issue's predicted ceiling, about 1.0 s of 4.3 s, concerns the signature route.

## 7. Left for the bench host, and open items

- The deciding one-worker walls (Done-when item 3) on MQ11 / Goldilocks, dense MQ n = 15–18 and
  Eco-12: the Monte Carlo route against the exact route, the best qualified configuration and grobx
  default, under `tools/bench-job` with paired ratios. The example above is the harness, and its
  `counts` reproduce on any machine.
- Panel rows at three seeds on the bench host (Done-when item 2). Development agreement is in §5–6.
- The signature engine (§4, issue item 2) and its fault-injection test.
- Cheaper screening: adaptive block sizes, or forming combinations from rows already reduced
  against the reducer block, to cut the rank × block cost that keeps MQ10 flat.
- Optional checks priced separately (§3): solution substitution, the Hilbert count where #1080
  applies, and a second seed.
