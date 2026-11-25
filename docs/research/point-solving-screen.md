# Point-solving feasibility screen: hybrid, crossbred, XL + block Wiedemann (#1041)

**Measured at:** branch `research/1041-point-solving` from `main` `04d949ff`. Apple M-series laptop
(48 GiB), release build, one worker, unpinned, one fresh process per solve. This is a development
screen, not a bench-host claim. The decision rule was posted on #1041 before any measurement
([comment](https://github.com/mfaulk/zeebra/issues/1041#issuecomment-7173280879)).
**Status:** complete, 2026-11-25. **Decision: proceed** for GF(2) (families C and D). A bounded
prototype proposal is filed as a follow-up issue.

Data, scripts and the full table: [`research/1041-point-solving/`](../../research/1041-point-solving/README.md).

## 1. Contract

| method | returns | fields | how a point is verified | complete (all points)? |
|---|---|---|---|---|
| Zeebra: grevlex F4 → FGLM → `solve_one` | one point | any prime field; GF(2) with field equations | substitution into the original generators | `solve_zero_dimensional` enumerates all |
| hybrid (Bettale–Faugère–Perret) | one point; all points if every branch runs | any; the `q^k` guesses restrict it to small `q` | substitution | only if every branch is completed |
| crossbred (Joux–Vitse) | the points found by enumeration | GF(2) and small `q`; `q^(n−k)` guesses | substitution | yes, if every guess is tested |
| XL + block Wiedemann | a kernel vector, read as a point | any; GF(2) packs 64 vectors per word | substitution | no: one solution, under the model |

The `q^k` and `q^(n−k)` guess counts are charged in full, unsuccessful branches included. Over
GF(31) and above, `q^k` is prohibitive for any useful `k`. At 64-bit primes no enumeration
strategy applies at all.

## 2. Instruments

- **Instances.** These are seeded, dense and planted. Every monomial of degree ≤ 2 gets a uniform
  coefficient; over GF(2) the squares are linear. They have the four Fukuoka shapes: **A**
  GF(31), m = 2n; **B** GF(31), n = 1.5m; **C** GF(2), m = 2n; **D** GF(2), n = 1.5m. Seeds are
  1–2. The generator is in [`examples/point_solving_screen.rs`](../../examples/point_solving_screen.rs);
  no Fukuoka file is used.
- **Zeebra's pipeline (measured).** `solve_one` under `GrevlexF4ThenFglm`, the opening route of
  `solve_one_planned`. F4's row and column caps are lifted, and its live-entry budget is 512 M. Over
  GF(2), field equations are adjoined. For n > m, the last n − m variables are fixed at random,
  and every attempt is charged until a point is found. The library default, `DirectLexF4`, under
  shipping budgets is not the comparand. In a 9-instance probe it was refused on 6 instances and
  10–400× slower on the other 3.
- **Hybrid (measured).** Each branch is a real substitution into the same instance. One branch is
  correct and one wrong, and the total is `(q^k − 1)·wrong + correct`.
- **Crossbred and XL + BW (counted, no solver built).**
  [`model.py`](../../research/1041-point-solving/model.py) is #75's accounting, ported from the
  module #668 moved out (commit `cd338ac4^`). Admissibility is 2024/758 Definition 5 under the
  q-semi-regular model. Preprocessing follows 2026/360 §4 and enumeration is `m·q^(n−k)·N^ω`. Its
  self-check reproduces Joux–Vitse Table 1, 2026/360 Tables 1–2 and Example 2, 2024/758 Example 2,
  and #76's 45,379,620 XL columns at n = 38. XL is `3·N²·t` at the model's degree of regularity;
  over GF(2) that is divided by the 64-bit block.
- **Rate.** Counted operations are converted at the slower of two one-core calibration runs on an
  in-cache array: 7.9·10⁹ GF(31) multiply-adds/s and 1.05·10¹⁰ GF(2) word operations/s. That is the
  most favourable rate for the counted methods. Pricing crossbred's bit-level enumeration terms as
  whole word operations is conservative for it.

## 3. Results

From [`tables.md`](../../research/1041-point-solving/tables.md), medians over two seeds:

| family | largest n × m completed | Zeebra pipeline | hybrid best (k) | crossbred | XL + BW | Zeebra ÷ best, at r | at r/4 |
|---|---|---:|---:|---:|---:|---:|---:|
| A: GF(31), m = 2n | 18 × 36 | 92.1 s | 125.2 s (1) | 1,055.5 s | 81.4 s | 1.13 | 0.28 |
| B: GF(31), n = 1.5m | 15 × 10 | 3.21 s | 6.28 s (1) | 0.50 s | 4,912 s | 6.40 | 1.60 |
| C: GF(2), m = 2n | 28 × 56 | 96.9 s | 23.6 s (4) | 0.30 s | 27.1 s | 319 | 80 |
| D: GF(2), n = 1.5m | 30 × 20 | 3.37 s | 1.28 s (4) | 11.0 ms | 0.70 s | 305 | 76 |

- **GF(31), Type III shape (A).** No method is ≥ 3× below Zeebra at the largest size. XL + BW is at
  parity (1.13× at the calibrated rate, 0.28× at r/4). Hybrid never pays, because one guess
  multiplies the work by 31. Crossbred's predicted cost is erratic across sizes (2.7 s at n = 16,
  1,056 s at n = 18) as its admissible parameters jump, and only n = 16 shows a 5× gap. This is
  #75's and #76's answer again.
- **GF(31), Type VI shape (B).** Crossbred is 6.4× below Zeebra at the calibrated rate and 1.6×
  at r/4. On its own this family would be a defer to the bench host. The gap falls with size,
  29× → 19× → 8.9× → 6.4×.
- **GF(2) (C, D).** Crossbred is **two to three orders of magnitude** below Zeebra at every size, and
  still ≥ 76× at a quarter of the calibrated rate. Zeebra's own hybrid route, specialising k = 2–4
  variables, already beats its plain pipeline by 1.0–4.1× on the larger GF(2) rows. That figure is
  measured, not counted.

## 4. What changed since #75 and #76

- **#75 (crossbred) declined because the comparison was GF(31)-only.** Crossbred's advantage
  over GF(2) was named, but Zeebra then imported no GF(2) instances and had no measured GF(2)
  pipeline. Both exist now: `docs/research/boolean-solving.md` shows that the field-equation
  pipeline works, and this screen measures it. The GF(31) conclusion stands.
- **#76 (XL + BW) stands.** At GF(31) Type III, XL's predicted cost is at parity with Zeebra here,
  not ≥ 3× below it.
- The new thing is **a workload class**: GF(2) point solving, measured on Zeebra's own pipeline for
  the first time.

## 5. Decision

**Proceed for GF(2), under the predeclared rule.** At their largest completed sizes, C and D are
≥ 3× at both r and r/4. The bounded prototype proposal is the follow-up issue linked on #1041. It
covers a GF(2) point-solving route of the crossbred family (with exhaustive enumeration as its
k = n − 1 special case), as an opt-in public capability, with its gate at the bench host.

**GF(31): close.** Hybrid, crossbred and XL + BW are not adopted at GF(31) Type III. Type VI (B)
passes only at the calibrated rate, and it is recorded as that, not as a separate proposal.

What the evidence does not establish:

- **The counted arms are predictions.** They assume semi-regular inputs and an implementation that
  reaches the in-cache rate. The r/4 margin covers some of that; a prototype covers the rest.
- **One machine, one worker.** These are not Threadripper figures, and Zeebra's multi-worker F4
  would narrow the GF(2) ratios by at most its parallel speedup, which is not measured here. It
  would have to exceed 25× to bring the r/4 ratio under 3×.
- **Zeebra's GF(2) pipeline is generic.** It has no bitsliced representation (#218). Part of the
  gap is representation, not algorithm, and a prototype should separate the two.

## 6. Reproduce

See the [README](../../research/1041-point-solving/README.md).
