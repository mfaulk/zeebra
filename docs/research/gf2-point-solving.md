# GF(2) point solving by enumeration: the bounded crossbred prototype (#1156)

**Measured at:** `ade8d741` (branch `feat/1156-gf2-crossbred`). Apple M-series laptop (48 GiB),
release build, unpinned, one fresh process per solve, with other sessions running (load average
about 3). This is a development measurement, not the gate. **The deciding measurement has not been
taken.** It needs the bench host; see §5.
**Status:** implemented and tested, 2026-11-25. **Decision: pending the gate.**

Parent: #1041, whose screen ([`point-solving-screen.md`](point-solving-screen.md)) predicted that
crossbred is 305–319× below Zeebra's field-equation pipeline on dense planted `GF(2)` systems. This
note covers the smallest route that can confirm or refute that prediction.

## 1. Contract

| | |
|---|---|
| input | quadratic polynomials over `GF(2)` in `n ≤ 64` variables (`MultivariatePolynomial<N, Zp2>`, or monomial bitmasks) |
| semantics | `GF(2)`-rational points; every exponent above one is read as one (`x_i² = x_i`), so cubic-or-higher Boolean degree is refused (`Gf2PointError::NotQuadratic`) |
| output | `gf2_solve_one`: one point or `None`; `gf2_all_points`: every point, ascending |
| verification | every returned point is substituted into the **original** generators; a failure is `VerificationFailed`, a bug, never an answer |
| completeness | both methods: `None` means no point exists |
| determinism | the point `gf2_solve_one` returns is the first one in a fixed chunk order, so it does not depend on `workers` (asserted at 1, 2, 3 and 8) |
| default | opt-in; no planner, dispatch or existing default changed |

Code: `src/grobner/gf2_points/` (`kernel.rs`, `crossbred.rs`, `mod.rs`). Harness:
[`examples/gf2_points.rs`](../../examples/gf2_points.rs).

## 2. Design

**The kernels are separate from the algorithms** (`kernel.rs`), so that a gap can be split between
representation (#218) and algorithm. Both are bitsliced across *equations*: lane `e` of a `u64` is
equation `e`.

- **`QuadraticLanes::gray_code_zeros`** is the fast exhaustive search of Bouillaguet et al. (CHES 2010). At
  step `i` the walk flips `k1 = ctz(i)`, and the first derivative `D_k1 f` changes by the one
  constant `a_k1k2`, `k2 = ctz(i & (i − 1))`. That is two word `xor`s per point for 64 equations.
  The derivation is in the function's comment. Measured: 0.94 ns per point (2^30 points in 1.01 s,
  §4).
- **`mobius_in_place`** evaluates bitsliced multilinear polynomials on a whole `c`-cube by the
  binary Möbius transform, `c/2` word operations per point and output slot. It is a stand-in. The
  degree-`D` Gray-code kernel costs `D` operations per point, so it would be about `c/(2D)` faster
  (2.3× at `c = 14`, `D = 3`).

**Exhaustive search** (`Gf2Method::Exhaustive`) fixes the high `n − 20` variables per chunk.
Specializing a chunk changes only the linear and constant lanes, so the quadratic lanes are built
once. Only the first 64 equations are in the lanes; a lane zero is then checked against all of
them, at an expected `2^(n − 64)` false candidates.

**Crossbred** (`Gf2Method::Crossbred`, Joux–Vitse, ePrint 2017/372) at `(D, d = 1)` with `k` kept
variables `0..k`:

1. **Preprocessing.** The Boolean Macaulay matrix has rows `u·f_i` for every multilinear `u` of
   degree `≤ D − 2`, and columns for every multilinear monomial of degree `≤ D`. The columns of degree
   `≥ 2` in the kept variables are ordered first. One packed Four Russians RREF
   (`linalg::gf2::reduced_row_echelon_four_russians`) follows. The pivot rows that lead in a low column
   are combinations of the form `Σ_{p<k} x_p·g_p(y) + g_k(y)`.
2. **Enumeration.** Per chunk of `2^14` assignments `y` of the enumerated variables, every `g_p` is
   evaluated by the Möbius kernel, 64 combinations per word. At each `y` the combinations are a
   linear system in `k` unknowns. It is reduced row by row, so a guess that cannot satisfy it (almost
   every guess) is rejected after about `k + 1` rows. Every solution of the linear system is checked
   against the whole quadratic system.

Every point satisfies every combination, so nothing is lost. A rank-deficient guess enumerates its
whole affine solution set.

**Underdetermined shapes (`n > m`) are solved directly.** The walk stops at the first point, and a
random system with `n > m` has about `2^(n − m)` of them. #1041's pipeline instead fixed `n − m`
variables at random and retried on a miss, charging every attempt. Here nothing is fixed and
nothing is retried.

## 3. Correctness evidence

Every test is in `src/grobner/gf2_points/` and runs in CI's debug suite.

| test | asserts |
|---|---|
| `every_method_returns_exactly_the_brute_force_points` | exhaustive, and crossbred at every `k ∈ 1..=n` and `D ∈ 2..=min(n, 4)`, return exactly brute force's point set for `n ≤ 9` and `m ∈ {1, n/2+1, n, 2n, 70}`, planted and unplanted. `m = 70` is the more-than-64-equations path, and `k = n` is pure linearization |
| `polynomial_route_agrees_with_rational_points_by_enumeration` | the field-polynomial entry points match `rational_points_by_enumeration` (#1156 scope 3), including terms with squared variables |
| `agrees_with_the_field_equation_pipeline_as_sets` | the same point set as `with_field_equations` + `solve_zero_dimensional` on #1041's dense planted shape (scope 3) |
| `the_point_returned_does_not_depend_on_workers` | four chunks, 1–8 workers: the same `solve_one` point and the same full set |
| `solve_one_agrees_with_brute_force_on_existence` | `None` exactly when brute force finds nothing |
| `crossbred_preprocessing_shape` | the Macaulay row, column and high-column counts, by formula |
| kernel tests | the Gray-code walk reports exactly the common zeros, at every point, `t ≤ 12`; Möbius agrees with direct subset sums; the linear solve returns exactly the affine solution set |

**Mutation check.** The tests were run against two deliberate faults. Dropping the walk's
initial-derivative term failed 7 of the 16 tests; moving the high-column threshold from 2 to 3
failed 6.

**The preprocessing reproduces the model's shape.** At #1041's C-28×56 parameters
`(k, D) = (13, 3)`, the matrix is 1,624 × 3,683 with 1,534 high columns, and 90 combinations are
retained. `model.py`'s `shape()` predicts `rows = polynomials + columns` = 90 + 1,534 = 1,624.

## 4. Development measurements

Medians of 3 runs on #1041's instances (`examples/gf2_points.rs` generates them bit for bit as
`point_solving_screen --q 2` does), one worker, seeds 1 and 2. "One" is the `solve_one` task. "All"
walks every point and is the worst case for the one-point task. Crossbred is at the model's
parameters from [`tables.md`](../../research/1041-point-solving/tables.md). Every returned point
verified.

| shape | seed | exhaustive, one | crossbred, one | exhaustive, all | crossbred, all | #1041 pipeline (one) | #1041 crossbred prediction |
|---|---:|---:|---:|---:|---:|---:|---:|
| C 20 × 40, (12, 3) | 1 | 1.38 ms | 3.09 ms | 1.02 ms | 2.86 ms | 249.2 ms | 2.4 ms |
| | 2 | 0.51 ms | 2.73 ms | 0.98 ms | 2.75 ms | | |
| C 24 × 48, (12, 3) | 1 | 9.85 ms | 7.17 ms | 16.07 ms | 8.53 ms | 2.47 s | 35.7 ms |
| | 2 | 12.55 ms | 7.99 ms | 15.90 ms | 8.16 ms | | |
| C 28 × 56, (13, 3) | 1 | 25.63 ms | 13.69 ms | 252.92 ms | 32.44 ms | 96.89 s | 303.4 ms |
| | 2 | 12.42 ms | 12.61 ms | 253.80 ms | 32.27 ms | | |
| D 18 × 12, (1, 2) | 1 | 14.9 µs | 206.4 µs | 251.8 µs | 3.26 ms | 13.5 ms | 29.0 µs |
| | 2 | 15.0 µs | 187.5 µs | 240.9 µs | 3.25 ms | | |
| D 24 × 16, (1, 2) | 1 | 77.9 µs | 1.43 ms | 16.08 ms | 200.96 ms | 325.0 ms | 560.9 µs |
| | 2 | 27.1 µs | 346.2 µs | 15.85 ms | 202.42 ms | | |
| D 30 × 20, (1, 2) | 1 | 1.24 ms | 15.52 ms | 1.01 s | 12.88 s | 3.37 s | 11.0 ms |
| | 2 | 0.52 ms | 9.95 ms | 1.01 s | 12.91 s | | |

The #1041 columns are copied from its tables, which were measured at a different commit on the same
class of machine and give the median over both seeds. Read them as scale, not as paired ratios.
`exhaustive, all` on D also returns 59–1,082 points: every point, not one.

What the table says, as far as a laptop can:

- **The prediction holds on C, with room to spare.** At 28 × 56, crossbred's complete walk (32 ms)
  is 9× below #1041's prediction (303 ms). Even the worst case, exhaustive over all 2^28 points
  (253 ms), is about 380× below the pipeline's 96.9 s. The one-point task is 13 ms by either method.
- **Crossbred overtakes exhaustive between 20 and 24 variables on C**, and is 7.8× faster at 28 when
  all points are walked, against 1.9× at 24. The gap widens because the enumeration is `2^(n−k)`
  against `2^n` once preprocessing is amortized.
- **On D, `(k, D) = (1, 2)` is exhaustive search plus overhead and loses by 13×.** The model priced it
  as exhaustive search over `n − 1` variables at one operation per point. This implementation pays
  the Möbius kernel and a one-variable linear solve at every guess instead. On D, use
  `Gf2Method::Exhaustive`. A parameter chooser would have to know this.
- **Underdetermined D shapes take microseconds to milliseconds for one point.** That reflects the
  `2^(n − m)` density of points, not an algorithmic win, and §5's gate must not be read off this
  column alone.

## 5. The gate (for the bench host)

The gate in #1156 is **≥ 10× complete-task wall** against Zeebra's best `GF(2)` configuration,
including its own hybrid route, at the largest Type I (C) and Type IV (D) shapes that configuration
completes, at 1 and 16 workers. It is taken under the shared measurement rules: `tools/bench-job`, a
frozen tag, paired ratios with bootstrap intervals. Below 10×, the route closes and the result is
recorded on #1041.

Proposed for predeclaration on #1156 before the session. This is a proposal, not posted yet:

1. **Shapes:** C at `n ∈ {24, 28}` and D at `n ∈ {24, 30}`, plus the largest of each that Zeebra's
   pipeline completes under a 600 s wall on the bench host, if larger. Seeds 1–5.
2. **Zeebra arm:** the best of #1041's pipeline (`point_solving_screen --mode pipeline`) and its
   hybrid branches at `k ∈ {2, 3, 4}`, per shape, at the same worker count.
3. **Prototype arm:** `examples/gf2_points.rs`, one point (`solve_one`), with whichever of
   exhaustive and crossbred at the model's parameters is faster per shape. The choice is fixed from
   this note's table before the session: crossbred on C at `n ≥ 24`, exhaustive otherwise.
4. **Score:** per shape, the geometric mean over seeds of the paired ratio, with a bootstrap 95%
   interval. The gate passes if the lower bound is ≥ 10 at the largest C and the largest D shape, at
   1 and at 16 workers.
5. **Also recorded, not gating:** the all-points wall (§4's worst case) and the Gray-code kernel's
   ns per point.

On this note's figures the gate would pass by more than two orders of magnitude. That is why it is
written down before anyone measures it, so it cannot drift.

## 6. Limitations and follow-ups

- **No parameter chooser.** The caller supplies `(k, D)`. A port of `model.py`'s admissibility plus a
  cost model calibrated to *this* implementation (§4's D finding) would be the follow-up, and only if
  the gate passes.
- **The Möbius kernel is the slower of the two textbook kernels.** A degree-`D` Gray-code
  enumeration (Bouillaguet et al.) is the natural replacement, at an estimated 2.3× at `D = 3`.
- **Out of scope here, per #1156:** GF(31) and larger fields, `GF(2^8)`, record-size campaigns, and
  any default change. `n ≤ 64` is a representation limit (`u64` points).
- **Preprocessing is dense.** The Macaulay matrix is a packed dense `BitMatrix`. At `D = 4` and
  `n ≈ 40` it reaches gigabytes, and the budget (`matrix_budget_bytes`, 1 GiB by default) refuses it
  with `MatrixTooLarge`. 2026/360's block Lanczos cokernel is the scalable route and is not built.

## 7. Reproduce

```sh
cargo test --release --lib gf2_points
cargo run --release --example gf2_points -- --n 28 --m 56 --seed 1 --method crossbred --kept 13 --degree 3
cargo run --release --example gf2_points -- --n 30 --m 20 --seed 1 --all
```
