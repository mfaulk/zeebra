# The Wiedemann route builds only the last operator (#1233, laptop stage)

**Measured at:** after arm `ff3d1d7d` (branch `perf/1233-wiedemann-last-operator`, tag
`measured/1233-wiedemann-last-operator`), before arm `ffe8787e` (`main` at the branch point). Two
binaries of `examples/lex_pipeline.rs`, built from two trees.

**Machine and profile:** M4 Pro laptop (macOS, arm64), release with
`CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16`, not the repository's
fat-LTO profile. Unpinned (macOS has no `taskset`), no RSS. Three repetitions per cell, with before
and after alternating within each cell. These figures are a laptop A/B inside one profile. They are
not publication figures, and they do not re-derive the `DenseOperator` rule. Both are left for the
bench host (§4).

## 1. What changed

`QuotientAlgebra::new` builds all `N` multiplication operators. The certified Wiedemann conversion
reads one of them: `reconstruct` applies `T_{N-1}`, and the other variables enter only through the
class of `x_i`. In #1039's publication medians the operator stage was 59% of the Wiedemann arm on
`katsura-11` and 33% on `pquad-10-1`.

- **Partial construction.** A conversion whose strategy may use Wiedemann (`Adaptive`, `Wiedemann`)
  builds `T_{N-1}` alone. The other operators are built only if the route falls back to the
  classical walk, and the border normal forms already computed are reused
  (`QuotientAlgebra::complete_controlled`). The fallback check against the dimension cap still
  runs before completion. A quotient above the cap therefore never pays for the other operators.
- **Read-off.** On the partial path, a border monomial that is the leading monomial of a source
  element `g` with a standard tail is not reduced. Its column is `-tail(g) / lc(g)`, which is
  exactly what normal form returns, because a normal form modulo a Gröbner basis is unique. On a
  stable grevlex staircase (Berthomieu–Neiger–Safey El Din, ISSAC 2022, Cor. 5.4) every border
  column of the last operator is of this kind. Katsura and the planted dense quadratics below need
  **zero** normal forms for it. The full construction does not read off, so its three strategies
  still differ only in how they reduce.
- **Variable classes.** The class of `x_i` for a deferred operator is a unit vector when `x_i` is
  standard, and is read off the element whose leading monomial is `x_i` otherwise. The first cut
  called the general `normal_form` here. Each call prepares a reducer over the whole basis, about
  45 ms on `katsura-11`, and there are `2(N−1)` calls per attempt. That cost more than the deferred
  operators saved: the conversion ran at 0.70× on `katsura-11`. The profile found it, and the fix
  is in the second commit.
- **Shared preparation.** The batched strategy's `MonicBasis` and the read-off index are prepared
  once per algebra and kept across a completion. When they were prepared once per stage, the
  `DenseOperator` fallback rows paid about 30 ms twice and ran at 0.89–0.94×.

New counters: `FglmStatistics::operators_built` and `BorderStatistics::read_off_columns`. The
operator figures in `FglmStatistics` describe the operators that were built, so a Wiedemann
conversion reports one operator's entries.

**Budgets.** The operator budgets are checked against what is built. A Wiedemann conversion can
therefore succeed inside an operator budget that the full algebra would exceed. A fallback checks
the budgets against all `N` operators, as before.

## 2. Tests

- `quotient_algebra::test_a_partial_construction_completes_to_the_full_algebra`: for every
  construction strategy and every variable, the partial operator equals the full construction's,
  every variable class matches, and completion yields an algebra equal to the full one. Covers six
  two-variable systems under lex, grlex and grevlex, plus Katsura-5, Cyclic-5 and planted-4 under
  grevlex.
- `quotient_algebra::test_the_last_operator_of_a_stable_staircase_is_read_off`: Katsura-6's last
  operator needs no normal form under any strategy.
- `conversion::test_the_wiedemann_route_builds_only_the_last_operator`: the Wiedemann route builds
  one operator and returns the classical basis. The adaptive route on a small quotient completes to
  `N` operators, with the classical walk's entries and row operations.
- `control::test_cancellation_before_the_fallback_prevents_it` now stops at `OperatorConstruction`,
  the fallback's first safe point, and not at `ClassicalWalk`. The walk still never starts.

## 3. Measurement

`lex_pipeline --family ROW --arm ARM --modulus 65537`, one worker. "Operator" is
`FglmStageTimings::operator_construction`, summed over both stages on a fallback. "Conversion" is
the whole `fglm_to_lex_with_options` call. Before ÷ after is the ratio of medians, with the range
of the per-repetition ratios in brackets. Every cell's `m33-basis-v1` lex digest is identical
before and after.

| Row | D | Arm | Route (fallback) | Operators built | Normal forms / read off | Operator ms before → after | Conversion ms before → after | Before ÷ after |
|---|---:|---|---|---:|---:|---:|---:|---:|
| `katsura-9` | 256 | adaptive | Classical (DenseOperator) | 9 | 931 / 143 | 6.8 → 7.4 | 18.6 → 18.9 | 0.99 [0.87, 1.02] |
| `katsura-9` | 256 | wiedemann | Wiedemann | 1 | 0 / 86 | 6.0 → 0.8 | 25.0 → 20.1 | 1.24 [1.22, 1.26] |
| `katsura-9` | 256 | classical | Classical | 9 | 1,074 / 0 | 6.4 → 5.9 | 18.2 → 17.9 | 1.02 [1.00, 1.02] |
| `katsura-10` | 512 | adaptive | Classical (DenseOperator) | 10 | 2,055 / 272 | 32.8 → 33.0 | 112.6 → 111.4 | 1.01 [0.98, 1.01] |
| `katsura-10` | 512 | wiedemann | Wiedemann | 1 | 0 / 171 | 30.1 → 2.7 | 169.0 → 143.2 | 1.18 [1.18, 1.21] |
| `katsura-10` | 512 | classical | Classical | 10 | 2,327 / 0 | 32.4 → 30.9 | 111.3 → 110.3 | 1.01 [0.98, 1.02] |
| `katsura-11` | 1,024 | adaptive | Classical (DenseOperator) | 11 | 4,471 / 537 | 223.1 → 225.3 | 798.0 → 802.6 | 0.99 [0.99, 1.00] |
| `katsura-11` | 1,024 | wiedemann | Wiedemann | 1 | 0 / 342 | 220.9 → 11.2 | 1,274.8 → 1,053.5 | 1.21 [1.18, 1.21] |
| `katsura-11` | 1,024 | classical | Classical | 11 | 5,008 / 0 | 230.0 → 226.5 | 808.9 → 806.8 | 1.00 [0.97, 1.01] |
| `pquad-10-1` | 1,024 | adaptive | Wiedemann | 1 | 0 / 252 | 66.7 → 8.3 | 915.1 → 854.8 | 1.07 [1.06, 1.07] |
| `pquad-10-1` | 1,024 | wiedemann | Wiedemann | 1 | 0 / 252 | 71.2 → 8.3 | 918.9 → 852.6 | 1.08 [1.07, 1.08] |
| `pquad-10-1` | 1,024 | classical | Classical | 10 | 3,271 / 0 | 71.2 → 67.5 | 595.9 → 591.0 | 1.01 [1.00, 1.01] |
| `pquad-11-1` | 2,048 | adaptive | Wiedemann | 1 | 0 / 462 | 409.0 → 32.0 | 6,509.4 → 6,114.9 | 1.06 [1.06, 1.07] |
| `pquad-11-1` | 2,048 | wiedemann | Wiedemann | 1 | 0 / 462 | 404.7 → 32.3 | 6,487.4 → 6,062.3 | 1.07 [1.07, 1.07] |
| `pquad-11-1` | 2,048 | classical | Classical | 11 | 6,995 / 0 | 409.2 → 407.4 | 4,255.4 → 4,240.9 | 1.00 [1.00, 1.00] |

On the Wiedemann route the operator stage falls by 7–20×, and the conversion gains 1.06–1.24×. The
`DenseOperator` fallback rows and the classical arm are at parity, 0.99–1.02×.

## 4. What the laptop does not settle

- **The gate and the `DenseOperator` rule (work items 4–5).** On this machine the classical walk
  beats the Wiedemann arm on every row above, both before and after the change: `katsura-11`
  runs 807 ms classical against 1,054 ms Wiedemann, and `pquad-10-1` 591 against 853. The bench
  host ranked these the other way in #1039: `pquad-10-1` ran 2,080 ms on Wiedemann, and
  `katsura-11`'s classical default ran 3,357 ms. Removing the operator stage moves the Wiedemann
  arm by the same absolute amount on either machine. The ratio between the two routes is a
  property of the machine, though, so `D² / 4` has to be re-derived from pinned fat-LTO runs on
  the bench host, not from these figures. The rule is unchanged here.
- **The prediction in #1233** (about 1,554 ms for `katsura-11`'s Wiedemann arm without operators,
  against 1,213 ms for grobx) is a bench-host quantity. It needs the same pinned panel, and the
  chain rows are its no-regression control.
- **Non-stable staircases.** Every row measured here is stable, so the last operator was read off
  entirely. On a non-stable row the border monomials that are not leading monomials are reduced
  as before. The differential test asserts operator equality on every row it builds, but no
  figure here times a row where the read-off is partial.
