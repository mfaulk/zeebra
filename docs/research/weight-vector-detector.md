# Weight vectors: inputs that already are a basis, and weighted grading (#1192, laptop stage)

**Measured at:** `1b0bab73` (branch `research/1192-weight-detector`, on `b364f557`),
`examples/weight_detector_study.rs` in release, `lto=thin`, `codegen-units=16`, one process, on a
macOS M4 Pro laptop, **unpinned, development only**. Every figure in §§3–5 is a count and does
not depend on the machine. The one wall ratio (§6) is an indication, not a deciding measurement.
**Status:** laptop stage complete, 2026-11-27. The wall columns are left for the bench host (§8).

Data, the driver's output and the table generator:
[`research/1192-weight-detector/`](../../research/1192-weight-detector/README.md).

## Summary

- **Audit.** Conventional F4 runs under `MonomialOrder::Weighted`, but its pair selection is the
  normal strategy by **total** degree, not weighted degree. The signature engine refuses every
  non-graded order. FGLM accepts a weighted source and converts only to lex. So Zeebra has
  weighted *orders*, not weighted-homogeneous F4 in the sense of Faugère, Safey El Din and Verron
  (§1).
- **Detector.** `grobner::weight_detector::detect_free_basis` is built and opt-in. It looks for
  positive weights and one leading monomial per generator, pairwise coprime, and re-checks every
  hit against the polynomials. On the 62-problem public panel it hits **4 rows**. All 4 are
  positive-dimensional, and grevlex F4 on them is already small (largest matrix 414 × 795)
  (§3).
- **Cost.** 43 of 62 rows are rejected before any linear program: 6 by pigeonhole, 37 by a
  combinatorial screen. The other 19 run 12–147 LPs. On the laptop, that search costs more than
  1% of the grevlex solve on 15 of the 18 rows that could be priced, and up to 17× the solve. It
  **fails #1036's 1% bar** as an always-on pre-pass (§6).
- **Weighted grading.** Three ellipsoid rows are weighted-homogeneous under `(2, 1, …, 1)`. Under
  that order, F4's largest matrix shrinks from 135 × 234 to 87 × 204 and from 307 × 561 to
  96 × 270. On `sd-ellipsoid-m2`, the default limits refuse the grevlex run, and the weighted run
  completes at 121 × 254. These ideals are positive-dimensional, and Zeebra has no conversion from
  a weighted basis to grevlex, so the gain is only usable by a caller that accepts a weighted basis
  (§4).
- **Recommendation: stop record for default routing.** The detector and the weighted-homogeneity
  search stay opt-in tools. Two follow-ups are worth filing (§7).

## 1. Audit: which engines honour `MonomialOrder::Weighted`

| Engine | Under `Weighted` | Where |
|---|---|---|
| Conventional F4 (`f4`, `f4_with_options`, `f4_reported`) | Runs. Every comparison uses the weighted order. **Pair selection is by the total degree of the lcm** (`CriticalPair::degree = lcm.degree()`), so batches are total-degree slices, not weighted-degree slices | `src/grobner/pairs.rs` (`CriticalPair::from_leads`), `src/grobner/f4/mod.rs` |
| `F4Options::graded_engine = Adaptive` | Ignored: lex, `Weighted` and `Block` always run conventional F4 | `src/grobner/f4/options.rs` (`GradedEngine` docs) |
| Signature engine (`f4_signature`, `signature_route`) | Refused, `SigF4Error::Unsupported`: "the signature engine supports graded orders only" | `src/grobner/sigf4/engine.rs` (`graded`), `src/grobner/sigf4/dispatch.rs` |
| Buchberger | Runs, tested end to end against the definition and the quotient dimension | `src/grobner/buchberger.rs` (`test_a_weighted_order_drives_the_engine`) |
| FGLM | Weighted **source** accepted. Target is lex only, so a weighted basis cannot be converted to grevlex. A positive-dimensional ideal cannot be converted at all | `src/grobner/fglm/conversion.rs` |
| External comparands | Refused explicitly, never approximated | `src/grobner/external/contract.rs` |

Termination and correctness under total-degree selection are not in question. Any selection
strategy is correct, and the weighted tests confirm that. What is missing is the *grading*: under
a weighted order, the degree-`d` batch mixes several weighted degrees. The complexity statements
of the weighted-homogeneous literature assume a batch per weighted degree. A weighted-degree pair
key would be the engine change. It touches `pairs.rs` and the F4 loop, both M35-owned, so it is
not made here.

## 2. The detector

`detect_free_basis(system, tie_break, &DetectorLimits)` returns a `FreeBasis { weights, order,
leading }` or a named `DetectionMiss`, together with its work counters. The stages are:

1. **Pigeonhole.** Pairwise-coprime non-constant monomials need pairwise-disjoint, non-empty
   supports, so more generators than variables is a miss with no search.
2. **Graded fast path.** If the leading monomials under the all-ones order with this tie-break
   are already coprime, the input is returned as it is.
3. **Screen.** A monomial that divides another of its generator's monomials never leads under
   positive weights. The screen searches for a choice of one divisibility-maximal monomial per
   generator with disjoint supports. It uses no LP and is capped at 4096 nodes. If no such choice
   exists, the row is a miss.
4. **LP search.** Each generator keeps up to 4 candidate leading monomials for which some
   positive weight makes the candidate strictly the largest, fewest variables first. A depth-first
   search over coprime assignments solves the accumulated strict inequalities
   `w·(m_i − m') ≥ 1, w ≥ 1` at each node. The solver is an exact two-phase simplex over checked
   `i128` rationals with Bland's rule, minimising `Σ w`. A run solves at most 256 LPs.
5. **Certificate.** The weights are rebuilt into a `MonomialOrder::weighted`. Each generator's
   leading monomial under that order must be the chosen one, and the leading monomials must be
   pairwise coprime (`leading_monomials_are_pairwise_coprime`). Only then is the hit returned.
   Because the inequalities are strict, the tie-break never decides a leading monomial.

A miss means *not found within the limits*. The bounded candidate list makes the search
incomplete by design. `weighted_homogeneous_weights` solves the corresponding equalities
`w·(m − m₀) = 0` and returns the least positive grading, if one exists.

Correctness tests (`src/grobner/weight_detector/`):

- The LP is checked against brute force on 300 random constraint sets.
- On 400 random systems, every hit is checked to be a Gröbner basis by Buchberger's criterion
  (`is_grobner_basis`), and the reported leading monomials are checked to match the order.
- Fixed cases cover each miss reason, the budget, the fast path, and a system that is a basis only
  under unequal weights (`y² − x³, x² + y`).

## 3. Hit rate on the public panel

These are the 62 base problems of the #1006 panel at `p31`
(`research/m34-public-corpus/catalog.json`), under the reverse-lexicographic tie-break.

| Stage that decided the row | Rows | Hits | LPs solved |
|---|---:|---:|---:|
| Pigeonhole (more generators than variables) | 6 | 0 | 0 |
| Screen (no coprime choice of maximal monomials) | 37 | 0 | 0 |
| Graded fast path | 0 | 0 | 0 |
| LP search | 19 | 4 | 866 |
| **Total** | **62** | **4** | |

The four hits are `sd-robot-romin` (12 variables, 7 equations), `sd-raksanyi` (8, 4),
`sd-heron` (7, 4) and `sd-geometry-heron-1` (6, 3). Every one has fewer equations than variables.
No zero-dimensional panel row is a free basis under any weight vector the search reaches. The 15
LP-stage misses are Chandrasekhar-H 4–13, Schwarz 7/9/11, Virasoro and Czapor-86a. Per-row work
is in [`tables.md`](../../research/1192-weight-detector/tables.md) §2.

**#1189's AO rows do not exist yet.** That issue is open, and its owner decision on which
arithmetization-oriented systems are public is still pending. The textbook stand-in below is a
MiMC-style power map, `(x_i + c_i)³ − x_{i+1}` (§5). It is a hit on the **graded fast path**:
the cubes lead under grevlex and are already coprime. Conventional F4 on it already builds
**zero** matrices, because the pair criteria discard every pair. On that structure the detector
saves F4 nothing it does not already skip.

## 4. Weighted grading against grevlex on the panel

This is conventional F4 with shipping options, under grevlex and under each weight vector the row
has. The weighted tie-break is reverse-lexicographic. "Top pair degree" is the largest total
degree of a selected lcm.

| Row | Weights (source) | grevlex batches | grevlex top pair degree | grevlex largest | weighted batches | weighted top pair degree | weighted largest |
|---|---|---:|---:|---|---:|---:|---|
| sd-ellipsoid-2 | 2 1 … 1 (homogeneous) | 4 | 9 | 135 × 234 | 7 | 11 | 87 × 204 |
| sd-ellipsoid-4 | 2 1 … 1 (homogeneous) | 5 | 17 | 307 × 561 | 10 | 21 | 96 × 270 |
| sd-ellipsoid-m2 | 2 1 … 1 (homogeneous) | — | — | refused, `TooManyColumns` (limit 200,000) | 4 | 11 | 121 × 254 |
| sd-heron | 1 1 1 2 1 1 1 (homogeneous) | 6 | 7 | 17 × 23 | 4 | 5 | 17 × 23 |
| sd-geometry-heron-1 | 1 1 1 1 1 2 (homogeneous) | 1 | 2 | 2 × 6 | 1 | 2 | 2 × 6 |
| sd-robot-romin | detector | 7 | 6 | 414 × 795 | 0 | — | — |
| sd-raksanyi | detector | 5 | 5 | 12 × 54 | 0 | — | — |
| sd-heron | detector | 6 | 7 | 17 × 23 | 0 | — | — |
| sd-geometry-heron-1 | detector | 1 | 2 | 2 × 6 | 0 | — | — |

On the ellipsoid rows, the weighted-homogeneous order reaches a higher total degree but builds
matrices with fewer rows. Peak live nonzeros fall from 521 to 415 and from 1214 to 545. One row
that grevlex refuses at the default column limit completes. Under total-degree selection, that is
the order acting on its own. A weighted-degree batch key (§1) would be the next experiment.

**Conversion is not charged, because it does not exist.** All of these ideals are
positive-dimensional. FGLM does not apply, and Zeebra has no Gröbner walk, so a weighted basis
cannot be turned into the grevlex basis the task asks for. The ellipsoid result is usable only for
work that accepts a weighted basis, such as ideal membership, dimension, or the Hilbert function
of the weighted-homogeneous ideal.

## 5. Families: F4 removed, conversion to lex charged

There are two parameterised families (`examples/weight_detector_study.rs`):

- **`chain-d<d>-n<n>`** is synthetic: `x_i^d + x_{i+1}^{d+1} + x_i x_{i+1} + c_i`, closed by
  `x_{n−1}^d + x_0 + 1`. Its grevlex leading monomials share a variable, and the detector finds a
  weight vector that reorients one link.
- **`power-map-<r>`** is the MiMC-style chain from §3.

Every row is zero-dimensional. The requested order is taken to be lex, because FGLM converts only
to lex, so conversion is charged as FGLM from each source basis. The driver asserts that both
routes return the same lex basis.

| Row | Weights | grevlex F4 batches | grevlex largest | grevlex peak nonzeros | weighted F4 batches | `D` | FGLM operator entries, grevlex / weighted |
|---|---|---:|---|---:|---:|---:|---|
| chain-d3-n4 | 175 127 91 64 | 10 | 195 × 270 | 2,760 | 0 | 81 | 3,898 / 2,389 |
| chain-d3-n5 | 781 589 445 337 256 | 13 | 953 × 1185 | 43,926 | 0 | 256 | 49,301 / 31,451 |
| chain-d4-n5 | 2101 1601 1201 881 625 | 16 | 2504 × 3522 | 66,787 | 0 | 1024 | 216,596 / 49,656 |
| chain-d2-n3 | 19 13 9 | 4 | 17 × 23 | 114 | 0 | 9 | 94 / 90 |
| chain-d3-n3, d4-n3, d4-n4, d5-n3, d5-n4 | — | 2–3 | ≤ 2 × 10 | ≤ 13 | 0 | 27–625 | equal |
| power-map-3 … 6 | 1 … 1 (graded) | 0 | — | 0 | 0 | 27–729 | equal |

Every chain row is a hit. On the three rows where grevlex F4 builds non-trivial matrices
(`chain-d3-n4`, `d3-n5` and `d4-n5`), the weighted source removes F4 entirely. It also shrinks the
FGLM operators by 1.6–4.4×. Normal-form calls move by at most 43%, from 358 to 512 on
`chain-d3-n5` (`tables.md` §4). This is the FreeLunch effect on a family built to show it. On the
public panel it does not occur (§3).

## 6. Cost against the solve it replaces

#1036's bar is that detection on rows it does not help must stay under 1% of the solve.

- **Pigeonhole rows (6):** a scan for zero and constant generators, then one comparison. Laptop
  detection was at most 0.01 ms.
- **Screen rows (37):** between 1 and 63 screen nodes and no LP. Laptop detection was at most
  0.26 ms. These rows were not priced against their solves; that is for the bench host.
- **LP-search rows (19):** 12–147 LPs and 59–5,030 pivots. Against the laptop grevlex F4 wall,
  in the same process with the same build, detection exceeds 1% on 15 of the 18 priced rows. It
  ranges from 216% on Schwarz-7 and 685% on Czapor-86a down to 0.06% on Chandrasekhar-H-12, and
  it is 1735% on the raksanyi hit, whose solve is 0.1 ms. Grevlex F4 refused Chandrasekhar-H-13,
  so that row has no ratio. (Unpinned laptop walls: the order of magnitude, not the exact
  figure, is the finding.)

The LP search's cost is dominated by the per-candidate feasibility LPs, one per kept candidate.
It falls under 1% only where the solve is already hundreds of milliseconds. A routed detector
would need its LP stage gated on a solve-size estimate, and on the panel that gate would admit
rows on which the detector never hits.

## 7. Recommendation, and what it would take to reverse it

**Stop record for default routing.** The detector is correct, and it is cheap where it rejects
early (43 of 62 rows). But it hits only on positive-dimensional panel rows where F4 is already
trivial, and its LP stage costs more than the solve on small rows. No default dispatch changes.
The detector and `weighted_homogeneous_weights` stay opt-in.

Worth filing:

1. **Weighted-degree pair selection in conventional F4.** Key `CriticalPair` on the weighted
   degree under a `Weighted` order, then re-measure the ellipsoid rows and the chain family. This
   touches `pairs.rs` and the F4 loop, so it is M35-owned.
2. **Re-run on #1189's AO rows** once that panel is declared. The detector's case rests on
   structured inputs, FreeLunch-style, that the public panel does not contain.

Reverse the stop if the AO rows give zero-dimensional hits on which grevlex F4 is
non-trivial, and the detection cost on that panel's misses is under 1% on the bench host.

## 8. Left for the bench host

- One-worker wall for every row of §4 and §5, grevlex against weighted. For §5, the FGLM wall from
  each source is charged as well.
- Detection wall against the grevlex solve on all 62 rows, including the 37 screen rows that are
  unpriced here, to settle §6's bar under the pinned protocol.

Reproduce:

```sh
export CARGO_TARGET_DIR=...  RUSTC_WRAPPER=""   # see CLAUDE.md
cargo build --release --example weight_detector_study
B=$CARGO_TARGET_DIR/release/examples/weight_detector_study
$B --panel research/m34-public-corpus/catalog.json --solve > research/1192-weight-detector/panel.jsonl
$B --families > research/1192-weight-detector/families.jsonl
python3 research/1192-weight-detector/tables.py > research/1192-weight-detector/tables.md
```
