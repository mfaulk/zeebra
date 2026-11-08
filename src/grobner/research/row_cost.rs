//! What one resultant-elimination row is predicted to cost, term by term, before anything is run.
//!
//! # Why this is a row and not a stage
//!
//! The budget guard in `examples/resultant_cico` costed exactly one term — the Sylvester
//! determinants — and that was defensible while determinants were ~99% of a four-round row
//! (`docs/research/resultant-elimination.md` line 139). #350 and #351 inverted the composition:
//! on `rf4-rp2` the symbolic build is 73% of the row and the determinants 15%, and on `rf6-rp0`
//! root finding is 78% after axis 4. A guard that admits a row by modelling the term that stopped
//! being dominant is a guard waiting to pass something it should refuse (#410).
//!
//! So every term carries its own [`TermBasis`], the row total is a **band** rather than a point,
//! and [`ResultantRowCost::verdict`] refuses on the pessimistic edge. A row with a term nobody has
//! measured at its size is [`RowVerdict::Unbounded`] rather than admitted: an unmodelled term is
//! not a zero term.
//!
//! # Where the anchors come from
//!
//! Every constant here is a recorded measurement with a document reference, and every law is
//! either derived or fitted over a stated range. The laws that interpolate between measurements go
//! through [`from_anchors`], whose tables are **monotone upper envelopes** — the running maximum of
//! every measurement at or below a degree — so no law can return less than something already
//! measured. That matters because the anchors come from different polynomial families: a real
//! `rf4-rp0` resultant takes 3.93 s to crack where a planted degree-8 192 polynomial takes 3.16 s,
//! and a law fitted through the planted sweep alone would under-predict the real row.

use super::{predicted_resultant_degree, DeterminantKernel, PoseidonParameters};

/// How well a term of the row cost is known at **this row's size**.
///
/// The distinction [`Self::Fitted`] / [`Self::Extrapolated`] is the one
/// `research::cost_model::FigureBasis` draws for recorded figures and for the same reason: nothing
/// bounds a law's error outside the range it was fitted over, so a prediction past the evidence
/// must not read like one inside it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TermBasis {
    /// An instrument read this term off a run at this row's own size.
    Measured,
    /// A law evaluated inside the range its anchors cover.
    Fitted,
    /// A law evaluated past its largest anchor, or held flat below its smallest.
    Extrapolated,
    /// No measurement and no law reaches this size. The term's seconds are **not** a figure.
    Unmeasured,
}

impl TermBasis {
    /// The word a printed cost line uses for this basis.
    pub fn label(&self) -> &'static str {
        match self {
            Self::Measured => "measured",
            Self::Fitted => "fitted",
            Self::Extrapolated => "extrapolated",
            Self::Unmeasured => "NOT MODELLED",
        }
    }

    /// Whether this basis carries a usable number at all.
    pub fn is_modelled(&self) -> bool {
        !matches!(self, Self::Unmeasured)
    }
}

/// One term of a row's predicted wall clock.
#[derive(Clone, Copy, Debug)]
pub struct CostTerm {
    /// The stage, as the printed table names it.
    pub stage: &'static str,
    /// Predicted wall clock, seconds. Zero and meaningless when the basis is
    /// [`TermBasis::Unmeasured`].
    pub seconds: f64,
    /// How well this term is known at this size.
    pub basis: TermBasis,
    /// The anchor or law behind the number, for the printed line.
    pub anchor: &'static str,
}

impl CostTerm {
    /// Seconds this term contributes to a budget decision: zero when there is no figure.
    ///
    /// An unmodelled term contributing zero is sound only because [`ResultantRowCost::verdict`]
    /// refuses a row that has one, rather than totalling around it.
    fn contribution(&self) -> f64 {
        if self.basis.is_modelled() {
            self.seconds
        } else {
            0.0
        }
    }
}

/// What the guard decided about a row, and on what arithmetic.
#[derive(Clone, Debug, PartialEq)]
pub enum RowVerdict {
    /// Every term is modelled and the pessimistic row total is inside the budget.
    Admit,
    /// The pessimistic row total exceeds the budget. Sound even with unmodelled terms, since those
    /// can only add.
    OverBudget {
        /// The pessimistic edge of the row band, seconds.
        pessimistic_seconds: f64,
    },
    /// A term of this row has no figure at this size, so the row cannot be bounded at all.
    Unbounded {
        /// The stages with no figure.
        stages: Vec<&'static str>,
    },
}

/// Every predicted term of one resultant-elimination row, with the band the root finder puts on it.
#[derive(Clone, Debug)]
pub struct ResultantRowCost {
    /// `R_F + R_P`.
    pub rounds: usize,
    /// The S-box exponent.
    pub alpha: u32,
    /// Full rounds.
    pub r_f: usize,
    /// Partial rounds.
    pub r_p: usize,
    /// `alpha^(2 R_F + R_P)`, the experimental degree, which is the resultant's degree when the
    /// off-domain check accepts it.
    pub predicted_degree: usize,
    /// Samples the prediction needs: `predicted_degree + 1`.
    pub samples: usize,
    /// Samples the proven `2d²` bound needs.
    pub proven_samples: usize,
    /// Order of the Sylvester matrix, `2 · 3^rounds`.
    pub matrix_order: usize,
    /// The kernel the row will be run with, which must be the kernel it was costed with.
    pub kernel: DeterminantKernel,
    /// The worker count the row will be run at.
    pub workers: usize,
    /// `cico_bivariate`: the two bivariate polynomials, built symbolically.
    pub build: CostTerm,
    /// The determinants at the predicted sample count — the only term the pre-#410 guard costed.
    pub determinants: CostTerm,
    /// Recovering the resultant from its evaluation table.
    pub interpolation: CostTerm,
    /// The eight off-domain determinants that decide whether the predicted degree held.
    pub validation: CostTerm,
    /// Root finding by the gcd route, which is the **pessimistic** edge of the band.
    pub root_finding_pessimistic: CostTerm,
    /// Root finding by deflation, which is the **optimistic** edge.
    pub root_finding_optimistic: CostTerm,
    /// The determinant term at the proven `2d²` sample count, for the fallback's affordability.
    pub proven_determinant_seconds: f64,
}

impl ResultantRowCost {
    /// Cost a row from its Poseidon parameters, at `workers` determinant workers.
    ///
    /// # Panics
    /// When the predicted degree overflows a `usize`, which is a row nothing here could cost.
    pub fn of(parameters: &PoseidonParameters, kernel: DeterminantKernel, workers: usize) -> Self {
        let rounds = parameters.rounds();
        let degree = 3usize.pow(rounds as u32);
        let predicted_degree =
            predicted_resultant_degree(parameters.alpha, parameters.r_f, parameters.r_p)
                .expect("the predicted degree fits a usize");
        let matrix_order = 2 * degree;
        let samples = predicted_degree + 1;
        let proven_samples = 2 * degree * degree + 1;

        // Core-time per determinant, divided by the workers that share it. `kernel_core_ms`
        // carries both the cost law and the measured penalty for running wide.
        let each = kernel_core_ms(kernel, matrix_order, workers) / 1e3 / workers.max(1) as f64;

        Self {
            rounds,
            alpha: parameters.alpha,
            r_f: parameters.r_f,
            r_p: parameters.r_p,
            predicted_degree,
            samples,
            proven_samples,
            matrix_order,
            kernel,
            workers,
            build: build_term(rounds),
            determinants: CostTerm {
                stage: "symbolic determinants",
                seconds: samples as f64 * each,
                basis: determinant_basis(kernel, matrix_order),
                anchor: determinant_anchor(kernel),
            },
            interpolation: interpolation_term(samples),
            validation: validation_term(matrix_order, workers),
            root_finding_pessimistic: gcd_root_term(predicted_degree),
            root_finding_optimistic: deflation_root_term(predicted_degree),
            proven_determinant_seconds: proven_samples as f64 * each,
        }
    }

    /// The five terms of the row, with root finding at its pessimistic edge.
    pub fn terms(&self) -> [CostTerm; 5] {
        [
            self.build,
            self.determinants,
            self.interpolation,
            self.validation,
            self.root_finding_pessimistic,
        ]
    }

    /// What the pre-#410 guard costed: the determinants, and nothing else.
    ///
    /// Kept because the printed line quotes it against the row total, which is the only way a
    /// reader can see how much of a row a determinant budget ever covered.
    pub fn determinant_seconds(&self) -> f64 {
        self.determinants.seconds
    }

    /// The row's pessimistic edge: every modelled term, root finding by the gcd route.
    pub fn pessimistic_seconds(&self) -> f64 {
        self.terms().iter().map(CostTerm::contribution).sum()
    }

    /// The row's optimistic edge: every modelled term, root finding by deflation.
    ///
    /// Deflation's cost is `(roots + 1)` searches, so this edge assumes the `O(1)` base-field root
    /// count measured on the three registered rows that have one. It is an edge of a band and not
    /// a prediction.
    pub fn optimistic_seconds(&self) -> f64 {
        self.pessimistic_seconds() - self.root_finding_pessimistic.contribution()
            + self.root_finding_optimistic.contribution()
    }

    /// The stages this row has no figure for.
    pub fn unmodelled(&self) -> Vec<&'static str> {
        self.terms()
            .iter()
            .filter(|t| !t.basis.is_modelled())
            .map(|t| t.stage)
            .collect()
    }

    /// The share of the pessimistic row the determinant term alone accounts for.
    pub fn determinant_share(&self) -> f64 {
        let row = self.pessimistic_seconds();
        if row > 0.0 {
            self.determinants.seconds / row
        } else {
            1.0
        }
    }

    /// Whether `wall_budget_seconds` admits this row.
    ///
    /// Refuses on the **pessimistic** edge, because the band's width is set by the eliminant's
    /// base-field root count and that is a property of the problem — unmeasured on exactly the
    /// rows that have not been attempted. Over-budget is checked before unbounded: a pessimistic
    /// total already past the budget refuses the row whatever the unmodelled terms turn out to be.
    pub fn verdict(&self, wall_budget_seconds: f64) -> RowVerdict {
        let pessimistic = self.pessimistic_seconds();
        if pessimistic > wall_budget_seconds {
            return RowVerdict::OverBudget {
                pessimistic_seconds: pessimistic,
            };
        }
        let stages = self.unmodelled();
        if !stages.is_empty() {
            return RowVerdict::Unbounded { stages };
        }
        RowVerdict::Admit
    }
}

// ---------------------------------------------------------------------------------------------
// The terms
// ---------------------------------------------------------------------------------------------

/// `cico_bivariate`'s measured wall clock by round count, seconds.
///
/// A **recorded constant rather than a model**: the build's cost is set by the round count alone,
/// because every row at a given round count shares the same word degrees — `resultant-elimination.md` §6.1
/// measures 419.3 ms
/// and 397.7 ms for the two four-round rows, and `MILESTONE-COMPETITIVE-ALGEBRA.md` §8.4.2's
/// 5.4 min six-round figure is "identical for every six-round row".
///
/// The larger figure is taken where a round count has two, which is why the four-round entry is
/// 419.3 ms: #243's collecting multiply made that build **50.8–52.5 ms** in #410's own lock run, so
/// the recorded §6.1 constant is now conservative by ~8x. It is kept rather than lowered for the
/// reason [`determinant_core_ms`] takes the larger of two laws — a guard that under-predicts
/// authorizes a run nobody costed — and lowering it would also pair a post-#243 build figure with a
/// pre-#243 one at a different round count.
///
/// Round counts with no measurement return `None` rather than an extrapolation: the build's growth
/// per two rounds is 145x then 772x, which no law covers, and at seven rounds
/// `structured-sylvester.md` §7.3 predicts a ~1 TB
/// transient from a mechanism that predicted the six-round peak to 0.7%. A number invented for
/// those rows would be the one thing a guard must not do.
fn measured_build_seconds(rounds: usize) -> Option<f64> {
    match rounds {
        2 => Some(0.0029),
        4 => Some(0.4193),
        6 => Some(324.0),
        _ => None,
    }
}

/// The symbolic build term.
fn build_term(rounds: usize) -> CostTerm {
    match measured_build_seconds(rounds) {
        Some(seconds) => CostTerm {
            stage: "symbolic build",
            seconds,
            basis: TermBasis::Measured,
            anchor: "recorded constant per round count, resultant-elimination.md 6.1: 2.9 ms at \
                     R=2, 419.3 ms at R=4, 324.0 s at R=6 (MILESTONE-COMPETITIVE-ALGEBRA.md \
                     8.4.2, on-lock, post-#243)",
        },
        None => CostTerm {
            stage: "symbolic build",
            seconds: 0.0,
            basis: TermBasis::Unmeasured,
            anchor: "no build measured at this round count; structured-sylvester.md 7.3 \
                 predicts ~1 TB of transient at R=7",
        },
    }
}

/// Lagrange interpolation of the resultant from `samples` evaluations, **measured** anchors.
///
/// Two measurements of the predicted-count Lagrange route, which is the one the example takes:
/// **5.1 ms at 730 samples** (`resultant-elimination.md` §6.7) and **31.7 s at 59 050** (#367's
/// authorized `rf4-rp2` run).
/// Their implied exponent is **1.99**, which confirms the `O(S²)` the quadratic
/// `lagrange_interpolate` derives, so that is the exponent used above the larger anchor.
///
/// This term was an extrapolation in the pre-#410 guard's documentation (0.01 h for `rf4-rp2`,
/// 0.75 h for `rf6-rp0`). It is not an extrapolation inside `[730, 59 050]` any more; the figure
/// `rf4-rp2` was costed at came out 12% high against the run.
fn interpolation_term(samples: usize) -> CostTerm {
    const ANCHORS: [(f64, f64); 2] = [(730.0, 0.0051), (59_050.0, 31.7)];
    let (seconds, basis) = from_anchors(&ANCHORS, samples as f64, 2.0);
    CostTerm {
        stage: "interpolation",
        seconds,
        basis,
        anchor: "measured 5.1 ms at S=730 (resultant-elimination.md 6.7) and 31.7 s at S=59 050 \
                 (#367); O(S^2) above",
    }
}

/// The off-domain check: eight **dense** direct Sylvester determinants.
///
/// `off_domain_check` calls `sylvester_determinant_at`, which is the dense kernel whatever `--kernel`
/// selects, so this term uses the dense law and not the row's. Eight points share at most eight
/// workers, so the divisor is `min(8, workers)` rather than `workers` — a 32-worker row cannot
/// spread eight determinants over 32 cores. That gives 3.5 s for `rf4-rp2` at 32 workers against
/// the 2.76 s #367 measured, conservative by 1.27x.
fn validation_term(matrix_order: usize, workers: usize) -> CostTerm {
    const CHECKS: usize = 8;
    let sharers = workers.clamp(1, CHECKS);
    let seconds = CHECKS as f64 * determinant_core_ms(matrix_order, workers) / 1e3 / sharers as f64;
    CostTerm {
        stage: "off-domain validation",
        seconds,
        basis: determinant_basis(DeterminantKernel::Dense, matrix_order),
        anchor: "8 dense determinants over min(8, workers), by the dense law",
    }
}

/// Root finding by `roots()` — `gcd(f, x^q − x)` — the band's **pessimistic** edge.
///
/// The anchor table is a monotone upper envelope over three sources: `graeffe-root-finding.md`
/// §9.7.4's nine-point doubling
/// sweep (256–65 536, one session, one binary, local exponent 1.90–1.97), §9.7.2's four points on
/// planted polynomials, and `resultant-elimination.md` §6.1's three **real resultants** from
/// registered rows. The real rows
/// are the slowest at their degrees — 3.93 s at 6 561 against the sweep's 3.16 s at 8 192 — which
/// is why they are in the table and why the table is an envelope rather than a fit: a law through
/// the planted sweep alone under-predicts the row it exists to cost.
///
/// Above 65 536 the exponent is **1.933**, the §9.7.4 fit that superseded the two-point one and
/// survived it on eight points.
///
/// **Every anchor here predates #193**, which dispatched division to Newton inversion and measured
/// `roots` **1.32x–1.67x faster over KoalaBear** at degrees 256–2 048 (`fast-univariate.md` §4.5).
/// This envelope is therefore conservative by about that factor on top of whatever else, which is
/// the safe direction for a pessimistic edge and the wrong direction for a figure anyone quotes.
/// It is **not** scaled down by 1.5x: re-anchoring honestly means re-running §9.7.4's doubling
/// sweep in one session post-#193, which is a measurement rather than an edit — the same reasoning
/// `resultant-elimination.md` §6.13 applies to [`DETERMINANT_MS_AT_162`]. #552.
fn gcd_root_term(degree: usize) -> CostTerm {
    // Monotone envelope: the running maximum, so no entry is below any measurement at or under its
    // degree. 8 192 carries 6 561's real-resultant figure for exactly that reason.
    const ANCHORS: [(f64, f64); 13] = [
        (81.0, 0.0009),
        (256.0, 0.0048),
        (512.0, 0.0163),
        (729.0, 0.0595),
        (1_024.0, 0.0651),
        (2_048.0, 0.2380),
        (4_096.0, 0.8519),
        (6_561.0, 3.9333),
        (8_192.0, 3.9333),
        (16_384.0, 11.7957),
        (32_768.0, 48.6214),
        (59_049.0, 153.2146),
        (65_536.0, 175.5648),
    ];
    let (seconds, basis) = from_anchors(&ANCHORS, degree as f64, 1.933);
    CostTerm {
        stage: "root finding, gcd route (pessimistic)",
        seconds,
        basis,
        anchor:
            "measured envelope over graeffe-root-finding.md 9.7.4's doubling sweep, its 9.7.2, \
                 and resultant-elimination.md 6.1's real resultants; exponent 1.933 above degree \
                 65 536",
    }
}

/// Root finding by deflate-and-repeat over `graeffe_root`, the band's **optimistic** edge.
///
/// `graeffe-root-finding.md` §9.7.2, one pinned core, on the lock. The cost is `(roots + 1)`
/// Graeffe searches, so it is a bet
/// on the **root count** and not on the degree: against a polynomial with `O(d)` base-field roots
/// it would lose to a single gcd pass. Every registered row measured so far came in at `O(1)` roots
/// — 3 at degree 81, 1 at 729, 1 at 59 049 — and this edge assumes that holds. That assumption is
/// the band's width, which is why the guard refuses on the other edge.
///
/// Above 59 049 the exponent is **1.0**: §9.7.1 derives a search near-linear in the degree, and the
/// measured local exponents are 0.68–0.86, so linear is the conservative reading of the evidence.
fn deflation_root_term(degree: usize) -> CostTerm {
    const ANCHORS: [(f64, f64); 4] = [
        (729.0, 0.0117),
        (6_561.0, 0.1133),
        (32_768.0, 0.3022),
        (59_049.0, 0.5001),
    ];
    let (seconds, basis) = from_anchors(&ANCHORS, degree as f64, 1.0);
    CostTerm {
        stage: "root finding, deflation (optimistic)",
        seconds,
        basis,
        anchor:
            "measured 0.0117-0.5001 s over degrees 729-59 049 (graeffe-root-finding.md 9.7.2), at \
             the O(1) root count every registered row has measured; linear above",
    }
}

/// Evaluate a monotone table of measurements at `x`.
///
/// Inside the table, log-log interpolation between the bracketing anchors: it passes exactly
/// through every measurement and never uses an exponent outside the pair it was computed from,
/// which is what stops a small anchor's fixed overhead from being projected forward as a growth
/// rate. Above the table, `exponent` from the largest anchor. Below it, the smallest anchor held
/// flat, which is an upper bound by monotonicity rather than a law run backwards.
///
/// # Panics
/// On an empty or non-monotone table, which would be a transcription error in a constant.
fn from_anchors(anchors: &[(f64, f64)], x: f64, exponent: f64) -> (f64, TermBasis) {
    assert!(!anchors.is_empty(), "a cost law needs at least one anchor");
    debug_assert!(
        anchors
            .windows(2)
            .all(|w| w[0].0 < w[1].0 && w[0].1 <= w[1].1),
        "the anchor table must be increasing in both coordinates"
    );
    let (first_x, first_y) = anchors[0];
    let &(last_x, last_y) = anchors.last().expect("non-empty");
    if x <= first_x {
        return (first_y, TermBasis::Extrapolated);
    }
    if x >= last_x {
        if x == last_x {
            return (last_y, TermBasis::Fitted);
        }
        return (
            last_y * (x / last_x).powf(exponent),
            TermBasis::Extrapolated,
        );
    }
    let at = anchors
        .windows(2)
        .find(|w| x <= w[1].0)
        .expect("x is inside the table");
    let (lo_x, lo_y) = at[0];
    let (hi_x, hi_y) = at[1];
    let local = (hi_y / lo_y).ln() / (hi_x / lo_x).ln();
    (lo_y * (x / lo_x).powf(local), TermBasis::Fitted)
}

// ---------------------------------------------------------------------------------------------
// The determinant laws, moved here from `examples/resultant_cico` unchanged
// ---------------------------------------------------------------------------------------------

/// One order-162 Sylvester determinant at **one** worker, measured.
///
/// `examples/determinant_sweep`, five orders, three draws each, under `tools/benchlock.sh` —
/// `docs/research/resultant-elimination.md` §6.9. It replaces the 2.868 ms §6.5 derived from
/// 37 634.3 ms over 13 123 samples, because **that figure no longer reproduces on this machine**:
/// the same 13 123-determinant reference route measured 45 131.0 ms (3.439 ms each) in M25, and the
/// synthetic sweep 3.624 ms. A cost model whose job is to refuse runs must not be anchored to the
/// fastest figure ever recorded, so the anchor is the larger, current one and §6.9 records the
/// unexplained 1.2x gap as a finding.
///
/// **Left at 3.624 by §6.13, which resolved that gap and could have re-anchored this.** The gap is
/// a measurement session and not an implementation — §6.5's own binary re-run at its own commit
/// gives 45 159.4–47 944.4 ms against the 37 634.3 ms on record — and the registered row measures
/// 3.758–3.840 ms at one worker at `1985504`, so this anchor is mildly optimistic. It is not raised,
/// because the `max` in [`determinant_core_ms`] pairs it with an exponent fitted over five orders in
/// *one* session: re-anchoring at 162 alone would leave the prefactor and the exponent belonging to
/// different sessions, which is the error §6.13 exists to stop. Re-anchoring honestly means
/// re-running §6.9's five-order sweep in one session on a quiet box, which is a measurement rather
/// than an edit.
pub const DETERMINANT_MS_AT_162: f64 = 3.624;

/// The matrix order that cost was measured at.
pub const MEASURED_ORDER: f64 = 162.0;

/// The largest order the dense sweep measured. Above it the dense law is an extrapolation.
pub const DENSE_FITTED_TO_ORDER: usize = 4_374;

/// The exponent measured above the L2 footprint: `core(order) ∝ order^2.9953`, ±0.0285.
///
/// §6.9's sweep, fitted over orders 486, 1 458 and 4 374 — every order whose matrix exceeds this
/// machine's 512 kB L2 — with a worst residual of 3.7%. The kernel is **cubic** up there to within
/// the measurement, and the 3.116 exponent #289 was opened with is not reproduced: it came from
/// dividing a 32-worker core-time at order 1 458 by a single-worker one at order 162, and the
/// width is what the excess was.
///
/// Below L2 the sweep measures 2.79 — fixed per-determinant overhead that the small orders cannot
/// amortize — and that is *sub*-cubic, so a model using it would predict less work than cubic.
/// [`determinant_core_ms`] therefore takes the larger of the two laws rather than this one.
pub const ABOVE_L2_EXPONENT: f64 = 2.9953;

/// How much core-time one determinant gains per doubling of the worker count, measured.
///
/// Core-time per determinant — wall clock times workers — is not flat in the worker count on this
/// box. A budget guard that costed a 32-worker run at the single-worker figure would under-predict
/// it by 30%, and a guard that under-predicts refuses nothing.
///
/// **6.5% a doubling, and §6.13 confirmed it rather than raising it.** The figure came from §6.9's
/// 2.404 s / 2.821 s / 3.148 s at order 1 458 on 1 / 8 / 32 workers. §6.6 had measured 4–9% out to
/// 32 workers, §6.9 re-measured 31–44%, and #319 was that disagreement; §6.13 re-ran §6.6's exact
/// configuration on §6.6's own binary and got **1.058x at 8 workers and 1.063x at 32** — §6.6's
/// figure, reproduced. The 31–44% came back the same day on the same binaries **when other agents'
/// `cargo test --release` runs were resident**: 1.343x and 1.478x. `tools/benchlock.sh` serializes
/// benchmarks and not builds, so that load runs straight through the lock.
///
/// **So the width penalty is 6.5% a doubling and ambient contention is a separate factor of up to
/// 1.4x on top of it.** This constant deliberately models the first and not the second. Folding
/// contention in would make the law predict a number no quiet machine produces, and mixing a
/// kernel property with a machine state is the error §6.13 exists to stop — the 3.116 "super-cubic"
/// exponent of #289 was exactly that mistake. The consequence for an operator is a real one and
/// belongs with the operator: **a 32-worker row on a loaded box costs up to 1.4x what this predicts,
/// so run it under the lock with the box otherwise quiet, and check `load=` in the benchlock log
/// afterwards.**
///
/// The mechanism is **not** the all-core clock, which §6.13 excludes: stages of one process on one
/// core move by 1.00x, 1.04–1.06x and 1.20x according to working-set size, and no clock can do that.
pub const CORE_TIME_PER_DOUBLING: f64 = 0.065;

/// The Euclidean kernel's **remainder sequence** at [`EUCLID_MEASURED_ORDER`], ms, **measured**.
///
/// Not the whole kernel. The kernel has two halves and until #412 this constant was the whole of
/// the law: `1.109 ms` from #350's §5.6, taken on a pair of degree **1** in the surviving variable,
/// where specializing a sample costs 1 460 Horner steps and is 0.4% of the sample. On that pair
/// this *is* the kernel, which is why the omission was invisible.
///
/// #412 re-measured the same quantity in its own process at **1.172 ms** — 5.7% above #350's
/// figure, inside #318's recorded ~1.2x session drift — and the larger is taken, because a cost
/// model that under-predicts is a budget that authorizes a run nobody costed.
pub const EUCLID_REMAINDER_MS_AT_1458: f64 = 1.172;

/// The order the Euclidean anchors were measured at — the order every six-round row uses.
pub const EUCLID_MEASURED_ORDER: f64 = 1458.0;

/// The Euclidean remainder sequence's fitted exponent, **fitted** over three orders.
///
/// Fitted on the synthetic pair, which is the remainder sequence alone — so it is the right
/// exponent for [`EUCLID_REMAINDER_MS_AT_1458`] and not for the whole kernel. #412's own three
/// orders on a row-shaped pair give 1.760 for this half, below the fit, and the fit is kept.
pub const EUCLID_EXPONENT: f64 = 1.8452;

/// Nanoseconds one Horner multiply-add of the per-sample specialization costs, **measured**.
///
/// `determinant_width`, one pinned core, on the lock, over row-shaped pairs at three orders:
/// **4.31 / 4.30 / 4.45 ns** at orders 162 / 486 / 1 458, against counted operation counts of
/// 6 642 / 59 292 / 532 170. The rate is flat across a 9x order range — Horner is a fixed-stride
/// dependent chain and has nothing to amortize — so the term's exponent is the operation count's
/// **2**, and the measured local exponent is **2.010**.
///
/// The largest of the three is taken, for the reason [`EUCLID_REMAINDER_MS_AT_1458`] gives.
pub const EUCLID_SPECIALIZE_NS_PER_OPERATION: f64 = 4.45;

/// Horner multiply-adds one sample's specialization costs on a CICO row's pair, **derived**.
///
/// **This is the term #412 found missing from the law.** `sylvester_resultant_euclid` evaluates
/// every coefficient of the pair in the eliminated variable at the sample point, once per sample,
/// *inside* the per-determinant timer:
///
/// ```text
/// let a: Vec<F> = fc.iter().map(|c| c.eval(&at)).collect();
/// let b: Vec<F> = gc.iter().map(|c| c.eval(&at)).collect();
/// resultant_from_coefficients(&a, &b)
/// ```
///
/// A CICO row of `R` rounds is a straight-line program of total degree `d = 3^R` in its two free
/// inputs, so the coefficient of `y^j` in either output has degree `d − j`, and specializing both
/// at one point is `2 · Σ_{j≤d} (d − j) = d(d + 1)` Horner multiply-adds with `d` half the
/// Sylvester order. That is **2.00x the remainder sequence's own `d²/2`**, so on a real row this
/// term is the larger half of the kernel and it grows as the square of the order where the
/// remainder sequence grows as [`EUCLID_EXPONENT`].
///
/// Derived, and **confirmed by counting**: `examples/determinant_width` sums
/// `Σ_j deg_x(fc[j]) + Σ_j deg_x(gc[j])` off each pair and gets 6 642 / 59 292 / 532 170 at orders
/// 162 / 486 / 1 458, which is `d(d + 1)` exactly.
///
/// It is **zero in all but name** on the synthetic pairs `determinant_sweep` uses, which are degree
/// 1 in the surviving variable: 1 460 steps at order 1 458 against this function's 532 170. That
/// difference is the whole of #412.
pub fn specialization_operations(matrix_order: usize) -> usize {
    let degree = matrix_order / 2;
    degree * (degree + 1)
}

/// Core-time of one Sylvester determinant at `matrix_order` on `workers` workers, in milliseconds.
///
/// The **larger** of the measured above-L2 law and the cubic, both anchored at order 162, times the
/// measured width penalty. Taking the larger is deliberate and is the whole point of the
/// calibration: the fitted exponent 2.9953 is *below* 3, so using the fit alone would predict less
/// work than the cubic this guard has always used, and a cost model that under-predicts is a budget
/// that authorizes a run nobody costed. If a future sweep measures an exponent above 3, this picks
/// it up with no further change.
///
/// Measured at orders 18 to 4 374 and at 1, 8 and 32 workers. Above 4 374 — which is every row past
/// seven rounds — it is an **extrapolation**, and every caller labels it as one.
pub fn determinant_core_ms(matrix_order: usize, workers: usize) -> f64 {
    let ratio = matrix_order as f64 / MEASURED_ORDER;
    let cubic = DETERMINANT_MS_AT_162 * ratio.powi(3);
    let fitted = DETERMINANT_MS_AT_162 * ratio.powf(ABOVE_L2_EXPONENT);
    cubic.max(fitted) * width_penalty(workers)
}

/// Core-time per determinant for the **Euclidean** kernel, in milliseconds.
///
/// **Two terms, because the kernel has two halves** (#412). Per sample it specializes the pair's
/// coefficients at the sample point and then runs a remainder sequence over the result, and both
/// are inside the timer. The specialization is
/// [`specialization_operations`] Horner steps at
/// [`EUCLID_SPECIALIZE_NS_PER_OPERATION`] each; the remainder sequence is
/// [`EUCLID_REMAINDER_MS_AT_1458`] scaled by [`EUCLID_EXPONENT`]. Their sum times this kernel's
/// own [`euclidean_width_penalty`].
///
/// On a CICO row at order 1 458 that is `2.368 + 1.172 = 3.540 ms` against **3.533 ms** measured on
/// the `rf4-rp2` pair at one worker, and the two halves sum to the whole to 1.3% when timed apart.
/// On a row the specialization is the *larger* half, and because it is exactly quadratic where the
/// remainder sequence is `order^1.8452`, its share grows with the round count: ~67% at six rounds
/// and ~70% at seven.
///
/// # What this function got wrong, and how
///
/// It was one term — `1.109 ms` times `order^1.8452` times a 3.21x width penalty — and it predicted
/// the one row anyone has run **correctly, for two compensating wrong reasons**. The anchor was
/// taken on `determinant_sweep`'s synthetic pair, which is degree **1** in the surviving variable,
/// so it measured the remainder sequence and almost none of the specialization; and the 3.21x was
/// read off a 32-worker row figure divided by that anchor, so it absorbed the missing term. `3.01 ×
/// 1.049 = 3.16`, which is the 3.21x to 1.6%.
///
/// The product was right at `(1 458, 32)` and wrong everywhere else: 3.2x optimistic at one worker,
/// and 3.4x pessimistic past 32 where it extrapolated a contention slope that does not exist.
///
/// Measured at orders 162 / 486 / 1 458 and at 1, 2, 4, 8, 16 and 32 workers. Above 1 458 it is an
/// **extrapolation** and [`determinant_basis`] labels it as one.
pub fn euclidean_core_ms(matrix_order: usize, workers: usize) -> f64 {
    let ratio = matrix_order as f64 / EUCLID_MEASURED_ORDER;
    let remainder = EUCLID_REMAINDER_MS_AT_1458 * ratio.powf(EUCLID_EXPONENT);
    let specialize =
        EUCLID_SPECIALIZE_NS_PER_OPERATION * specialization_operations(matrix_order) as f64 / 1e6;
    (remainder + specialize) * euclidean_width_penalty(workers)
}

/// The Euclidean kernel's core-time penalty for running at `workers` workers, **measured**.
///
/// **1.049x at 32 workers — 95.3% parallel efficiency**, swept over 1 / 2 / 4 / 8 / 16 / 32 in one
/// process against one row-shaped pair at order 1 458, on the lock, at an ambient one-minute load of
/// 2.4–4.2. Interpolated linearly in `log2(workers)` as [`width_penalty`] does for the dense kernel
/// and extrapolated at the same slope beyond 32.
///
/// This replaces a **3.21x** that was not a width penalty at all. That figure was `3.563 ms` from a
/// 32-worker row divided by `1.109 ms` from a one-worker synthetic pair — two binaries, two
/// sessions, and two pairs whose per-sample cost differs by 3.01x at *identical* width, which is
/// the term [`specialization_operations`] now carries.
///
/// So axis 4 does not contend worse than the dense kernel. At order 1 458 and 32 workers the
/// Euclidean kernel is 1.049x and the dense one 1.058–1.063x (#319 §6.13) — the same, and both of
/// them near the 1.060x a register-only control shows, which is the floor the machine imposes.
/// The penalty is also **larger at smaller orders** — 1.370x at order 162, 1.114x at 486, 1.049x at
/// 1 458 — which is fixed per-batch thread-spawn overhead failing to amortize, the opposite shape
/// from contention.
pub fn euclidean_width_penalty(workers: usize) -> f64 {
    const PER_DOUBLING: f64 = (1.049 - 1.0) / 5.0;
    1.0 + PER_DOUBLING * (workers.max(1) as f64).log2()
}

/// Core-time per determinant for `kernel`.
pub fn kernel_core_ms(kernel: DeterminantKernel, matrix_order: usize, workers: usize) -> f64 {
    match kernel {
        DeterminantKernel::Dense => determinant_core_ms(matrix_order, workers),
        DeterminantKernel::Euclidean => euclidean_core_ms(matrix_order, workers),
    }
}

/// The measured core-time penalty for running at `workers` workers, as a factor.
///
/// Linear in `log2(workers)` through the widths measured, and extrapolated at the same slope beyond
/// 32 rather than held flat: nothing wider has been measured, and flattening it would make the
/// guard optimistic exactly where it has no evidence. See [`CORE_TIME_PER_DOUBLING`] for why the
/// slope is the uncontended 6.5% and what an operator owes on top of it on a busy box.
pub fn width_penalty(workers: usize) -> f64 {
    1.0 + CORE_TIME_PER_DOUBLING * (workers.max(1) as f64).log2()
}

/// Whether the determinant law is inside the orders it was fitted over.
fn determinant_basis(kernel: DeterminantKernel, matrix_order: usize) -> TermBasis {
    let fitted_to = match kernel {
        DeterminantKernel::Dense => DENSE_FITTED_TO_ORDER,
        DeterminantKernel::Euclidean => EUCLID_MEASURED_ORDER as usize,
    };
    if matrix_order <= fitted_to {
        TermBasis::Fitted
    } else {
        TermBasis::Extrapolated
    }
}

/// The anchor a printed line should name for `kernel`.
fn determinant_anchor(kernel: DeterminantKernel) -> &'static str {
    match kernel {
        DeterminantKernel::Dense => {
            "3.624 ms at order 162, one worker; max(cubic, order^2.9953) x width penalty"
        }
        DeterminantKernel::Euclidean => {
            "1.172 ms remainder at order 1 458 x order^1.8452, plus 4.45 ns x (order/2)(order/2+1) specialization, x measured 1.049x width penalty"
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::KOALABEAR_PRIME;
    use super::*;

    /// `t = 16` KoalaBear Poseidon with the given round split, which is what the ladder's rows are.
    fn row(r_f: usize, r_p: usize) -> PoseidonParameters {
        PoseidonParameters {
            prime: KOALABEAR_PRIME,
            alpha: 3,
            t: 16,
            r_f,
            r_p,
        }
    }

    /// The determinant term alone admits a six-round row whose whole cost the same budget refuses.
    #[test]
    fn a_determinant_only_budget_admits_a_row_it_cannot_afford() {
        let cost = ResultantRowCost::of(&row(4, 2), DeterminantKernel::Euclidean, 32);
        // A budget between the determinant term and the row: the pre-#410 guard admitted here.
        let budget = 100.0;
        assert!(
            cost.determinant_seconds() < budget,
            "the determinant term is {} s, which was the whole of the old guard",
            cost.determinant_seconds()
        );
        assert!(
            cost.pessimistic_seconds() > budget,
            "the row is {} s",
            cost.pessimistic_seconds()
        );
        assert_eq!(
            cost.verdict(budget),
            RowVerdict::OverBudget {
                pessimistic_seconds: cost.pessimistic_seconds()
            }
        );
    }

    /// The determinant term is a minority of the authorized `rf4-rp2` row, as #367 measured.
    #[test]
    fn determinants_are_a_minority_of_a_six_round_row() {
        let cost = ResultantRowCost::of(&row(4, 2), DeterminantKernel::Euclidean, 32);
        assert!(
            cost.determinant_share() < 0.25,
            "determinants are {:.1}% of the row",
            100.0 * cost.determinant_share()
        );
    }

    /// Both band edges are above the 362.0 s #367 measured on `rf4-rp2`, and the optimistic edge is
    /// within 5% of it.
    #[test]
    fn the_band_is_conservative_and_tight_against_the_measured_rf4_rp2_row() {
        let cost = ResultantRowCost::of(&row(4, 2), DeterminantKernel::Euclidean, 32);
        let measured = 362.0;
        let optimistic = cost.optimistic_seconds();
        assert!(
            optimistic >= measured,
            "the optimistic edge {} is below the measured row, so the model under-predicts",
            optimistic
        );
        assert!(
            optimistic <= 1.05 * measured,
            "the optimistic edge {} is more than 5% above the measured row",
            optimistic
        );
        assert!(cost.pessimistic_seconds() > optimistic);
    }

    /// The band's width on `rf6-rp0` is the root finder, which is the reason it is a band.
    #[test]
    fn root_finding_sets_the_band_width_at_six_rounds_of_full() {
        let cost = ResultantRowCost::of(&row(6, 0), DeterminantKernel::Euclidean, 32);
        let width = cost.pessimistic_seconds() - cost.optimistic_seconds();
        assert!(
            width > 0.5 * cost.pessimistic_seconds(),
            "the band is {} s wide on a {} s pessimistic row",
            width,
            cost.pessimistic_seconds()
        );
    }

    /// A row whose symbolic build nobody has measured is refused as unbounded, not admitted.
    #[test]
    fn an_unmeasured_build_makes_a_row_unbounded_rather_than_free() {
        let cost = ResultantRowCost::of(&row(6, 2), DeterminantKernel::Euclidean, 32);
        assert_eq!(cost.build.basis, TermBasis::Unmeasured);
        assert_eq!(cost.unmodelled(), vec!["symbolic build"]);
        // An enormous budget cannot admit it, because the row is not bounded at all.
        assert_eq!(
            cost.verdict(f64::MAX),
            RowVerdict::Unbounded {
                stages: vec!["symbolic build"]
            }
        );
    }

    /// Over-budget is reported ahead of unbounded, since unmodelled terms can only add.
    #[test]
    fn over_budget_outranks_unbounded() {
        let cost = ResultantRowCost::of(&row(6, 2), DeterminantKernel::Euclidean, 32);
        assert!(matches!(cost.verdict(1.0), RowVerdict::OverBudget { .. }));
    }

    /// The four-round rows the default 1 800 s budget has always admitted are still admitted.
    #[test]
    fn the_four_round_rows_stay_inside_the_default_budget() {
        for (r_f, r_p) in [(2, 0), (2, 2), (4, 0)] {
            let cost = ResultantRowCost::of(&row(r_f, r_p), DeterminantKernel::Dense, 1);
            assert_eq!(
                cost.verdict(1_800.0),
                RowVerdict::Admit,
                "rf{}-rp{} costs {} s",
                r_f,
                r_p,
                cost.pessimistic_seconds()
            );
        }
    }

    /// Every anchored law returns its own measurement at the degree it was measured at.
    #[test]
    fn the_anchored_laws_reproduce_their_own_anchors() {
        let (interp, basis) = from_anchors(&[(730.0, 0.0051), (59_050.0, 31.7)], 59_050.0, 2.0);
        assert_eq!(basis, TermBasis::Fitted);
        assert!((interp - 31.7).abs() < 1e-9);
        let gcd = gcd_root_term(59_049);
        assert!((gcd.seconds - 153.2146).abs() < 1e-6, "{}", gcd.seconds);
        let deflation = deflation_root_term(59_049);
        assert!((deflation.seconds - 0.5001).abs() < 1e-9);
    }

    /// A law evaluated past its largest anchor is labelled extrapolated, not fitted.
    #[test]
    fn past_the_largest_anchor_is_extrapolated() {
        let rf6 = ResultantRowCost::of(&row(6, 0), DeterminantKernel::Euclidean, 32);
        assert_eq!(rf6.interpolation.basis, TermBasis::Extrapolated);
        assert_eq!(rf6.root_finding_pessimistic.basis, TermBasis::Extrapolated);
        let rf4 = ResultantRowCost::of(&row(4, 2), DeterminantKernel::Euclidean, 32);
        assert_eq!(rf4.interpolation.basis, TermBasis::Fitted);
        assert_eq!(rf4.root_finding_pessimistic.basis, TermBasis::Fitted);
    }

    /// The anchor table is never below a measurement at or under the degree it is read at.
    #[test]
    fn the_gcd_envelope_is_never_below_a_real_resultant_measurement() {
        // §6.1's real rows: degree 81 / 729 / 6 561 at 0.9 ms / 52.7 ms / 3 933.3 ms.
        for (degree, measured) in [(81usize, 0.0009), (729, 0.0527), (6_561, 3.9333)] {
            let term = gcd_root_term(degree);
            assert!(
                term.seconds >= measured - 1e-9,
                "degree {} predicts {} against {} measured",
                degree,
                term.seconds,
                measured
            );
        }
    }

    /// Costing a row with the Euclidean kernel is cheaper than with the dense one at six rounds.
    #[test]
    fn the_kernel_the_row_is_costed_with_changes_the_determinant_term() {
        let dense = ResultantRowCost::of(&row(4, 2), DeterminantKernel::Dense, 32);
        let euclidean = ResultantRowCost::of(&row(4, 2), DeterminantKernel::Euclidean, 32);
        assert!(euclidean.determinant_seconds() < dense.determinant_seconds());
    }

    /// The Euclidean law at one worker is not below what one worker measured on a row's own pair.
    ///
    /// #412's finding, as a guard. The law was anchored on a **synthetic** pair of degree 1 in the
    /// surviving variable, where the per-sample specialization is 1 460 Horner steps; a registered
    /// row's pair is of total degree `3^R`, where the same specialization is `(order/2)²` steps and
    /// 2.00x the remainder sequence it feeds. Both are inside the per-determinant timer, so the
    /// anchor was 3x below the thing it was costing, and the 3.21x "width penalty" was what hid it.
    #[test]
    fn the_euclidean_law_at_one_worker_covers_a_row_pair_determinant() {
        // `determinant_width --pair row`, order 1 458, one pinned core, on the lock: 3.533 ms.
        const MEASURED_MS: f64 = 3.533;
        let predicted = euclidean_core_ms(1_458, 1);
        assert!(
            predicted >= MEASURED_MS,
            "the law predicts {predicted} ms at one worker where a row's own pair measured \
             {MEASURED_MS} ms — a guard that under-predicts refuses nothing"
        );
    }

    /// The Euclidean width penalty does not exceed what the swept curve measured.
    ///
    /// The 3.21x the law carried was never a width penalty: it was the ratio of two *pairs*, taken
    /// at the same width in two different sessions. Swept in one process the penalty is 1.049x at
    /// 32 workers — 95.3% parallel efficiency, which is the dense kernel's own figure.
    #[test]
    fn the_euclidean_width_penalty_is_the_swept_one() {
        let at_32 = euclidean_width_penalty(32);
        assert!(
            (1.0..=1.10).contains(&at_32),
            "the penalty at 32 workers is {at_32}x against a measured 1.049x"
        );
        assert!(
            euclidean_width_penalty(1) == 1.0,
            "one worker is the curve's own reference"
        );
    }

    /// The law reproduces the one determinant stage anyone has measured, and is not below it.
    ///
    /// `rf4-rp2` ran 59 050 determinants in **6.574 s** of wall on 32 workers (#367). This pins
    /// both halves of the correction at once: a law that fixed the anchor without fixing the
    /// penalty would predict three times this.
    #[test]
    fn the_law_covers_the_measured_rf4_rp2_determinant_stage() {
        const MEASURED_SECONDS: f64 = 6.574;
        let predicted = 59_050.0 * euclidean_core_ms(1_458, 32) / 1e3 / 32.0;
        assert!(
            predicted >= MEASURED_SECONDS,
            "predicts {predicted} s against {MEASURED_SECONDS} s measured"
        );
        assert!(
            predicted <= 1.25 * MEASURED_SECONDS,
            "predicts {predicted} s against {MEASURED_SECONDS} s measured, which is not a cost \
             model but a refusal"
        );
    }

    /// The counted specialization operation count is `d(d + 1)` at every order measured.
    #[test]
    fn the_specialization_operation_count_matches_what_was_counted_off_the_pairs() {
        // `determinant_width` counts `Σ_j deg_x(fc[j]) + Σ_j deg_x(gc[j])` off each pair.
        for (order, counted) in [(162usize, 6_642usize), (486, 59_292), (1_458, 532_170)] {
            assert_eq!(specialization_operations(order), counted, "order {order}");
        }
    }
}
