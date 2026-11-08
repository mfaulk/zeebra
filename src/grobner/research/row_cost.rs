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
/// because every row at a given round count shares the same word degrees — §6.1 measures 419.3 ms
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
/// per two rounds is 145x then 772x, which no law covers, and at seven rounds §7.3 predicts a ~1 TB
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
            anchor: "recorded constant per round count: 2.9 ms at R=2, 419.3 ms at R=4 (§6.1), \
                     324.0 s at R=6 (§8.4.2, on-lock, post-#243)",
        },
        None => CostTerm {
            stage: "symbolic build",
            seconds: 0.0,
            basis: TermBasis::Unmeasured,
            anchor:
                "no build measured at this round count; §7.3 predicts ~1 TB of transient at R=7",
        },
    }
}

/// Lagrange interpolation of the resultant from `samples` evaluations, **measured** anchors.
///
/// Two measurements of the predicted-count Lagrange route, which is the one the example takes:
/// **5.1 ms at 730 samples** (§6.7) and **31.7 s at 59 050** (#367's authorized `rf4-rp2` run).
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
        anchor: "measured 5.1 ms at S=730 (§6.7) and 31.7 s at S=59 050 (#367); O(S^2) above",
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
/// The anchor table is a monotone upper envelope over three sources: §9.7.4's nine-point doubling
/// sweep (256–65 536, one session, one binary, local exponent 1.90–1.97), §9.7.2's four points on
/// planted polynomials, and §6.1's three **real resultants** from registered rows. The real rows
/// are the slowest at their degrees — 3.93 s at 6 561 against the sweep's 3.16 s at 8 192 — which
/// is why they are in the table and why the table is an envelope rather than a fit: a law through
/// the planted sweep alone under-predicts the row it exists to cost.
///
/// Above 65 536 the exponent is **1.933**, the §9.7.4 fit that superseded the two-point one and
/// survived it on eight points.
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
        anchor: "measured envelope over §9.7.4's doubling sweep, §9.7.2 and §6.1's real \
                 resultants; exponent 1.933 above degree 65 536",
    }
}

/// Root finding by deflate-and-repeat over `graeffe_root`, the band's **optimistic** edge.
///
/// §9.7.2, one pinned core, on the lock. The cost is `(roots + 1)` Graeffe searches, so it is a bet
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
            "measured 0.0117–0.5001 s over degrees 729–59 049 (§9.7.2), at the O(1) root count \
                 every registered row has measured; linear above",
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

/// Euclidean core-time per determinant at [`EUCLID_MEASURED_ORDER`], milliseconds, **measured**.
pub const EUCLID_MS_AT_1458: f64 = 1.109;

/// The order the Euclidean anchor was measured at — the order every six-round row uses.
pub const EUCLID_MEASURED_ORDER: f64 = 1458.0;

/// The Euclidean kernel's fitted exponent above the L2 footprint, **fitted** over three orders.
pub const EUCLID_EXPONENT: f64 = 1.8452;

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
/// Anchored at the measurement that landed with #350: **1.109 ms at order 1 458**, one pinned core,
/// on the lock, the Euclidean kernel and its dense comparand taken in the same binary minutes
/// apart. The exponent is the **1.8452** fitted above the L2 footprint over orders 162/486/1 458,
/// against the dense kernel's 2.94 — the two differ by about one power of the order, which is the
/// whole point of axis 4 and the reason the gap widens with the row.
///
/// The width penalty is this kernel's **own, measured**, and it is worse than the dense one —
/// which falsifies the hypothesis this function was first written under.
///
/// #350 predicted axis 4 would *recover* #319's width penalty, on the reasoning that the working
/// set falls from a 17 MB matrix to two ~6 kB coefficient vectors. The authorized `rf4-rp2` row
/// measured the opposite: **3.21x at 32 workers**, against the dense law's 1.32x. 59 050
/// determinants took 6.574 s of wall on 32 workers, so 210.4 s of core time, so **3.563 ms** a
/// determinant against the **1.109 ms** measured on one core.
///
/// The first version of this function used [`width_penalty`] — the dense curve — and called that
/// conservative. It was optimistic, and under-predicted the row's determinant stage by **2.43x**.
/// The mechanism is **unmeasured**; the plausible candidate is allocator contention, since
/// `remainder` allocates a fresh vector per step and there are as many steps as the degree, so 32
/// threads each allocate thousands of times per determinant where the dense kernel allocates a
/// handful of large matrices. That is a hypothesis and #412 is the measurement.
pub fn euclidean_core_ms(matrix_order: usize, workers: usize) -> f64 {
    let ratio = matrix_order as f64 / EUCLID_MEASURED_ORDER;
    EUCLID_MS_AT_1458 * ratio.powf(EUCLID_EXPONENT) * euclidean_width_penalty(workers)
}

/// The Euclidean kernel's measured core-time penalty for running at `workers` workers.
///
/// Anchored on the two points there are: **1.0x at one worker** and **3.21x at 32**, interpolated
/// linearly in `log2(workers)` as [`width_penalty`] does for the dense kernel, and extrapolated at
/// the same slope beyond 32 rather than held flat — nothing wider has been measured and flattening
/// it would make the guard optimistic exactly where it has no evidence, which is the mistake this
/// function already made once.
pub fn euclidean_width_penalty(workers: usize) -> f64 {
    const PER_DOUBLING: f64 = (3.21 - 1.0) / 5.0;
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
            "1.109 ms at order 1 458, one worker; order^1.8452 x measured 3.21x width penalty"
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
}
