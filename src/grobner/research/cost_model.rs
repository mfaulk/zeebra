//! The cost-and-resource-model register: what a stage was predicted to cost, what it cost, and why
//! those differ.
//!
//! # The one invariant
//!
//! **A prediction and a measurement are never representable by the same field without a label.**
//! [`FigureBasis`] is that label and every figure carries one. The failure this exists to prevent
//! is documented rather than hypothetical: `MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md` §10.1 found
//! that every M24 prediction about a stage Zeebra had already *measured* held, and every prediction
//! about a quantity nobody had measured was wrong — three of the four by more than an order of
//! magnitude — because all ten were written in the same prose with the same confidence.
//!
//! The name is deliberately not `Provenance`: [`f4::certify::Provenance`](crate::grobner::f4) is
//! about whether a derivation invariant holds and [`record::Provenance`](crate::grobner::record::Provenance)
//! is a licensing struct. It is deliberately *like* `RssBasis` and `CpuBasis` in
//! `grobner::external::contract`, which are the same idea one level down: a byte count whose basis
//! is unstated is the quantity those two exist to keep apart.
//!
//! # What is reused rather than reinvented
//!
//! [`Environment`] and [`Json`] from the cryptanalysis scoreboard, and the conventions
//! `grobner::external::board` established on top of them: hand-rolled JSON with absent figures
//! **omitted** rather than `null`, a generated Markdown renderer so the readable table cannot drift
//! from the data, an append-only history with its contract written into the file, and a closed set
//! wherever a free-text field would let two different things be written in one column.
//!
//! No `serde` reaches this subsystem, by the same decision as the boards it mirrors.
//!
//! # Two things the schema refuses
//!
//! - **An estimate in a measured field** is a [`SchemaError`], not a caveat. `measured_*` holds
//!   only [`FigureBasis::Measured`] and `predicted_*` holds only the other three.
//! - **Peak allocated and peak resident do not share a column.** #237 measured 21 674 MB allocated
//!   against 13 996 MB resident on one row, because a `VecDeque` reached `2^28` slots in a single
//!   20 480 MiB allocation of which ~60% was never written. One allocation larger than the whole
//!   resident peak is why reading "peak memory" carefully does not distinguish the two — only
//!   recording which one it is does.
//!
//! # Curated, not a second copy of the scoreboard
//!
//! Every row is here because somebody made a claim about what a stage would cost. A row may be
//! *emitted* from a retained run by [`CostRow::from_run`], filling only the measured half, but
//! [`select_runs_by_stem`] takes the runs **by name** and there is no way to ask for all of them
//! (#532). Two reasons, and the second is the harder one: an emitted row carries no prediction, so
//! [`CostModelBoard::open_predictions`] ignores it while [`CostModelBoard::to_markdown`] still
//! renders it; and — until #540 — a run that shared a `run_file_stem` with another had no record
//! file holding its figures, so a row emitted for it would cite a source that did not contain it.
//! Sixteen retained runs were in that position. **#540 closed it**: the stem carries a digest over
//! the record, so every retained run has its own file and the citation always resolves. The first
//! reason stands on its own and is why the register is still curated.
//!
//! Prediction error is **derived** by [`CostRow::prediction_errors`] and never authored. The stored
//! form carries it for a machine consumer's convenience and [`CostRow::from_json`] ignores what is
//! there, so a typo in the file cannot become a published finding.

use std::{collections::BTreeMap, fmt::Write as _, time::Duration};

use super::{Environment, Json, RunRecord};

/// What `research/cost-model/results/history.json` promises a consumer.
///
/// Append-only for the reason the cryptanalysis history is: array position is the only record of
/// when a row was taken, and a re-measurement of an already-registered claim is a **new row** —
/// overwriting one because a newer implementation is faster destroys the evidence that the
/// prediction was ever wrong, which is the only thing this board is for.
pub const COST_MODEL_HISTORY_CONTRACT: &str = "every cost-model row ever recorded, APPEND-ONLY \
     and in the order recorded, INCLUDING the rows whose prediction has no measurement yet. Every \
     figure carries a basis: measured, fitted, predicted or extrapolated. A `measured_` field \
     holds ONLY a measured figure and a `predicted_` field NEVER holds one -- a row that violates \
     either is a schema error, not a caveat. Peak allocated and peak resident are separate \
     columns and are not comparable (see grobner::external::contract::RssBasis). Prediction error \
     is DERIVED from the predicted and measured columns; the stored `derived` object is a \
     convenience and is recomputed on load. A re-measurement is a new row with a new commit, \
     never an edit to an old one.";

/// What a figure *is*, which is not the same question as what it says.
///
/// The four variants are ordered by how much evidence stands behind them. [`Self::Measured`] is the
/// only one an instrument produced; the other three are arithmetic, and the distance between
/// [`Self::Fitted`] and [`Self::Extrapolated`] is the whole of #289's useful caveat — the same cubic
/// law is a 3.7%-residual fit at order 4 374 and a guess at order 13 122.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FigureBasis {
    /// An instrument read it off a run that happened.
    ///
    /// Carries the instrument because two instruments for "peak memory" measure different
    /// quantities: `VmHWM` counts touched pages and a tracking allocator counts reservations.
    Measured {
        /// `VmHWM`, `/usr/bin/time -v`, `tracking global allocator`, `count x size_of`.
        instrument: String,
    },

    /// A regression over measurements, valid only inside the range it was fitted over.
    ///
    /// `fitted_to` is **not** optional. A fitted law quoted without its applicability limit is an
    /// extrapolation waiting to be mistaken for a measurement, which is exactly what #289's
    /// `8.3216e-10 · order^2.9953` would be at order 13 122.
    Fitted {
        /// The law in its own variable: `8.3216e-10 * order^2.9953`.
        law: String,
        /// Worst residual over the fitted points, in basis points. 3.7% is `370`.
        ///
        /// Basis points rather than a float because [`Json`] has no float, and a decimal rounded
        /// on the way out and read back as exact would be a figure nobody measured.
        worst_residual_bp: u32,
        /// The largest input the law was fitted over, in the law's own variable.
        fitted_to: i128,
    },

    /// Nobody measured it. A number from a plan, a model, or an argument.
    Predicted {
        /// The reasoning that produced it: `max_live_nonzeros x 16 B`, `term-products x 16 B`.
        model: String,
    },

    /// A fitted law evaluated past the range it was fitted over.
    ///
    /// Separated from [`Self::Fitted`] because the residual does not transfer: nothing bounds the
    /// error of a law outside its range, and [`Self::times_past_the_evidence`] is the only honest
    /// thing the row can report in place of one.
    Extrapolated {
        /// The law being evaluated.
        law: String,
        /// The largest input it was fitted over.
        fitted_to: i128,
        /// The input it was evaluated at. Larger than `fitted_to`, or this is a [`Self::Fitted`].
        evaluated_at: i128,
    },
}

impl FigureBasis {
    /// The stable tag used in records and tables.
    pub fn tag(&self) -> &'static str {
        match self {
            Self::Measured { .. } => "measured",
            Self::Fitted { .. } => "fitted",
            Self::Predicted { .. } => "predicted",
            Self::Extrapolated { .. } => "extrapolated",
        }
    }

    /// True only for [`Self::Measured`]. **The gate every `measured_*` field is checked against.**
    pub fn is_measurement(&self) -> bool {
        matches!(self, Self::Measured { .. })
    }

    /// How far past its evidence an extrapolation reaches, as a multiple.
    ///
    /// `None` for every other basis, because none of them is outside a range. #289's order 13 122
    /// against a fit to 4 374 is `3.0`, and that number is the caveat.
    pub fn times_past_the_evidence(&self) -> Option<f64> {
        match self {
            Self::Extrapolated {
                fitted_to,
                evaluated_at,
                ..
            } if *fitted_to > 0 => Some(*evaluated_at as f64 / *fitted_to as f64),
            _ => None,
        }
    }

    /// The basis in a sentence, for a table cell and for the stored record.
    pub fn detail(&self) -> String {
        match self {
            Self::Measured { instrument } => format!("measured by {}", instrument),
            Self::Fitted {
                law,
                worst_residual_bp,
                fitted_to,
            } => format!(
                "fitted `{}`, worst residual {:.2}%, fitted to {}",
                law,
                *worst_residual_bp as f64 / 100.0,
                fitted_to
            ),
            Self::Predicted { model } => format!("predicted from {}", model),
            Self::Extrapolated {
                law,
                fitted_to,
                evaluated_at,
            } => format!(
                "extrapolated `{}` to {}, {:.1}x past the largest input measured ({})",
                law,
                evaluated_at,
                self.times_past_the_evidence().unwrap_or(f64::NAN),
                fitted_to
            ),
        }
    }

    /// The basis as JSON, round-tripping its payload exactly.
    pub fn to_json(&self) -> Json {
        match self {
            Self::Measured { instrument } => Json::object([
                ("kind", Json::string("measured")),
                ("instrument", Json::string(instrument)),
            ]),
            Self::Fitted {
                law,
                worst_residual_bp,
                fitted_to,
            } => Json::object([
                ("kind", Json::string("fitted")),
                ("law", Json::string(law)),
                ("worst_residual_bp", Json::int(*worst_residual_bp)),
                ("fitted_to", Json::int(*fitted_to)),
            ]),
            Self::Predicted { model } => Json::object([
                ("kind", Json::string("predicted")),
                ("model", Json::string(model)),
            ]),
            Self::Extrapolated {
                law,
                fitted_to,
                evaluated_at,
            } => Json::object([
                ("kind", Json::string("extrapolated")),
                ("law", Json::string(law)),
                ("fitted_to", Json::int(*fitted_to)),
                ("evaluated_at", Json::int(*evaluated_at)),
            ]),
        }
    }

    /// A basis read back from JSON.
    ///
    /// # Errors
    /// [`SchemaError::MalformedRow`] when the kind is missing or unknown. An unreadable basis is
    /// **not** defaulted to anything: defaulting it to `Measured` would manufacture the exact
    /// claim this type exists to prevent, and defaulting it to `Predicted` would silently demote a
    /// real measurement.
    pub fn from_json(value: &Json) -> Result<Self, SchemaError> {
        let text = |key: &'static str| -> Result<String, SchemaError> {
            Ok(value
                .get(key)
                .and_then(Json::as_str)
                .ok_or(SchemaError::MalformedRow { field: key })?
                .to_string())
        };
        let number = |key: &'static str| -> Result<i128, SchemaError> {
            value
                .get(key)
                .and_then(Json::as_int)
                .ok_or(SchemaError::MalformedRow { field: key })
        };
        match value.get("kind").and_then(Json::as_str) {
            Some("measured") => Ok(Self::Measured {
                instrument: text("instrument")?,
            }),
            Some("fitted") => Ok(Self::Fitted {
                law: text("law")?,
                worst_residual_bp: number("worst_residual_bp")?.unsigned_abs() as u32,
                fitted_to: number("fitted_to")?,
            }),
            Some("predicted") => Ok(Self::Predicted {
                model: text("model")?,
            }),
            Some("extrapolated") => Ok(Self::Extrapolated {
                law: text("law")?,
                fitted_to: number("fitted_to")?,
                evaluated_at: number("evaluated_at")?,
            }),
            _ => Err(SchemaError::MalformedRow {
                field: "basis.kind",
            }),
        }
    }
}

impl std::fmt::Display for FigureBasis {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.detail())
    }
}

/// A number, what kind of number it is, and where to read it.
///
/// The three travel together or not at all. A figure whose basis is in one column and whose value
/// is in another is one careless `SELECT` away from being quoted as a measurement.
#[derive(Clone, Debug, PartialEq)]
pub struct Figure<T> {
    /// The quantity itself, in a unit fixed by the field that holds it.
    pub value: T,

    /// What makes it a number. **Read before comparing two figures.**
    pub basis: FigureBasis,

    /// Where it is published: a document section, an issue, or a results file.
    ///
    /// Non-empty on every figure in the register. A row whose figure cannot be sourced does not go
    /// in: an invented number on a board about prediction accuracy would be self-refuting.
    pub source: String,
}

impl<T> Figure<T> {
    /// A figure an instrument produced.
    pub fn measured(value: T, instrument: impl Into<String>, source: impl Into<String>) -> Self {
        Self {
            value,
            basis: FigureBasis::Measured {
                instrument: instrument.into(),
            },
            source: source.into(),
        }
    }

    /// A figure a plan, model or argument produced, with nothing measured behind it.
    pub fn predicted(value: T, model: impl Into<String>, source: impl Into<String>) -> Self {
        Self {
            value,
            basis: FigureBasis::Predicted {
                model: model.into(),
            },
            source: source.into(),
        }
    }

    /// A figure with an explicitly given basis, for [`FigureBasis::Fitted`] and
    /// [`FigureBasis::Extrapolated`], whose payloads are too specific for a positional constructor.
    pub fn with_basis(value: T, basis: FigureBasis, source: impl Into<String>) -> Self {
        Self {
            value,
            basis,
            source: source.into(),
        }
    }

    /// Shorthand for `self.basis.is_measurement()`.
    pub fn is_measurement(&self) -> bool {
        self.basis.is_measurement()
    }

    /// The basis and source, as the two keys every stored figure carries.
    fn common_json(&self) -> Vec<(&'static str, Json)> {
        vec![
            ("basis", self.basis.to_json()),
            ("source", Json::string(&self.source)),
        ]
    }
}

impl Figure<u64> {
    /// A byte figure as JSON.
    pub fn to_json(&self) -> Json {
        let mut fields = vec![("bytes", Json::int(self.value))];
        fields.extend(self.common_json());
        Json::object(fields)
    }

    /// A byte figure read back.
    ///
    /// # Errors
    /// [`SchemaError::MalformedRow`] when the value or the basis is unreadable.
    pub fn from_json(value: &Json) -> Result<Self, SchemaError> {
        Ok(Self {
            value: value
                .get("bytes")
                .and_then(Json::as_int)
                .ok_or(SchemaError::MalformedRow { field: "bytes" })?
                .unsigned_abs() as u64,
            basis: basis_of(value)?,
            source: source_of(value),
        })
    }
}

impl Figure<Duration> {
    /// An elapsed-time figure as JSON.
    pub fn to_json(&self) -> Json {
        let mut fields = vec![("elapsed_nanos", Json::nanos(self.value))];
        fields.extend(self.common_json());
        Json::object(fields)
    }

    /// An elapsed-time figure read back.
    ///
    /// # Errors
    /// [`SchemaError::MalformedRow`] when the value or the basis is unreadable.
    pub fn from_json(value: &Json) -> Result<Self, SchemaError> {
        Ok(Self {
            value: Duration::from_nanos(
                value
                    .get("elapsed_nanos")
                    .and_then(Json::as_int)
                    .ok_or(SchemaError::MalformedRow {
                        field: "elapsed_nanos",
                    })?
                    .unsigned_abs() as u64,
            ),
            basis: basis_of(value)?,
            source: source_of(value),
        })
    }
}

impl Figure<i128> {
    /// A counted figure as JSON.
    pub fn to_json(&self) -> Json {
        let mut fields = vec![("count", Json::int(self.value))];
        fields.extend(self.common_json());
        Json::object(fields)
    }

    /// A counted figure read back.
    ///
    /// # Errors
    /// [`SchemaError::MalformedRow`] when the value or the basis is unreadable.
    pub fn from_json(value: &Json) -> Result<Self, SchemaError> {
        Ok(Self {
            value: value
                .get("count")
                .and_then(Json::as_int)
                .ok_or(SchemaError::MalformedRow { field: "count" })?,
            basis: basis_of(value)?,
            source: source_of(value),
        })
    }
}

/// The basis of a stored figure, refusing rather than defaulting. See [`FigureBasis::from_json`].
fn basis_of(value: &Json) -> Result<FigureBasis, SchemaError> {
    FigureBasis::from_json(
        value
            .get("basis")
            .ok_or(SchemaError::MalformedRow { field: "basis" })?,
    )
}

/// The source of a stored figure. Empty is tolerated here and refused by [`CostRow::check`].
fn source_of(value: &Json) -> String {
    value
        .get("source")
        .and_then(Json::as_str)
        .unwrap_or_default()
        .to_string()
}

/// A quantity that is neither a time nor a byte count: a count, a degree, a share, a ratio.
///
/// Integer in a **stated** unit because [`Json`] has no float. A share goes in as basis points and
/// says so in `unit`, which keeps the stored file exact and keeps the reader from dividing by the
/// wrong thousand.
#[derive(Clone, Debug, PartialEq)]
pub struct Quantity {
    /// What it counts: `families per witness`, `parallel efficiency`, `fftmul degree ceiling`.
    pub name: String,

    /// The unit `figure.value` is in: `families`, `basis points`, `log2 degree`.
    pub unit: String,

    /// The number, with its basis.
    pub figure: Figure<i128>,
}

impl Quantity {
    /// A quantity as JSON.
    pub fn to_json(&self) -> Json {
        Json::object([
            ("name", Json::string(&self.name)),
            ("unit", Json::string(&self.unit)),
            ("figure", self.figure.to_json()),
        ])
    }

    /// A quantity read back.
    ///
    /// # Errors
    /// [`SchemaError::MalformedRow`] when the name or the figure is unreadable.
    pub fn from_json(value: &Json) -> Result<Self, SchemaError> {
        Ok(Self {
            name: value
                .get("name")
                .and_then(Json::as_str)
                .ok_or(SchemaError::MalformedRow {
                    field: "quantity.name",
                })?
                .to_string(),
            unit: value
                .get("unit")
                .and_then(Json::as_str)
                .unwrap_or_default()
                .to_string(),
            figure: Figure::<i128>::from_json(value.get("figure").ok_or(
                SchemaError::MalformedRow {
                    field: "quantity.figure",
                },
            )?)?,
        })
    }
}

/// Which stage, and which structure inside it, bound the run.
///
/// **A closed set, not a string.** #237's finding is unstateable in a free-text column: "memory"
/// and "the `2^28`-slot monomial queue of one refused batch" are both legal strings and only the
/// second is the result. The same conflation is what #237 was opened about.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum LimitingStage {
    /// Symbolic preprocessing's pending-monomial queue. #237: 88.4% of peak RSS, before any matrix
    /// exists and therefore before any entry budget can be crossed.
    SymbolicPreprocessingQueue,

    /// Macaulay matrix entry storage — the quantity `max_live_nonzeros` budgets. #237: 1.3%.
    MatrixEntryStorage,

    /// Reduction of the matrix: elimination, or the LU inside a determinant.
    LinearAlgebra,

    /// The basis itself, in however many copies are live at once.
    BasisStorage,

    /// A polynomial multiply's `O(|a| · |b|)` transient. §6.8: 56.6 GB for a 4.3 MB product.
    PolynomialMultiplyTransient,

    /// Evaluation of Sylvester determinants.
    DeterminantEvaluation,

    /// Interpolation and recovery of the eliminant.
    EliminantRecovery,

    /// Univariate root finding.
    RootFinding,

    /// Order conversion, FGLM-style.
    OrderConversion,

    /// A declared wall-clock budget stopped it, so nothing internal bound.
    WallClockBudget,

    /// Nothing bound: the run finished inside every budget.
    NothingBound,

    /// It was bound and which stage is not established. **Not a synonym for
    /// [`Self::NothingBound`]** — one says the run was free and the other says nobody looked.
    NotEstablished,
}

impl LimitingStage {
    /// The stable tag used in records and tables.
    pub fn tag(&self) -> &'static str {
        match self {
            Self::SymbolicPreprocessingQueue => "symbolic-preprocessing-queue",
            Self::MatrixEntryStorage => "matrix-entry-storage",
            Self::LinearAlgebra => "linear-algebra",
            Self::BasisStorage => "basis-storage",
            Self::PolynomialMultiplyTransient => "polynomial-multiply-transient",
            Self::DeterminantEvaluation => "determinant-evaluation",
            Self::EliminantRecovery => "eliminant-recovery",
            Self::RootFinding => "root-finding",
            Self::OrderConversion => "order-conversion",
            Self::WallClockBudget => "wall-clock-budget",
            Self::NothingBound => "nothing-bound",
            Self::NotEstablished => "not-established",
        }
    }

    /// The stage for a tag, or `None` for one this version does not know.
    pub fn from_tag(tag: &str) -> Option<Self> {
        [
            Self::SymbolicPreprocessingQueue,
            Self::MatrixEntryStorage,
            Self::LinearAlgebra,
            Self::BasisStorage,
            Self::PolynomialMultiplyTransient,
            Self::DeterminantEvaluation,
            Self::EliminantRecovery,
            Self::RootFinding,
            Self::OrderConversion,
            Self::WallClockBudget,
            Self::NothingBound,
            Self::NotEstablished,
        ]
        .into_iter()
        .find(|stage| stage.tag() == tag)
    }
}

impl std::fmt::Display for LimitingStage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.tag())
    }
}

/// Why a prediction and the measurement of it differ.
///
/// A closed set with prose inside the variants, because the *kind* of error is the reusable finding
/// and the detail is not. §10.1's two patterns are visible only because the column distinguishes
/// "wrong by a factor" from "about the wrong quantity": the budget ladder's 16 GB is within 8% of
/// the 14.75 GB process it was compared against and is still the worst entry in the table, because
/// it bounded one allocation and was read as bounding a process.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Attribution {
    /// The prediction was right, within the measurement's own spread.
    PredictionHeld,

    /// The prediction modelled a different quantity, rather than this one badly.
    WrongQuantity {
        /// What the prediction actually bounded.
        predicted_quantity: String,
        /// What was measured.
        actual_quantity: String,
    },

    /// The prediction charged the subject a stage the subject does not run.
    StageNotInScope {
        /// The stage, and whose it is.
        stage: String,
    },

    /// Two figures of different kinds were divided: core-time against a wall clock, one worker
    /// width against another, one session against another.
    IncomparableFigures {
        /// What was divided by what.
        detail: String,
    },

    /// Right quantity, wrong magnitude.
    MagnitudeOnly {
        /// Where the magnitude came from.
        detail: String,
    },

    /// A risk the plan did not list at all — distinct from a listed risk mis-sized, which is
    /// [`Self::MagnitudeOnly`].
    UnlistedRisk {
        /// What was not listed.
        detail: String,
    },

    /// Measured, reproducible, and nobody knows why.
    ///
    /// **A legitimate attribution.** #318 and #319 were both of this kind and both belonged on the
    /// board: a schema that forced a cause would have one invented for it. Both are now resolved —
    /// §6.13 re-ran each figure's own binary and found the gap to be
    /// [`Self::IncomparableFigures`], one session against another — and the M25 rows keep this
    /// attribution anyway, because they were unexplained when taken and the register is
    /// append-only. The resolution is a later row, not an edit to an earlier one.
    Unexplained {
        /// The issue tracking it, so the row points at where the work is.
        issue: String,
        /// What is unexplained.
        detail: String,
    },

    /// There is no measurement, so there is nothing to attribute. The legal state of a row that is
    /// a prediction and nothing else.
    NoMeasurementYet,
}

impl Attribution {
    /// The stable tag used in records and tables.
    pub fn tag(&self) -> &'static str {
        match self {
            Self::PredictionHeld => "prediction-held",
            Self::WrongQuantity { .. } => "wrong-quantity",
            Self::StageNotInScope { .. } => "stage-not-in-scope",
            Self::IncomparableFigures { .. } => "incomparable-figures",
            Self::MagnitudeOnly { .. } => "magnitude-only",
            Self::UnlistedRisk { .. } => "unlisted-risk",
            Self::Unexplained { .. } => "unexplained",
            Self::NoMeasurementYet => "no-measurement-yet",
        }
    }

    /// True where the difference is accounted for. [`Self::Unexplained`] is **not**.
    pub fn is_explained(&self) -> bool {
        !matches!(self, Self::Unexplained { .. } | Self::NoMeasurementYet)
    }

    /// The attribution in a sentence.
    pub fn detail(&self) -> String {
        match self {
            Self::PredictionHeld => "the prediction held".to_string(),
            Self::WrongQuantity {
                predicted_quantity,
                actual_quantity,
            } => format!(
                "the wrong quantity: predicted {}, measured {}",
                predicted_quantity, actual_quantity
            ),
            Self::StageNotInScope { stage } => {
                format!("charged a stage the subject does not run: {}", stage)
            }
            Self::IncomparableFigures { detail } => format!("incomparable figures: {}", detail),
            Self::MagnitudeOnly { detail } => format!("magnitude only: {}", detail),
            Self::UnlistedRisk { detail } => format!("a risk nobody listed: {}", detail),
            Self::Unexplained { issue, detail } => {
                format!("UNEXPLAINED ({}): {}", issue, detail)
            }
            Self::NoMeasurementYet => "no measurement yet, so nothing to attribute".to_string(),
        }
    }

    /// The attribution as JSON.
    pub fn to_json(&self) -> Json {
        let mut fields = vec![("kind", Json::string(self.tag()))];
        match self {
            Self::WrongQuantity {
                predicted_quantity,
                actual_quantity,
            } => {
                fields.push(("predicted_quantity", Json::string(predicted_quantity)));
                fields.push(("actual_quantity", Json::string(actual_quantity)));
            }
            Self::StageNotInScope { stage } => fields.push(("stage", Json::string(stage))),
            Self::IncomparableFigures { detail }
            | Self::MagnitudeOnly { detail }
            | Self::UnlistedRisk { detail } => fields.push(("detail", Json::string(detail))),
            Self::Unexplained { issue, detail } => {
                fields.push(("issue", Json::string(issue)));
                fields.push(("detail", Json::string(detail)));
            }
            Self::PredictionHeld | Self::NoMeasurementYet => {}
        }
        Json::object(fields)
    }

    /// An attribution read back.
    ///
    /// # Errors
    /// [`SchemaError::MalformedRow`] for an absent or unknown kind. Not defaulted, for the reason
    /// [`FigureBasis::from_json`] is not: every default here asserts something about a measurement.
    pub fn from_json(value: &Json) -> Result<Self, SchemaError> {
        let text = |key: &str| {
            value
                .get(key)
                .and_then(Json::as_str)
                .unwrap_or_default()
                .to_string()
        };
        match value.get("kind").and_then(Json::as_str) {
            Some("prediction-held") => Ok(Self::PredictionHeld),
            Some("wrong-quantity") => Ok(Self::WrongQuantity {
                predicted_quantity: text("predicted_quantity"),
                actual_quantity: text("actual_quantity"),
            }),
            Some("stage-not-in-scope") => Ok(Self::StageNotInScope {
                stage: text("stage"),
            }),
            Some("incomparable-figures") => Ok(Self::IncomparableFigures {
                detail: text("detail"),
            }),
            Some("magnitude-only") => Ok(Self::MagnitudeOnly {
                detail: text("detail"),
            }),
            Some("unlisted-risk") => Ok(Self::UnlistedRisk {
                detail: text("detail"),
            }),
            Some("unexplained") => Ok(Self::Unexplained {
                issue: text("issue"),
                detail: text("detail"),
            }),
            Some("no-measurement-yet") => Ok(Self::NoMeasurementYet),
            _ => Err(SchemaError::MalformedRow {
                field: "attribution.kind",
            }),
        }
    }
}

/// The largest intermediate object a run built, in its own terms.
///
/// Sized in its own unit rather than in bytes because the interesting fact about §6.8's product is
/// `3.54e9` term-products against a 266 815-term result, and converting both to bytes loses it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Intermediate {
    /// What it is: `Sylvester matrix`, `bivariate product transient`, `pending monomial queue`.
    pub what: String,

    /// Its extent.
    pub extent: i128,

    /// What `extent` counts: `matrix order`, `term-products`, `monomials`.
    pub unit: String,
}

impl Intermediate {
    /// An intermediate object, described and sized.
    pub fn new(what: impl Into<String>, extent: i128, unit: impl Into<String>) -> Self {
        Self {
            what: what.into(),
            extent,
            unit: unit.into(),
        }
    }

    /// As JSON.
    fn to_json(&self) -> Json {
        Json::object([
            ("what", Json::string(&self.what)),
            ("extent", Json::int(self.extent)),
            ("unit", Json::string(&self.unit)),
        ])
    }

    /// Read back, tolerantly: a partially recorded intermediate is better evidence than none.
    fn from_json(value: &Json) -> Self {
        Self {
            what: value
                .get("what")
                .and_then(Json::as_str)
                .unwrap_or_default()
                .to_string(),
            extent: value.get("extent").and_then(Json::as_int).unwrap_or(0),
            unit: value
                .get("unit")
                .and_then(Json::as_str)
                .unwrap_or_default()
                .to_string(),
        }
    }
}

/// What the next size up is projected to cost, and on what basis.
///
/// Carried on the row rather than derived, because the projection is a *claim* this milestone makes
/// and the next one checks. Its figures are necessarily [`FigureBasis::Predicted`] or
/// [`FigureBasis::Extrapolated`]: if the next size had been measured it would be a row of its own.
#[derive(Clone, Debug, PartialEq)]
pub struct NextSizeProjection {
    /// What "next size" means here: `order 13 122`, `N = 6`, `eight rounds`.
    pub next: String,

    /// The projected runtime.
    pub runtime: Option<Figure<Duration>>,

    /// The projected peak storage.
    pub peak_bytes: Option<Figure<u64>>,
}

impl NextSizeProjection {
    /// A projection for `next`, with no figures yet.
    pub fn of(next: impl Into<String>) -> Self {
        Self {
            next: next.into(),
            runtime: None,
            peak_bytes: None,
        }
    }

    /// Set the projected runtime.
    pub fn with_runtime(mut self, runtime: Figure<Duration>) -> Self {
        self.runtime = Some(runtime);
        self
    }

    /// Set the projected peak storage.
    pub fn with_peak_bytes(mut self, bytes: Figure<u64>) -> Self {
        self.peak_bytes = Some(bytes);
        self
    }

    /// As JSON.
    fn to_json(&self) -> Json {
        let mut fields = vec![("next", Json::string(&self.next))];
        if let Some(runtime) = &self.runtime {
            fields.push(("runtime", runtime.to_json()));
        }
        if let Some(bytes) = &self.peak_bytes {
            fields.push(("peak_bytes", bytes.to_json()));
        }
        Json::object(fields)
    }

    /// Read back.
    ///
    /// # Errors
    /// [`SchemaError`] from either figure.
    fn from_json(value: &Json) -> Result<Self, SchemaError> {
        Ok(Self {
            next: value
                .get("next")
                .and_then(Json::as_str)
                .unwrap_or_default()
                .to_string(),
            runtime: value
                .get("runtime")
                .map(Figure::<Duration>::from_json)
                .transpose()?,
            peak_bytes: value
                .get("peak_bytes")
                .map(Figure::<u64>::from_json)
                .transpose()?,
        })
    }
}

/// A prediction against the measurement of it. **Derived, never stored as truth.**
///
/// Produced only by [`CostRow::prediction_errors`]. An author-supplied error column is a place for
/// a typo to become a published finding, so [`CostRow::from_json`] recomputes this and ignores
/// whatever the file's `derived` object says.
#[derive(Clone, Debug, PartialEq)]
pub struct PredictionError {
    /// Which pair this is: `runtime`, `peak memory`, `accounted storage`, or the quantity's name.
    pub quantity: String,

    /// What was predicted, rendered in the pair's own unit, for the table.
    pub predicted: String,

    /// What was measured, likewise.
    pub measured: String,

    /// `measured / predicted`. Above one means the prediction was **low**.
    pub factor: f64,

    /// `(measured - predicted) / predicted`, as a percentage. Signed.
    pub relative_percent: f64,
}

impl PredictionError {
    /// The error between two figures, or `None` where the prediction is zero and no ratio exists.
    fn between(
        quantity: &str,
        predicted: f64,
        measured: f64,
        render: impl Fn(f64) -> String,
    ) -> Option<Self> {
        if predicted == 0.0 || !predicted.is_finite() || !measured.is_finite() {
            return None;
        }
        Some(Self {
            quantity: quantity.to_string(),
            predicted: render(predicted),
            measured: render(measured),
            factor: measured / predicted,
            relative_percent: (measured - predicted) / predicted * 100.0,
        })
    }
}

/// Why a row is not a legal row, or why a stored one could not be read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SchemaError {
    /// A field the register reads is missing, or is at the wrong type.
    MalformedRow {
        /// Which field.
        field: &'static str,
    },

    /// A `measured_*` field holds something no instrument produced. **The headline refusal.**
    EstimateInAMeasuredField {
        /// Which field.
        field: &'static str,
        /// The basis it holds instead.
        basis: &'static str,
    },

    /// A `predicted_*` field holds a measurement, which would launder a measurement into a claim
    /// about what was expected before it.
    MeasurementInAPredictedField {
        /// Which field.
        field: &'static str,
    },

    /// A row with no measurement attributes a difference that does not exist yet.
    AttributionWithoutAMeasurement,

    /// A row with both a prediction and a measurement of it declines to attribute the difference.
    MeasurementWithoutAnAttribution,

    /// A figure carries no source. Every number here is cited or absent.
    UnsourcedFigure {
        /// Which field.
        field: &'static str,
    },
}

impl std::fmt::Display for SchemaError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedRow { field } => write!(f, "a stored row has no usable {}", field),
            Self::EstimateInAMeasuredField { field, basis } => write!(
                f,
                "{} is a measured field and holds a {} figure",
                field, basis
            ),
            Self::MeasurementInAPredictedField { field } => {
                write!(f, "{} is a predicted field and holds a measurement", field)
            }
            Self::AttributionWithoutAMeasurement => {
                write!(
                    f,
                    "nothing was measured, so there is no difference to attribute"
                )
            }
            Self::MeasurementWithoutAnAttribution => write!(
                f,
                "a prediction was measured and the difference is not attributed"
            ),
            Self::UnsourcedFigure { field } => write!(f, "{} carries no source", field),
        }
    }
}

impl std::error::Error for SchemaError {}

/// One claim about what a stage would cost, against what it cost.
///
/// Every row is **one claim**, not one run: `six-round symbolic build, peak RSS` and
/// `six-round symbolic build, elapsed` are separate rows because they were predicted separately,
/// missed separately, and are attributed separately.
#[derive(Clone, Debug, PartialEq)]
pub struct CostRow {
    /// Schema version.
    pub schema: u32,

    /// What was predicted, short enough for a table: `six-round symbolic build, peak RSS`.
    ///
    /// With `algorithm` and `subject`, the row's identity. See [`Self::key`].
    pub claim: String,

    /// The algorithm: `f4`, `resultant-elimination`, `univariate-cico`, `fglm`, `fftmul`.
    pub algorithm: String,

    /// How the problem was posed to it: `full-width grevlex`, `bivariate CICO`, `synthetic pairs`.
    pub formulation: String,

    /// What it was run on: a registered row's id, a corpus name, or a synthetic family.
    pub subject: String,

    /// Input size and structural parameters, as named integers: `n = 20`, `order = 1458`.
    pub parameters: Vec<(String, i128)>,

    /// The degree the solve reached, where a degree describes it.
    pub solving_degree: Option<usize>,

    /// The largest intermediate matrix or polynomial.
    pub largest_intermediate: Option<Intermediate>,

    /// Work counts: determinants, samples, multiply-subtracts, monomials.
    pub work: Vec<(String, i128)>,

    /// Peak **estimated** storage: an accounting of named structures at `count x size_of`.
    ///
    /// Never a measurement. #237's point is that this quantity accounted 186 MB inside a 13 996 MB
    /// process, so it is an estimate of *one allocation* and not a model of a process.
    pub peak_estimated_bytes: Option<Figure<u64>>,

    /// Measured peak **resident** set size: touched pages, from `VmHWM` or `/usr/bin/time -v`.
    pub measured_peak_resident_bytes: Option<Figure<u64>>,

    /// Measured peak bytes **allocated**, from a tracking allocator inside the process.
    ///
    /// **A separate column from [`Self::measured_peak_resident_bytes`] and not comparable with it.**
    /// #237: 21 674 MB allocated against 13 996 MB resident, because one `VecDeque` reservation of
    /// 20 480 MiB was ~60% never written.
    pub measured_peak_allocated_bytes: Option<Figure<u64>>,

    /// Per-stage runtime, as the run reported it.
    pub stage_runtimes: Vec<(String, Figure<Duration>)>,

    /// Total runtime.
    pub measured_runtime: Option<Figure<Duration>>,

    /// What the runtime was predicted to be, before anyone measured it.
    pub predicted_runtime: Option<Figure<Duration>>,

    /// What the peak storage was predicted to be.
    pub predicted_peak_bytes: Option<Figure<u64>>,

    /// A predicted quantity that is neither a time nor a byte count.
    pub predicted_quantity: Option<Quantity>,

    /// The measurement of [`Self::predicted_quantity`], in the same unit.
    pub measured_quantity: Option<Quantity>,

    /// Why predicted and measured differ. [`Attribution::Unexplained`] is a legal answer.
    pub attribution: Attribution,

    /// Which stage, and which structure inside it, bound the run.
    pub limiting_stage: LimitingStage,

    /// What the next size up is projected to cost.
    pub next_size: Option<NextSizeProjection>,

    /// Where the row's figures are published: a document section, or an issue.
    pub source: String,

    /// The machine, build and commit the measurements were taken on.
    ///
    /// A transcribed row carries whatever its source document states. An empty `commit` means the
    /// document did not state one, which is a fact about the document.
    pub environment: Environment,

    /// The command that reproduces it, where one does.
    pub reproduce: String,
}

impl CostRow {
    /// The current schema version.
    pub const SCHEMA: u32 = 1;

    /// A row with its identity and its source, and nothing claimed yet.
    ///
    /// Starts at [`Attribution::NoMeasurementYet`] and [`LimitingStage::NotEstablished`], which are
    /// the honest states before anything is added.
    pub fn new(
        claim: impl Into<String>,
        algorithm: impl Into<String>,
        subject: impl Into<String>,
        source: impl Into<String>,
    ) -> Self {
        Self {
            schema: Self::SCHEMA,
            claim: claim.into(),
            algorithm: algorithm.into(),
            formulation: String::new(),
            subject: subject.into(),
            parameters: Vec::new(),
            solving_degree: None,
            largest_intermediate: None,
            work: Vec::new(),
            peak_estimated_bytes: None,
            measured_peak_resident_bytes: None,
            measured_peak_allocated_bytes: None,
            stage_runtimes: Vec::new(),
            measured_runtime: None,
            predicted_runtime: None,
            predicted_peak_bytes: None,
            predicted_quantity: None,
            measured_quantity: None,
            attribution: Attribution::NoMeasurementYet,
            limiting_stage: LimitingStage::NotEstablished,
            next_size: None,
            source: source.into(),
            environment: Environment {
                commit: String::new(),
                base_commit: String::new(),
                patch_id: String::new(),
                machine: String::new(),
                cpu: String::new(),
                concurrency: 1,
                build: String::new(),
                policy: String::new(),
            },
            reproduce: String::new(),
        }
    }

    /// The row's identity: algorithm, subject and claim.
    ///
    /// Used to tell a **re-measurement** from a duplicate. A re-measurement shares the key and
    /// differs in `environment.commit`, and both rows stay: that is the append-only rule, and #318
    /// is the row that proves it is needed — the same measurement months apart is 1.2x apart.
    pub fn key(&self) -> String {
        format!("{}|{}|{}", self.algorithm, self.subject, self.claim)
    }

    /// A row emitted from a retained run, carrying **only what the run measured**.
    ///
    /// #334: `RunRecord` and `CostRow` hold the same storage pair, and until now the register got
    /// the second copy only if somebody remembered to transcribe it. This is the adapter, and three
    /// things it deliberately does not do:
    ///
    /// 1. **It fills no predicted field, including [`Self::peak_estimated_bytes`].** That field is
    ///    on the *prediction* side of the schema — [`Self::has_prediction`] counts it, and it is
    ///    the predicted half of the `accounted storage` pair — so emitting the run's frontier
    ///    accounting beside the measured RSS would make the row [`Self::is_complete`], which
    ///    [`Self::check`] then requires an attribution for. The adapter has no basis for one, and a
    ///    defaulted attribution would make every emitted row report that a prediction held. The
    ///    estimate is therefore the one frontier figure a run may not emit; a later pass adds it
    ///    together with the attribution it is claiming.
    /// 2. **It never reads the crossed budget as the limiting structure.** [`LimitingStage::NotEstablished`]
    ///    always. #237 is why: `max_live_nonzeros` was the budget crossed and 88.4% of the peak was
    ///    the symbolic queue, which contains no matrix at all.
    /// 3. **It drops a peak it cannot attribute.** `VmHWM` from a process that ran several rows is
    ///    a ceiling over all of them, so a row only gets one when
    ///    [`RunRecord::measured_peak_is_attributable`] holds. A bound copied into a `measured_`
    ///    field is a bound published as a measurement.
    ///
    /// A **completed** run's `max_pair_degree` is its solving degree; a stopped run's is the degree
    /// it reached, which is a different quantity, so that one is left absent.
    ///
    /// `algorithm` comes from the caller because the record does not carry it — the same run shape
    /// is produced by the F4 route and by resultant elimination. Everything else is derived, and
    /// the derived [`Self::claim`] is stable across re-runs so that [`Self::key`] joins a later
    /// row about the same quantity to this one.
    pub fn from_run(run: &RunRecord, algorithm: impl Into<String>) -> Self {
        let source = format!("research/scoreboard/runs/{}.json", run.run_file_stem());
        let mut row = Self::new(
            format!("{}, cost as run", run.formulation),
            algorithm,
            run.challenge.clone(),
            source.clone(),
        )
        .with_formulation(run.formulation.clone())
        .with_environment(run.environment.clone())
        .with_reproduce(run.reproduce.clone());

        for stage in &run.stages {
            row = row.with_stage(
                stage.stage.name(),
                stage.elapsed,
                "std::time::Instant, as the run recorded it",
                source.clone(),
            );
        }
        if !run.stages.is_empty() {
            row = row.with_measured_runtime(
                run.elapsed(),
                "sum of the run's recorded stages",
                source.clone(),
            );
        }
        if run.measured_peak_is_attributable() {
            let bytes = run
                .measured_peak_resident_bytes
                .expect("attributable implies present");
            row = row.with_measured_resident(bytes as u64, "VmHWM", source.clone());
        }
        if let Some(frontier) = &run.frontier {
            if frontier.completed {
                row = row.with_solving_degree(frontier.max_pair_degree as usize);
            }
            row = row
                .with_largest_intermediate(Intermediate::new(
                    "Macaulay matrix",
                    frontier.max_matrix_columns as i128,
                    "columns",
                ))
                .with_work("pairs reduced", frontier.pairs_reduced as i128)
                .with_work("basis elements added", frontier.elements_added as i128)
                .with_work("peak live nonzeros", frontier.peak_live_nonzeros as i128);
            if let Some(dimension) = frontier.quotient_dimension {
                row = row.with_parameter("quotient dimension", dimension as i128);
            }
        }
        row
    }

    /// Set how the problem was posed.
    pub fn with_formulation(mut self, formulation: impl Into<String>) -> Self {
        self.formulation = formulation.into();
        self
    }

    /// Add a named structural parameter.
    pub fn with_parameter(mut self, name: impl Into<String>, value: i128) -> Self {
        self.parameters.push((name.into(), value));
        self
    }

    /// Set the solving degree.
    pub fn with_solving_degree(mut self, degree: usize) -> Self {
        self.solving_degree = Some(degree);
        self
    }

    /// Set the solving degree from an F4 run, rather than by hand.
    ///
    /// [`Self::solving_degree`] is the field #334 is about: it exists, it is optional, and until
    /// F4 recorded its step degrees the only callers that filled it in were tests passing a
    /// literal. This reads
    /// [`F4Statistics::observed_solving_degree`](crate::grobner::F4Statistics::observed_solving_degree),
    /// so a row carries what the run did.
    ///
    /// Leaves the field `None` for a run that built no matrix, which is the honest reading: no
    /// batch was selected, so no degree was reached.
    pub fn with_solving_degree_from(mut self, statistics: &crate::grobner::F4Statistics) -> Self {
        self.solving_degree = statistics
            .observed_solving_degree()
            .and_then(|degree| usize::try_from(degree).ok());
        self
    }

    /// Set the largest intermediate object.
    pub fn with_largest_intermediate(mut self, intermediate: Intermediate) -> Self {
        self.largest_intermediate = Some(intermediate);
        self
    }

    /// Add a named work count.
    pub fn with_work(mut self, name: impl Into<String>, count: i128) -> Self {
        self.work.push((name.into(), count));
        self
    }

    /// Set the accounted storage estimate.
    pub fn with_estimated_peak(mut self, bytes: Figure<u64>) -> Self {
        self.peak_estimated_bytes = Some(bytes);
        self
    }

    /// Set the measured peak **resident** bytes, stamping the basis as measured here.
    pub fn with_measured_resident(
        mut self,
        bytes: u64,
        instrument: impl Into<String>,
        source: impl Into<String>,
    ) -> Self {
        self.measured_peak_resident_bytes = Some(Figure::measured(bytes, instrument, source));
        self
    }

    /// Set the measured peak **allocated** bytes. A different quantity from the resident peak.
    pub fn with_measured_allocated(
        mut self,
        bytes: u64,
        instrument: impl Into<String>,
        source: impl Into<String>,
    ) -> Self {
        self.measured_peak_allocated_bytes = Some(Figure::measured(bytes, instrument, source));
        self
    }

    /// Add a measured stage runtime.
    pub fn with_stage(
        mut self,
        name: impl Into<String>,
        elapsed: Duration,
        instrument: impl Into<String>,
        source: impl Into<String>,
    ) -> Self {
        self.stage_runtimes
            .push((name.into(), Figure::measured(elapsed, instrument, source)));
        self
    }

    /// Set the measured total runtime.
    pub fn with_measured_runtime(
        mut self,
        elapsed: Duration,
        instrument: impl Into<String>,
        source: impl Into<String>,
    ) -> Self {
        self.measured_runtime = Some(Figure::measured(elapsed, instrument, source));
        self
    }

    /// Set the predicted runtime.
    pub fn with_predicted_runtime(mut self, runtime: Figure<Duration>) -> Self {
        self.predicted_runtime = Some(runtime);
        self
    }

    /// Set the predicted peak storage.
    pub fn with_predicted_peak(mut self, bytes: Figure<u64>) -> Self {
        self.predicted_peak_bytes = Some(bytes);
        self
    }

    /// Set the predicted non-time, non-byte quantity.
    pub fn with_predicted_quantity(mut self, quantity: Quantity) -> Self {
        self.predicted_quantity = Some(quantity);
        self
    }

    /// Set the measurement of that quantity, stamping the basis as measured here.
    pub fn with_measured_quantity(
        mut self,
        name: impl Into<String>,
        unit: impl Into<String>,
        value: i128,
        instrument: impl Into<String>,
        source: impl Into<String>,
    ) -> Self {
        self.measured_quantity = Some(Quantity {
            name: name.into(),
            unit: unit.into(),
            figure: Figure::measured(value, instrument, source),
        });
        self
    }

    /// Set the attribution.
    pub fn with_attribution(mut self, attribution: Attribution) -> Self {
        self.attribution = attribution;
        self
    }

    /// Set the limiting stage.
    pub fn with_limiting_stage(mut self, stage: LimitingStage) -> Self {
        self.limiting_stage = stage;
        self
    }

    /// Set the next-size projection.
    pub fn with_next_size(mut self, projection: NextSizeProjection) -> Self {
        self.next_size = Some(projection);
        self
    }

    /// Set the environment the measurements were taken in.
    pub fn with_environment(mut self, environment: Environment) -> Self {
        self.environment = environment;
        self
    }

    /// Set the reproduction command.
    pub fn with_reproduce(mut self, command: impl Into<String>) -> Self {
        self.reproduce = command.into();
        self
    }

    /// True if anything on this row was measured.
    pub fn has_measurement(&self) -> bool {
        self.measured_runtime.is_some()
            || self.measured_peak_resident_bytes.is_some()
            || self.measured_peak_allocated_bytes.is_some()
            || self.measured_quantity.is_some()
            || !self.stage_runtimes.is_empty()
    }

    /// True if anything on this row was predicted.
    pub fn has_prediction(&self) -> bool {
        self.predicted_runtime.is_some()
            || self.predicted_peak_bytes.is_some()
            || self.predicted_quantity.is_some()
            || self.peak_estimated_bytes.is_some()
    }

    /// True if a prediction here has been checked against a measurement.
    ///
    /// A row with a prediction and no measurement is **legal**, and
    /// [`CostModelBoard::to_markdown`] marks it `open` rather than dropping it: a prediction nobody
    /// has checked is the single most useful thing this register can show.
    pub fn is_complete(&self) -> bool {
        !self.prediction_errors().is_empty()
    }

    /// Every prediction-against-measurement pair on this row, **computed**.
    ///
    /// Four possible pairs, each present only when both of its sides are:
    ///
    /// | pair | predicted | measured |
    /// |---|---|---|
    /// | `runtime` | `predicted_runtime` | `measured_runtime` |
    /// | `peak memory` | `predicted_peak_bytes` | `measured_peak_resident_bytes` |
    /// | `accounted storage` | `peak_estimated_bytes` | `measured_peak_resident_bytes` |
    /// | the quantity's name | `predicted_quantity` | `measured_quantity` |
    ///
    /// `accounted storage` is kept apart from `peak memory` because the two together are #237's
    /// finding: the budget ladder's 16 GB is within 8% of the process it was read against *and*
    /// the accounting inside that process is 75x smaller. One pair alone says the prediction held.
    pub fn prediction_errors(&self) -> Vec<PredictionError> {
        let mut errors = Vec::new();
        if let (Some(predicted), Some(measured)) = (&self.predicted_runtime, &self.measured_runtime)
        {
            errors.extend(PredictionError::between(
                "runtime",
                predicted.value.as_secs_f64(),
                measured.value.as_secs_f64(),
                |seconds| format!("{:.3} s", seconds),
            ));
        }
        if let (Some(predicted), Some(measured)) = (
            &self.predicted_peak_bytes,
            &self.measured_peak_resident_bytes,
        ) {
            errors.extend(PredictionError::between(
                "peak memory",
                predicted.value as f64,
                measured.value as f64,
                bytes_text,
            ));
        }
        if let (Some(estimated), Some(measured)) = (
            &self.peak_estimated_bytes,
            &self.measured_peak_resident_bytes,
        ) {
            errors.extend(PredictionError::between(
                "accounted storage",
                estimated.value as f64,
                measured.value as f64,
                bytes_text,
            ));
        }
        if let (Some(predicted), Some(measured)) =
            (&self.predicted_quantity, &self.measured_quantity)
        {
            let unit = predicted.unit.clone();
            errors.extend(PredictionError::between(
                &predicted.name,
                predicted.figure.value as f64,
                measured.figure.value as f64,
                move |value| format!("{} {}", value, unit),
            ));
        }
        errors
    }

    /// Everything wrong with this row, or `Ok(())`.
    ///
    /// Called by [`CostModelBoard::add`] and by [`Self::from_json`], so a bad row cannot reach the
    /// file and a bad file cannot reach a reader. This is the "self-consistency checked by a test
    /// rather than by the author" requirement, made into code the author cannot skip.
    ///
    /// # Errors
    /// The first [`SchemaError`] found, in the order the fields are declared.
    pub fn check(&self) -> Result<(), SchemaError> {
        let measured: [(&'static str, Option<&FigureBasis>); 4] = [
            (
                "measured_peak_resident_bytes",
                self.measured_peak_resident_bytes.as_ref().map(|f| &f.basis),
            ),
            (
                "measured_peak_allocated_bytes",
                self.measured_peak_allocated_bytes
                    .as_ref()
                    .map(|f| &f.basis),
            ),
            (
                "measured_runtime",
                self.measured_runtime.as_ref().map(|f| &f.basis),
            ),
            (
                "measured_quantity",
                self.measured_quantity.as_ref().map(|q| &q.figure.basis),
            ),
        ];
        for (field, basis) in measured {
            if let Some(basis) = basis {
                if !basis.is_measurement() {
                    return Err(SchemaError::EstimateInAMeasuredField {
                        field,
                        basis: basis.tag(),
                    });
                }
            }
        }
        for (name, figure) in &self.stage_runtimes {
            if !figure.is_measurement() {
                return Err(SchemaError::EstimateInAMeasuredField {
                    field: "stage_runtimes",
                    basis: figure.basis.tag(),
                });
            }
            if figure.source.is_empty() || name.is_empty() {
                return Err(SchemaError::UnsourcedFigure {
                    field: "stage_runtimes",
                });
            }
        }

        let predicted: [(&'static str, Option<&FigureBasis>); 4] = [
            (
                "predicted_runtime",
                self.predicted_runtime.as_ref().map(|f| &f.basis),
            ),
            (
                "predicted_peak_bytes",
                self.predicted_peak_bytes.as_ref().map(|f| &f.basis),
            ),
            (
                "predicted_quantity",
                self.predicted_quantity.as_ref().map(|q| &q.figure.basis),
            ),
            (
                "peak_estimated_bytes",
                self.peak_estimated_bytes.as_ref().map(|f| &f.basis),
            ),
        ];
        for (field, basis) in predicted {
            if basis.is_some_and(FigureBasis::is_measurement) {
                return Err(SchemaError::MeasurementInAPredictedField { field });
            }
        }

        for (field, source) in self.sources() {
            if source.is_empty() {
                return Err(SchemaError::UnsourcedFigure { field });
            }
        }

        if !self.has_measurement() && self.attribution != Attribution::NoMeasurementYet {
            return Err(SchemaError::AttributionWithoutAMeasurement);
        }
        if self.is_complete() && self.attribution == Attribution::NoMeasurementYet {
            return Err(SchemaError::MeasurementWithoutAnAttribution);
        }
        Ok(())
    }

    /// Every figure's source, field by field, for [`Self::check`].
    ///
    /// The field name travels with the source so that the error says which figure is uncited.
    fn sources(&self) -> Vec<(&'static str, &str)> {
        let mut sources: Vec<(&'static str, &str)> = vec![("row", self.source.as_str())];
        for (field, source) in [
            (
                "peak_estimated_bytes",
                self.peak_estimated_bytes
                    .as_ref()
                    .map(|f| f.source.as_str()),
            ),
            (
                "measured_peak_resident_bytes",
                self.measured_peak_resident_bytes
                    .as_ref()
                    .map(|f| f.source.as_str()),
            ),
            (
                "measured_peak_allocated_bytes",
                self.measured_peak_allocated_bytes
                    .as_ref()
                    .map(|f| f.source.as_str()),
            ),
            (
                "measured_runtime",
                self.measured_runtime.as_ref().map(|f| f.source.as_str()),
            ),
            (
                "predicted_runtime",
                self.predicted_runtime.as_ref().map(|f| f.source.as_str()),
            ),
            (
                "predicted_peak_bytes",
                self.predicted_peak_bytes
                    .as_ref()
                    .map(|f| f.source.as_str()),
            ),
            (
                "predicted_quantity",
                self.predicted_quantity
                    .as_ref()
                    .map(|q| q.figure.source.as_str()),
            ),
            (
                "measured_quantity",
                self.measured_quantity
                    .as_ref()
                    .map(|q| q.figure.source.as_str()),
            ),
        ] {
            if let Some(source) = source {
                sources.push((field, source));
            }
        }
        sources
    }

    /// The row as JSON.
    ///
    /// Absent figures are **omitted**, never `null`: "not measured" is not zero, and a key holding
    /// `null` invites being coerced to one. The `derived` object is written for a reader's
    /// convenience and is **not** an input — see [`Self::from_json`].
    pub fn to_json(&self) -> Json {
        let mut fields = vec![
            ("schema", Json::int(self.schema)),
            ("claim", Json::string(&self.claim)),
            ("algorithm", Json::string(&self.algorithm)),
            ("formulation", Json::string(&self.formulation)),
            ("subject", Json::string(&self.subject)),
            (
                "parameters",
                Json::Array(
                    self.parameters
                        .iter()
                        .map(|(name, value)| {
                            Json::object([
                                ("name", Json::string(name)),
                                ("value", Json::int(*value)),
                            ])
                        })
                        .collect(),
                ),
            ),
        ];
        if let Some(degree) = self.solving_degree {
            fields.push(("solving_degree", Json::size(degree)));
        }
        if let Some(intermediate) = &self.largest_intermediate {
            fields.push(("largest_intermediate", intermediate.to_json()));
        }
        if !self.work.is_empty() {
            fields.push((
                "work",
                Json::Array(
                    self.work
                        .iter()
                        .map(|(name, count)| {
                            Json::object([
                                ("name", Json::string(name)),
                                ("count", Json::int(*count)),
                            ])
                        })
                        .collect(),
                ),
            ));
        }
        for (key, figure) in [
            ("peak_estimated_bytes", &self.peak_estimated_bytes),
            (
                "measured_peak_resident_bytes",
                &self.measured_peak_resident_bytes,
            ),
            (
                "measured_peak_allocated_bytes",
                &self.measured_peak_allocated_bytes,
            ),
            ("predicted_peak_bytes", &self.predicted_peak_bytes),
        ] {
            if let Some(figure) = figure {
                fields.push((key, figure.to_json()));
            }
        }
        if !self.stage_runtimes.is_empty() {
            fields.push((
                "stage_runtimes",
                Json::Array(
                    self.stage_runtimes
                        .iter()
                        .map(|(name, figure)| {
                            Json::object([
                                ("name", Json::string(name)),
                                ("elapsed", figure.to_json()),
                            ])
                        })
                        .collect(),
                ),
            ));
        }
        if let Some(runtime) = &self.measured_runtime {
            fields.push(("measured_runtime", runtime.to_json()));
        }
        if let Some(runtime) = &self.predicted_runtime {
            fields.push(("predicted_runtime", runtime.to_json()));
        }
        if let Some(quantity) = &self.predicted_quantity {
            fields.push(("predicted_quantity", quantity.to_json()));
        }
        if let Some(quantity) = &self.measured_quantity {
            fields.push(("measured_quantity", quantity.to_json()));
        }
        fields.push(("attribution", self.attribution.to_json()));
        fields.push(("limiting_stage", Json::string(self.limiting_stage.tag())));
        if let Some(projection) = &self.next_size {
            fields.push(("next_size", projection.to_json()));
        }
        fields.push(("source", Json::string(&self.source)));
        fields.push(("environment", self.environment.to_json()));
        fields.push(("reproduce", Json::string(&self.reproduce)));
        // **No error column is stored.** Not even under a hedged name: a number in the file is a
        // number someone will quote, and the file would then also have to be rewritten whenever
        // the renderer's precision changed -- in an append-only history, rewriting everything is
        // the operation the contract exists to forbid. The error is computed by
        // `prediction_errors` from the fields above, which are inputs.
        fields.push((
            "prediction_error",
            Json::string(
                "NOT STORED. Compute it from the predicted and measured fields: see \
                 CostRow::prediction_errors.",
            ),
        ));
        Json::object(fields)
    }

    /// A row read back from JSON, checked.
    ///
    /// **`derived` is ignored.** The error column is recomputed from the predicted and measured
    /// fields on every load, so a hand-edited or stale `derived` object cannot be read as a
    /// finding.
    ///
    /// # Errors
    /// [`SchemaError`], naming the field.
    pub fn from_json(value: &Json) -> Result<Self, SchemaError> {
        let text = |key: &'static str| -> Result<String, SchemaError> {
            Ok(value
                .get(key)
                .and_then(Json::as_str)
                .ok_or(SchemaError::MalformedRow { field: key })?
                .to_string())
        };
        let pairs = |key: &str| -> Vec<(String, i128)> {
            value
                .get(key)
                .map(|list| {
                    list.items()
                        .iter()
                        .filter_map(|entry| {
                            Some((
                                entry.get("name").and_then(Json::as_str)?.to_string(),
                                entry
                                    .get("value")
                                    .or_else(|| entry.get("count"))?
                                    .as_int()?,
                            ))
                        })
                        .collect()
                })
                .unwrap_or_default()
        };
        let figure_bytes = |key: &str| -> Result<Option<Figure<u64>>, SchemaError> {
            value.get(key).map(Figure::<u64>::from_json).transpose()
        };

        // Identity first, so that a row missing its claim says so rather than reporting whichever
        // field the reader happened to reach first. Same rule as `external::board`.
        let claim = text("claim")?;
        let algorithm = text("algorithm")?;
        let subject = text("subject")?;
        let limiting_tag = text("limiting_stage")?;
        let row = Self {
            schema: value.get("schema").and_then(Json::as_int).unwrap_or(1) as u32,
            claim,
            algorithm,
            formulation: value
                .get("formulation")
                .and_then(Json::as_str)
                .unwrap_or_default()
                .to_string(),
            subject,
            parameters: pairs("parameters"),
            solving_degree: value
                .get("solving_degree")
                .and_then(Json::as_int)
                .map(|d| d as usize),
            largest_intermediate: value
                .get("largest_intermediate")
                .map(Intermediate::from_json),
            work: pairs("work"),
            peak_estimated_bytes: figure_bytes("peak_estimated_bytes")?,
            measured_peak_resident_bytes: figure_bytes("measured_peak_resident_bytes")?,
            measured_peak_allocated_bytes: figure_bytes("measured_peak_allocated_bytes")?,
            stage_runtimes: value
                .get("stage_runtimes")
                .map(|stages| {
                    stages
                        .items()
                        .iter()
                        .map(|stage| {
                            let name = stage
                                .get("name")
                                .and_then(Json::as_str)
                                .unwrap_or_default()
                                .to_string();
                            let figure = Figure::<Duration>::from_json(
                                stage.get("elapsed").ok_or(SchemaError::MalformedRow {
                                    field: "stage_runtimes.elapsed",
                                })?,
                            )?;
                            Ok((name, figure))
                        })
                        .collect::<Result<Vec<_>, SchemaError>>()
                })
                .transpose()?
                .unwrap_or_default(),
            measured_runtime: value
                .get("measured_runtime")
                .map(Figure::<Duration>::from_json)
                .transpose()?,
            predicted_runtime: value
                .get("predicted_runtime")
                .map(Figure::<Duration>::from_json)
                .transpose()?,
            predicted_quantity: value
                .get("predicted_quantity")
                .map(Quantity::from_json)
                .transpose()?,
            measured_quantity: value
                .get("measured_quantity")
                .map(Quantity::from_json)
                .transpose()?,
            predicted_peak_bytes: figure_bytes("predicted_peak_bytes")?,
            attribution: Attribution::from_json(value.get("attribution").ok_or(
                SchemaError::MalformedRow {
                    field: "attribution",
                },
            )?)?,
            limiting_stage: LimitingStage::from_tag(&limiting_tag).ok_or(
                SchemaError::MalformedRow {
                    field: "limiting_stage",
                },
            )?,
            next_size: value
                .get("next_size")
                .map(NextSizeProjection::from_json)
                .transpose()?,
            source: text("source")?,
            environment: environment_from_json(value.get("environment").ok_or(
                SchemaError::MalformedRow {
                    field: "environment",
                },
            )?),
            reproduce: value
                .get("reproduce")
                .and_then(Json::as_str)
                .unwrap_or_default()
                .to_string(),
        };
        row.check()?;
        Ok(row)
    }
}

/// An [`Environment`] read back from the form [`Environment::to_json`] writes.
///
/// Tolerant by design, for the reason `external::board` gives: an environment recorded incompletely
/// is still better evidence than no row.
fn environment_from_json(value: &Json) -> Environment {
    let text = |key: &str| {
        value
            .get(key)
            .and_then(Json::as_str)
            .unwrap_or_default()
            .to_string()
    };
    Environment {
        commit: text("commit"),
        base_commit: text("base_commit"),
        patch_id: text("patch_id"),
        machine: text("machine"),
        cpu: text("cpu"),
        concurrency: value
            .get("concurrency")
            .and_then(Json::as_int)
            .unwrap_or(1)
            .max(1) as usize,
        build: text("build"),
        policy: text("policy"),
    }
}

/// The register: rows in the order recorded, with the renderers.
#[derive(Clone, Debug, Default)]
pub struct CostModelBoard {
    rows: Vec<CostRow>,
}

impl CostModelBoard {
    /// An empty register.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a row, **appending**.
    ///
    /// A row whose [`CostRow::key`] already appears is still appended: that is a re-measurement,
    /// and keeping both is the point. There is no update path and no `remove`, which is how the
    /// append-only contract is enforced rather than merely documented.
    ///
    /// # Errors
    /// [`SchemaError`] from [`CostRow::check`]. A row that cannot be stated cannot be stored.
    pub fn add(&mut self, row: CostRow) -> Result<(), SchemaError> {
        row.check()?;
        self.rows.push(row);
        Ok(())
    }

    /// The rows, in insertion order. **Position is evidence**; nothing sorts this.
    pub fn rows(&self) -> &[CostRow] {
        &self.rows
    }

    /// Every row for one claim key, oldest first: the re-measurement trail.
    pub fn history_of(&self, key: &str) -> Vec<&CostRow> {
        self.rows.iter().filter(|row| row.key() == key).collect()
    }

    /// Rows carrying a prediction nobody has checked yet.
    ///
    /// The register's most useful view, since §10.1's finding is precisely that an unchecked
    /// prediction is the one most likely to be wrong by an order of magnitude.
    pub fn open_predictions(&self) -> Vec<&CostRow> {
        self.rows
            .iter()
            .filter(|row| row.has_prediction() && !row.is_complete())
            .collect()
    }

    /// Load an accumulated history: `{"rows": [...]}` as [`Self::to_json`] writes it.
    ///
    /// # Errors
    /// [`SchemaError`] from any malformed or inconsistent row.
    pub fn load(history: &Json) -> Result<Self, SchemaError> {
        let entries = history
            .get("rows")
            .ok_or(SchemaError::MalformedRow { field: "rows" })?;
        let mut board = Self::new();
        for entry in entries.items() {
            board.rows.push(CostRow::from_json(entry)?);
        }
        Ok(board)
    }

    /// The register as JSON, with the history contract written into it.
    pub fn to_json(&self) -> Json {
        Json::object([
            ("schema", Json::int(CostRow::SCHEMA)),
            ("contract", Json::string(COST_MODEL_HISTORY_CONTRACT)),
            ("row_count", Json::size(self.rows.len())),
            (
                "rows",
                Json::Array(self.rows.iter().map(CostRow::to_json).collect()),
            ),
        ])
    }

    /// The register as Markdown, grouped by algorithm.
    ///
    /// Generated rather than hand-maintained, for the reason `SCOREBOARD.md` and `COMPETITIVE.md`
    /// are: §10.1's table lived only as prose inside one milestone document, so the next milestone
    /// could not check its own predictions against it.
    pub fn to_markdown(&self) -> String {
        let mut out = String::new();
        out.push_str(
            "# Cost model: predicted against measured, with the difference attributed\n\n",
        );
        out.push_str(
            "Generated by `cargo run --release --example cost_model`. Do not edit: regenerate it.\n\n\
             Every figure carries a **basis** — `measured`, `fitted`, `predicted` or \
             `extrapolated` — because the failure this register exists to prevent is a prediction \
             quoted with the confidence of a measurement. A `measured` column holds only what an \
             instrument read; a row reporting an estimate there is a schema error and does not \
             load. **Peak allocated and peak resident are separate columns** and are not \
             comparable. Prediction error is computed from the predicted and measured columns and \
             is never authored. The history is **append-only**: a re-measurement is a new row with \
             a new commit, never an edit.\n\n",
        );
        out.push_str(
            "The register is **curated**, not a second copy of the scoreboard (#532). Every row \
             is here because somebody made a claim about what a stage would cost; \
             `research/scoreboard/` is the complete measured record. A row may be *emitted* from a \
             retained run — `--from-runs <run-file-stem>`, one named run at a time, which fills \
             only the measured half — and there is deliberately no way to ask for all of them.\n\n",
        );

        if self.rows.is_empty() {
            out.push_str("_No rows yet._\n");
            return out;
        }

        let mut by_algorithm: BTreeMap<&str, Vec<&CostRow>> = BTreeMap::new();
        for row in &self.rows {
            by_algorithm
                .entry(row.algorithm.as_str())
                .or_default()
                .push(row);
        }

        for (algorithm, rows) in &by_algorithm {
            let _ = writeln!(out, "## {}\n", algorithm);
            let _ = writeln!(
                out,
                "| claim | subject | predicted | measured | error | attribution | limiting stage | next size | source |"
            );
            let _ = writeln!(out, "|---|---|---|---|---|---|---|---|---|");
            for row in rows {
                let _ = writeln!(
                    out,
                    "| {} | `{}` | {} | {} | {} | {} | `{}` | {} | {} |",
                    row.claim,
                    row.subject,
                    predicted_cell(row),
                    measured_cell(row),
                    error_cell(row),
                    row.attribution.detail(),
                    row.limiting_stage,
                    next_size_cell(row),
                    row.source,
                );
            }
            out.push('\n');
        }

        let open = self.open_predictions();
        if !open.is_empty() {
            out.push_str("## Open predictions — stated, not yet measured\n\n");
            out.push_str(
                "Visibly incomplete rather than absent. §10.1's finding is that every M24 \
                 prediction about a quantity nobody had measured was wrong, three of the four by \
                 more than an order of magnitude, so this is the list that matters most.\n\n",
            );
            let _ = writeln!(out, "| claim | subject | predicted | basis | source |");
            let _ = writeln!(out, "|---|---|---|---|---|");
            for row in &open {
                let _ = writeln!(
                    out,
                    "| {} | `{}` | {} | {} | {} |",
                    row.claim,
                    row.subject,
                    predicted_cell(row),
                    predicted_basis_cell(row),
                    row.source,
                );
            }
            out.push('\n');
        }

        let unexplained: Vec<&CostRow> = self
            .rows
            .iter()
            .filter(|row| matches!(row.attribution, Attribution::Unexplained { .. }))
            .collect();
        if !unexplained.is_empty() {
            out.push_str("## Unexplained — measured, reproducible, cause unknown\n\n");
            out.push_str(
                "Carried rather than resolved. A ratio that spans one of these carries a \
                 systematic belonging to neither side of it.\n\n",
            );
            let _ = writeln!(out, "| claim | subject | what is unexplained | source |");
            let _ = writeln!(out, "|---|---|---|---|");
            for row in &unexplained {
                let _ = writeln!(
                    out,
                    "| {} | `{}` | {} | {} |",
                    row.claim,
                    row.subject,
                    row.attribution.detail(),
                    row.source
                );
            }
            out.push('\n');
        }

        out
    }
}

/// The predicted side of a row, or an em dash.
fn predicted_cell(row: &CostRow) -> String {
    let mut parts = Vec::new();
    if let Some(runtime) = &row.predicted_runtime {
        parts.push(format!("{} elapsed", duration_text(runtime.value)));
    }
    if let Some(bytes) = &row.predicted_peak_bytes {
        parts.push(format!("{} peak", bytes_text(bytes.value as f64)));
    }
    if let Some(bytes) = &row.peak_estimated_bytes {
        parts.push(format!("{} accounted", bytes_text(bytes.value as f64)));
    }
    if let Some(quantity) = &row.predicted_quantity {
        parts.push(format!(
            "{}: {} {}",
            quantity.name, quantity.figure.value, quantity.unit
        ));
    }
    if parts.is_empty() {
        "—".to_string()
    } else {
        parts.join("; ")
    }
}

/// The bases behind a row's predicted figures, so the cell above is never read bare.
fn predicted_basis_cell(row: &CostRow) -> String {
    let mut parts: Vec<String> = Vec::new();
    for basis in [
        row.predicted_runtime.as_ref().map(|f| &f.basis),
        row.predicted_peak_bytes.as_ref().map(|f| &f.basis),
        row.peak_estimated_bytes.as_ref().map(|f| &f.basis),
        row.predicted_quantity.as_ref().map(|q| &q.figure.basis),
    ]
    .into_iter()
    .flatten()
    {
        let detail = basis.detail();
        if !parts.contains(&detail) {
            parts.push(detail);
        }
    }
    if parts.is_empty() {
        "—".to_string()
    } else {
        parts.join("; ")
    }
}

/// The measured side of a row, or an em dash. Resident and allocated are labelled, always.
fn measured_cell(row: &CostRow) -> String {
    let mut parts = Vec::new();
    if let Some(runtime) = &row.measured_runtime {
        parts.push(format!("{} elapsed", duration_text(runtime.value)));
    }
    if let Some(bytes) = &row.measured_peak_resident_bytes {
        parts.push(format!("{} resident", bytes_text(bytes.value as f64)));
    }
    if let Some(bytes) = &row.measured_peak_allocated_bytes {
        parts.push(format!("{} allocated", bytes_text(bytes.value as f64)));
    }
    if let Some(quantity) = &row.measured_quantity {
        parts.push(format!(
            "{}: {} {}",
            quantity.name, quantity.figure.value, quantity.unit
        ));
    }
    if parts.is_empty() {
        "— _nothing measured_".to_string()
    } else {
        parts.join("; ")
    }
}

/// The derived error cell, or a note saying which side of the division is missing.
///
/// `_open_` and `_no numeric prediction_` are different states and the table says which: the first
/// is a prediction waiting to be checked and the second is a measurement nobody predicted.
fn error_cell(row: &CostRow) -> String {
    let errors = row.prediction_errors();
    if errors.is_empty() {
        return if row.has_prediction() {
            "_open_".to_string()
        } else {
            "_no numeric prediction_".to_string()
        };
    }
    errors
        .iter()
        .map(|error| format!("{}: **{}**", error.quantity, factor_text(error.factor)))
        .collect::<Vec<String>>()
        .join("; ")
}

/// The next-size projection cell, carrying how far past its evidence it reaches.
fn next_size_cell(row: &CostRow) -> String {
    let Some(projection) = &row.next_size else {
        return "—".to_string();
    };
    let mut parts = vec![projection.next.clone()];
    if let Some(runtime) = &projection.runtime {
        let mut cell = duration_text(runtime.value);
        if let Some(times) = runtime.basis.times_past_the_evidence() {
            let _ = write!(cell, " ({:.1}x past the evidence)", times);
        }
        parts.push(cell);
    }
    if let Some(bytes) = &projection.peak_bytes {
        parts.push(bytes_text(bytes.value as f64));
    }
    parts.join(": ")
}

/// A byte count in the largest unit that keeps it readable.
///
/// **GiB and MiB, spelled out.** The source documents use `MB` for both decimal and binary
/// megabytes, and the stored figure is exact bytes either way; rendering it in an ambiguous unit
/// would reintroduce the conflation one column over from where the basis label removes it.
///
/// Takes `f64` because [`PredictionError`] renders both sides of a ratio through it.
fn bytes_text(bytes: f64) -> String {
    const GIB: f64 = (1u64 << 30) as f64;
    const MIB: f64 = (1u64 << 20) as f64;
    if bytes >= GIB {
        format!("{:.2} GiB", bytes / GIB)
    } else if bytes >= MIB {
        format!("{:.1} MiB", bytes / MIB)
    } else {
        format!("{:.0} B", bytes)
    }
}

/// A ratio at a precision that does not round it away.
///
/// `{:.2}` turns the 0.0013x of 13x-against-four-orders-of-magnitude into `0.00x`, which reports
/// the opposite of the finding.
fn factor_text(factor: f64) -> String {
    let magnitude = factor.abs();
    if magnitude >= 100.0 {
        format!("{:.0}x", factor)
    } else if magnitude >= 1.0 {
        format!("{:.2}x", factor)
    } else if magnitude >= 0.01 {
        format!("{:.3}x", factor)
    } else {
        format!("{:.2e}x", factor)
    }
}

/// A duration in the largest unit that keeps it readable.
fn duration_text(elapsed: Duration) -> String {
    let seconds = elapsed.as_secs_f64();
    if seconds >= 86_400.0 {
        format!("{:.2} d", seconds / 86_400.0)
    } else if seconds >= 3_600.0 {
        format!("{:.2} h", seconds / 3_600.0)
    } else if seconds >= 60.0 {
        format!("{:.2} min", seconds / 60.0)
    } else if seconds >= 1.0 {
        format!("{:.3} s", seconds)
    } else {
        // Three decimals, not one: the figures this register divides are millisecond-scale
        // determinant costs (2.868 ms against 3.439 ms is #318) and rounding them to 2.9 and 3.4
        // would print a ratio the numbers in the cells cannot produce.
        format!("{:.3} ms", seconds * 1e3)
    }
}

/// The retained runs a cost-model emission names, and the repeats it could not address.
///
/// Returned by [`select_runs_by_stem`].
#[derive(Debug)]
pub struct SelectedRuns<'a> {
    /// One run per named stem: the one `research/scoreboard/runs/<stem>.json` holds.
    pub runs: Vec<&'a RunRecord>,
    /// Named stems that cover more than one retained run, with how many: `(stem, count)`.
    ///
    /// Surfaced rather than swallowed. Only the last run written under a stem is in the record
    /// tree, so the earlier ones have no file to cite and no row is emitted for them.
    pub shadowed: Vec<(String, usize)>,
}

/// Why a run selection was refused.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RunSelectionError {
    /// No run was named, and there is no sweep to fall back on.
    NoSelector,
    /// A named stem matches no retained run.
    UnknownRun {
        /// The stem as given.
        stem: String,
    },
}

impl std::fmt::Display for RunSelectionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoSelector => f.write_str(
                "no run named. The register is curated: it holds claims about what a stage was \
                 predicted to cost, so a row is emitted for a run whose prediction wants its \
                 measurement, one run at a time",
            ),
            Self::UnknownRun { stem } => {
                write!(f, "no retained run is written under the stem {:?}", stem)
            }
        }
    }
}

/// The retained runs named by their record-file stems, one row's worth each.
///
/// **There is deliberately no way to ask for all of them.** #532 settled what this register is:
/// the module doc's "what a stage was predicted to cost, what it cost, and why those differ", a
/// board about prediction accuracy rather than a second copy of the scoreboard. A row emitted from
/// a run carries no prediction, so [`CostModelBoard::open_predictions`] — the register's most
/// useful view — ignores it, while [`CostModelBoard::to_markdown`] still renders it in the
/// per-algorithm table. Sweeping the retained history would therefore add nothing to the view the
/// register exists for and dilute its table four to one.
///
/// The second reason **used to be** that a row per run is not expressible in the record tree:
/// identity was `challenge--formulation--commit`, so a re-run of one problem at one commit
/// replaced its predecessor's record file, and sixteen committed runs shared a stem with another —
/// the three `poseidon-t2-rf4-rp0-planted` runs at `86aaa53` measured 369.4 ms, 360.9 ms and
/// 369.3 ms in Gröbner, and only the last was in the one file all three would have cited.
///
/// **#540 closed that.** [`RunRecord::run_file_stem`] now carries [`RunRecord::short_digest`], so
/// every retained run has its own file and a `source` always holds the figures it cites.
/// [`SelectedRuns::shadowed`] is kept and is now empty on the committed history: it can only fire
/// for records that are byte-identical, which are interchangeable rather than shadowed. So this
/// function's refusal to sweep rests on the first reason alone, which is a judgement about what
/// the register is for; revisiting it is #532's decision and not a consequence of #540.
///
/// # Errors
/// [`RunSelectionError::NoSelector`] if `stems` is empty, [`RunSelectionError::UnknownRun`] if a
/// stem matches no retained run — a mistyped selector that emitted nothing would read as
/// "already up to date".
pub fn select_runs_by_stem<'a>(
    runs: &'a [RunRecord],
    stems: &[String],
) -> Result<SelectedRuns<'a>, RunSelectionError> {
    if stems.is_empty() {
        return Err(RunSelectionError::NoSelector);
    }
    let mut selection = SelectedRuns {
        runs: Vec::new(),
        shadowed: Vec::new(),
    };
    let mut named: Vec<&str> = Vec::new();
    for stem in stems {
        // A stem named twice is selected once, so a repeated selector cannot double-append.
        if named.contains(&stem.as_str()) {
            continue;
        }
        named.push(stem.as_str());
        let matching: Vec<&RunRecord> = runs
            .iter()
            .filter(|run| &run.run_file_stem() == stem)
            .collect();
        let Some(addressable) = matching.last().copied() else {
            return Err(RunSelectionError::UnknownRun { stem: stem.clone() });
        };
        if matching.len() > 1 {
            selection.shadowed.push((stem.clone(), matching.len()));
        }
        selection.runs.push(addressable);
    }
    Ok(selection)
}

/// Every distinct record-file stem in a retained run set, in first-appearance order, with how many
/// runs share it.
///
/// A count above one is a run the record tree cannot cite, which is what makes the stem set the
/// honest measure of how much of the history is addressable. Since #540 put the record's digest in
/// the stem, every count on the committed history is **one**, and a count above one could only mean
/// two byte-identical records — interchangeable, so one file holding both is the right answer.
/// `test_every_retained_run_is_addressable_by_its_own_record_file` is where that is asserted.
///
/// Linear scan rather than a map because first-appearance order is the history's order and the set
/// is a few dozen entries.
pub fn retained_run_stems(runs: &[RunRecord]) -> Vec<(String, usize)> {
    let mut stems: Vec<(String, usize)> = Vec::new();
    for run in runs {
        let stem = run.run_file_stem();
        match stems.iter_mut().find(|(known, _)| *known == stem) {
            Some((_, count)) => *count += 1,
            None => stems.push((stem, 1)),
        }
    }
    stems
}

/// The rows transcribed from the documents that published them, in the order their claims were
/// made.
///
/// **Every figure here is cited and none is invented.** The sources are
/// `MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md` §10.1, `docs/research/f4-resource-scaling.md` §9
/// (#237), and `docs/research/resultant-elimination.md` §6.8 (#243) and §6.9 (#289, #318, #319).
/// A transcribed row carries the environment its source document states; an **empty `commit`**
/// means the document did not state one, which is a fact about the document and not a gap to be
/// filled in.
///
/// Two conventions the transcription had to settle, because the documents are not uniform:
///
/// - `MB` means **MiB** wherever a figure was cross-checked against `/proc` (#237's 13 996 MB is
///   `14 336 724 kB`), and decimal **MB** where a plan quoted a round number (§7.4's "~68 MB",
///   against which 57.0 GB is the documented 838x). Each row's figure is the one its own source
///   states.
/// - A figure that was a *measurement* when taken and is quoted as the *expectation* for a later
///   run enters as [`FigureBasis::Predicted`] with the earlier measurement named as its model.
///   That is what #318 and #319 are: a measurement disagreeing with a measurement, which is only
///   a prediction error once the earlier figure is being relied on.
pub fn transcribed_rows() -> Vec<CostRow> {
    /// A mebibyte, for the figures that were read against `/proc`.
    const MIB: u64 = 1 << 20;

    let m24 = "MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md 10.1";
    let f4_scaling = "docs/research/f4-resource-scaling.md 9.2 (#237)";
    let f4_scaling_d4 = "docs/research/f4-resource-scaling.md 9.3 (#237)";
    let build = "docs/research/resultant-elimination.md 6.8 (#243)";
    let law = "docs/research/resultant-elimination.md 6.9 (#289)";
    let collecting = "docs/research/resultant-elimination.md 6.12 (#243, merged)";
    let resolved = "docs/research/resultant-elimination.md 6.13 (#318, #319)";

    // The documents state the machine and the policy and never a commit. Recorded as stated.
    let workstation = |policy: &str| Environment {
        commit: String::new(),
        base_commit: String::new(),
        patch_id: String::new(),
        machine: "workstation".to_string(),
        cpu: "64 logical".to_string(),
        concurrency: 1,
        build: "release, -C target-cpu=x86-64-v3".to_string(),
        policy: policy.to_string(),
    };

    vec![
        // ---- M24 10.1, the univariate route ----
        CostRow::new(
            "mean roots per family, which sets families per witness at p / roots",
            "univariate-cico",
            "poseidon31-cico, univariate route, k = 1",
            m24,
        )
        .with_formulation("univariate CICO, one family end to end")
        .with_parameter("families enumerated", 17_838)
        .with_parameter("roots examined", 17_901)
        .with_predicted_quantity(Quantity {
            name: "mean roots per family".to_string(),
            unit: "per 10 000".to_string(),
            figure: Figure::predicted(
                10_000,
                "one root per family in expectation, from the random-polynomial heuristic",
                "docs/research/graeffe-root-finding.md 9.3",
            ),
        })
        .with_measured_quantity(
            "mean roots per family",
            "per 10 000",
            9_997,
            "17 838 families enumerated; chi-squared independence inside +/-3 sigma",
            m24,
        )
        .with_attribution(Attribution::PredictionHeld)
        .with_limiting_stage(LimitingStage::RootFinding)
        .with_environment(workstation("tools/benchlock.sh")),
        CostRow::new(
            "univariate route, cost per family",
            "univariate-cico",
            "poseidon31-cico, univariate route, k = 1",
            m24,
        )
        .with_formulation("univariate CICO, one family end to end")
        .with_predicted_runtime(Figure::predicted(
            Duration::from_secs(120),
            "9.2's per-family stage budget",
            "docs/research/graeffe-root-finding.md 9.2",
        ))
        .with_measured_runtime(
            Duration::from_millis(15_200),
            "wall clock, 12 + 0.09 + 3.11 s of stages",
            m24,
        )
        .with_attribution(Attribution::StageNotInScope {
            stage: "a ~100 s r = 2^24 subgroup scan belonging to Zeebra's single-root descent, \
                    which a loop filtering ~1 root does not run and whose W_check the published \
                    paper itself calls negligible"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::RootFinding)
        .with_environment(workstation("tools/benchlock.sh")),
        CostRow::new(
            "advantage over the published 7 h on 96 GPUs",
            "univariate-cico",
            "poseidon31-cico, univariate route, k = 1",
            m24,
        )
        .with_formulation("univariate CICO against the published attack")
        .with_parameter("published GPU-hours", 672)
        .with_parameter("implied per-GPU factor over one core", 13_500)
        .with_predicted_quantity(Quantity {
            name: "advantage over the published figure".to_string(),
            unit: "x".to_string(),
            figure: Figure::predicted(
                10_000,
                "\"four orders of magnitude after any plausible GPU factor\"",
                "MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md 5.4",
            ),
        })
        .with_measured_quantity(
            "advantage over the published figure",
            "x",
            13,
            "~1 036 core-years against 672 GPU-hours at a 10^3 per-GPU factor",
            m24,
        )
        .with_attribution(Attribution::IncomparableFigures {
            detail: "two separable errors: core-years divided by a wall clock, and the \
                     subgroup-scan stage charged to every family. 43x at 10^2.5 and 135x at 10^2, \
                     so the gap is inside two orders for any per-GPU factor above ~140"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::RootFinding)
        .with_environment(workstation("tools/benchlock.sh")),
        CostRow::new(
            "family count under round reduction",
            "univariate-cico",
            "poseidon31-cico, the round ladder",
            m24,
        )
        .with_formulation("univariate CICO at reduced R_F and R_P")
        .with_parameter("span of delta across the ladder", 6_561)
        .with_measured_quantity(
            "mean roots per family across the round ladder",
            "per 10 000",
            10_000,
            "the full round ladder; delta spans 6 561x and the mean root count never leaves 1.0",
            "MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md 6.4",
        )
        .with_attribution(Attribution::WrongQuantity {
            predicted_quantity: "a family count falling with R_F and R_P (6.3's assumption)"
                .to_string(),
            actual_quantity: "p / (roots per family), which contains neither R_F nor R_P"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::RootFinding)
        .with_environment(workstation("tools/benchlock.sh")),
        CostRow::new(
            "the published per-family stage ordering",
            "univariate-cico",
            "poseidon31-cico, univariate route, k = 1",
            m24,
        )
        .with_formulation("univariate CICO, one family end to end")
        .with_measured_quantity(
            "construction's share of the per-family cost",
            "basis points",
            7_700,
            "per-stage timings: 77% construction, 23% root finding, microseconds checking",
            m24,
        )
        .with_attribution(Attribution::PredictionHeld)
        .with_limiting_stage(LimitingStage::RootFinding)
        .with_environment(workstation("tools/benchlock.sh")),
        // ---- M24 10.1, the two predictions about already-measured stages ----
        CostRow::new(
            "parallel efficiency of the determinant sweep to 32 cores",
            "resultant-elimination",
            "Sylvester determinants, 32 cores",
            m24,
        )
        .with_formulation("sample determinants over a worker pool")
        .with_parameter("workers", 32)
        .with_predicted_quantity(Quantity {
            name: "parallel efficiency at 32 workers".to_string(),
            unit: "basis points".to_string(),
            figure: Figure::predicted(
                10_000,
                "\"a constant factor bounded by core count\"",
                "MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md 7.3",
            ),
        })
        .with_measured_quantity(
            "parallel efficiency at 32 workers",
            "basis points",
            9_200,
            "the 32-core sweep, 92-95% efficient; the low end is recorded",
            m24,
        )
        .with_attribution(Attribution::PredictionHeld)
        .with_limiting_stage(LimitingStage::DeterminantEvaluation)
        .with_environment(workstation("tools/benchlock.sh, 32 workers")),
        CostRow::new(
            "fftmul's reported ceiling is checker-limited, not multiply-limited",
            "fftmul",
            "fftmul degree ceiling",
            m24,
        )
        .with_formulation("the multiply's own reported ceiling")
        .with_work("ceiling before, as a degree", 262_144)
        .with_work("ceiling after, as a degree", 4_194_304)
        .with_measured_quantity(
            "reported degree ceiling",
            "log2 degree",
            22,
            "#189: the ceiling moved from 2^18 to 2^22, 16x, with the budget now on the multiply",
            m24,
        )
        .with_attribution(Attribution::PredictionHeld)
        .with_limiting_stage(LimitingStage::LinearAlgebra)
        .with_environment(workstation("tools/benchlock.sh")),
        // ---- M24 10.1, the budget ladder: the right magnitude about the wrong quantity ----
        CostRow::new(
            "F4 budget ladder, the memory the entry budget bounds",
            "f4",
            "fukuoka-mq-III-n20-seed0",
            m24,
        )
        .with_formulation("full-width grevlex under a live-entry cap")
        .with_parameter("variables", 20)
        .with_predicted_peak(Figure::predicted(
            16_000_000_000,
            "9.1's entry-storage ladder, 0.32 / 1.6 / 6.4 / 16 GB at 16 bytes an entry",
            "MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md 9.1",
        ))
        .with_estimated_peak(Figure::predicted(
            195 * MIB,
            "live matrix entries x 16 B, which is what the budget accounts",
            m24,
        ))
        .with_measured_resident(14_752 * MIB, "VmHWM", m24)
        .with_attribution(Attribution::WrongQuantity {
            predicted_quantity:
                "the entry storage of one allocation, which the entry budget bounds".to_string(),
            actual_quantity: "the peak resident set of the process: 195 MB accounted inside \
                              14 752 MB, a factor of 75. README said the budget bounds one \
                              allocation"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::SymbolicPreprocessingQueue)
        .with_environment(workstation(
            "ZEEBRA_AFFINITY=0-7, one live-entry cap per rung",
        )),
        // ---- M24 10.1 / #243, the six-round build ----
        CostRow::new(
            "six-round symbolic build, peak RSS",
            "resultant-elimination",
            "poseidon31-cico-t16-rf2-rp4",
            build,
        )
        .with_formulation("bivariate CICO, t = 16, symbolic build alone")
        .with_parameter("rounds", 6)
        .with_parameter("state words cubed", 16)
        .with_parameter("output degree", 729)
        .with_largest_intermediate(Intermediate::new(
            "the (p^2) * p transient of SparseMultiPoly's multiply",
            3_540_000_000,
            "term-products",
        ))
        .with_work("term-products in p * p", 886_000_000)
        .with_work("term-products in (p^2) * p", 3_540_000_000)
        .with_work("terms in the result", 266_815)
        .with_predicted_peak(Figure::predicted(
            68_000_000,
            "7.4's \"peak memory is not a concern ... ~68 MB\"",
            "MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md 7.4",
        ))
        .with_measured_resident(
            57_000_000_000,
            "VmHWM, polled externally and cross-checked against util::peak_resident_bytes",
            build,
        )
        .with_attribution(Attribution::UnlistedRisk {
            detail: "7.5 named the build's *time* as the one unchecked cost and did not list its \
                     memory as a risk at all. The term-count extrapolation was right and the \
                     memory estimate was not: the transient is four orders of magnitude larger \
                     than the 4.3 MB result it builds, and the RSS trace is a sawtooth with one \
                     peak per state word rather than a leak"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::PolynomialMultiplyTransient)
        .with_environment(workstation(
            "tools/benchlock.sh, single-threaded on one pinned core",
        ))
        .with_reproduce(
            "cargo run --release --example resultant_cico -- --row poseidon31-cico-t16-rf2-rp4 \
             --build-only",
        ),
        CostRow::new(
            "six-round symbolic build, elapsed",
            "resultant-elimination",
            "poseidon31-cico-t16-rf2-rp4",
            build,
        )
        .with_formulation("bivariate CICO, t = 16, symbolic build alone")
        .with_parameter("rounds", 6)
        .with_predicted_runtime(Figure::predicted(
            Duration::from_secs(36 * 60),
            "7.4's ~36 min estimate",
            "MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md 7.4",
        ))
        .with_measured_runtime(
            Duration::from_secs_f64(48.37 * 60.0),
            "wall clock under tools/benchlock.sh, reported as an upper bound",
            build,
        )
        .with_attribution(Attribution::MagnitudeOnly {
            detail: "1.34x and the same order, so the time estimate holds. The build is now a \
                     binding stage at about half of 7.4's whole ~1-1.5 h for the row, where it \
                     had been 0.8% of every row before it"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::PolynomialMultiplyTransient)
        .with_environment(workstation(
            "tools/benchlock.sh, single-threaded on one pinned core",
        ))
        .with_reproduce(
            "cargo run --release --example resultant_cico -- --row poseidon31-cico-t16-rf2-rp4 \
             --build-only",
        ),
        // ---- #243: the one large prediction in this family that held ----
        CostRow::new(
            "the six-round build's peak RSS, from the multiply's term-product count",
            "resultant-elimination",
            "poseidon31-cico-t16-rf2-rp4",
            build,
        )
        .with_formulation("bivariate CICO, t = 16, symbolic build alone")
        .with_parameter("rounds", 6)
        .with_largest_intermediate(Intermediate::new(
            "the (p^2) * p transient of SparseMultiPoly's multiply",
            3_540_000_000,
            "term-products",
        ))
        .with_predicted_peak(Figure::predicted(
            56_600_000_000,
            "3.54e9 term-products for (p^2) * p at 16 bytes an entry",
            build,
        ))
        .with_measured_resident(
            57_000_000_000,
            "VmHWM, polled externally and cross-checked against util::peak_resident_bytes",
            build,
        )
        .with_attribution(Attribution::PredictionHeld)
        .with_limiting_stage(LimitingStage::PolynomialMultiplyTransient)
        .with_environment(workstation(
            "tools/benchlock.sh, single-threaded on one pinned core",
        ))
        .with_next_size(
            NextSizeProjection::of(
                "eight rounds, bounded by the output instead of the product count",
            )
            .with_peak_bytes(Figure::predicted(
                4_300_000,
                "the product's actual size, which a collecting or chunked multiply would bound \
                     the live set by (#243)",
                build,
            )),
        )
        .with_reproduce(
            "cargo run --release --example resultant_cico -- --row poseidon31-cico-t16-rf2-rp4 \
             --build-only",
        ),
        // ---- #243 merged: the same claim, re-measured. A NEW row, not an edit to the one above ----
        CostRow::new(
            "six-round symbolic build, peak RSS",
            "resultant-elimination",
            "poseidon31-cico-t16-rf2-rp4",
            collecting,
        )
        .with_formulation("bivariate CICO, t = 16, symbolic build alone, collecting multiply")
        .with_parameter("rounds", 6)
        .with_parameter("state words cubed", 16)
        .with_parameter("output degree", 729)
        .with_largest_intermediate(Intermediate::new(
            "the output state, held two to three times over across the MDS layer",
            266_815,
            "terms a word, sixteen words at (Monomial<2>, F)",
        ))
        .with_predicted_peak(Figure::predicted(
            68_000_000,
            "7.4's \"peak memory is not a concern ... ~68 MB\"",
            "MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md 7.4",
        ))
        .with_measured_resident(
            325_500_928,
            "VmHWM: an external /proc poll and util::peak_resident_bytes agreeing exactly at \
             317 872 kB, taken off tools/benchlock.sh per f4-resource-scaling.md 8",
            collecting,
        )
        .with_attribution(Attribution::MagnitudeOnly {
            detail: "7.4's estimate is now wrong by 4.7x rather than 838x, in the same direction, \
                     and the quantity is no longer wrong: the remaining 0.32 GB is the *output* \
                     two to three times over, because Add still materialises |a| + |b| terms and \
                     rebuilds a fresh map across the MDS layer. A constant factor on the output is \
                     the regime #243 set out to reach. 179x smaller than 6.8 for an identical \
                     result -- deg 729 / 729, 266 815 / 266 815 terms"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::BasisStorage)
        .with_environment(Environment {
            policy:
                "off tools/benchlock.sh for the peak-RSS probe; after #243's collecting multiply"
                    .to_string(),
            ..workstation("")
        })
        .with_reproduce(
            "cargo run --release --example resultant_cico -- --row poseidon31-cico-t16-rf2-rp4 \
             --build-only",
        ),
        // ---- #237: the attribution ----
        CostRow::new(
            "F4 peak RSS at the 20 000 000-entry rung, attributed",
            "f4",
            "fukuoka-mq-III-n20-seed0",
            f4_scaling,
        )
        .with_formulation("full-width grevlex, 200 000 columns, 20 000 000 live entries")
        .with_parameter("variables", 20)
        .with_parameter("equations", 40)
        .with_parameter("characteristic", 31)
        .with_parameter("live-entry cap", 20_000_000)
        .with_solving_degree(5)
        .with_largest_intermediate(Intermediate::new(
            "the VecDeque<Monomial<20>> pending-monomial queue of symbolic preprocessing",
            162_188_194,
            "monomials at the queue's high water, 80 B each",
        ))
        .with_work("monomials at the queue's high water", 162_188_194)
        .with_work("rows in the refused closure", 64_062)
        .with_work("basis terms at peak", 5_389_241)
        .with_work("named sites' share of peak RSS, basis points", 9_600)
        .with_estimated_peak(Figure::predicted(
            195_433_980,
            "max_live_nonzeros 12 212 087 x 16 B + 40 588 B of dense buffer",
            f4_scaling,
        ))
        .with_measured_resident(
            13_996 * MIB,
            "util::peak_resident_bytes (VmHWM), in-process after F4 returned",
            f4_scaling,
        )
        .with_measured_allocated(
            21_674 * MIB,
            "a tracking #[global_allocator] with LIVE/PEAK atomics",
            f4_scaling,
        )
        .with_measured_quantity(
            "the pending-monomial queue's share of peak RSS",
            "basis points",
            8_840,
            "162 188 194 monomials x 80 B against VmHWM",
            f4_scaling,
        )
        .with_attribution(Attribution::WrongQuantity {
            predicted_quantity: "matrix entry storage, which max_live_nonzeros budgets and which \
                                 measures 1.3% of the peak"
                .to_string(),
            actual_quantity: "one VecDeque<Monomial<20>> in symbolic preprocessing at 88.4%, \
                              reached before any matrix exists and therefore before any budget \
                              can be crossed. The basis held twice is 6.5%"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::SymbolicPreprocessingQueue)
        .with_environment(workstation(
            "ZEEBRA_AFFINITY=0-7, max_live_bytes set clear of the entry cap",
        ))
        .with_reproduce("cargo run --release --example f4_memory"),
        CostRow::new(
            "peak allocated against peak resident, on one row",
            "f4",
            "fukuoka-mq-III-n20-seed0",
            f4_scaling,
        )
        .with_formulation("full-width grevlex, 200 000 columns, 20 000 000 live entries")
        .with_solving_degree(5)
        .with_largest_intermediate(Intermediate::new(
            "the pending-monomial queue's capacity, one allocation",
            268_435_456,
            "slots at 80 B = 20 480 MiB, about 60% never written",
        ))
        .with_measured_resident(
            13_996 * MIB,
            "util::peak_resident_bytes (VmHWM), which counts touched pages",
            f4_scaling,
        )
        .with_measured_allocated(
            21_674 * MIB,
            "a tracking #[global_allocator], which counts reservations",
            f4_scaling,
        )
        .with_attribution(Attribution::WrongQuantity {
            predicted_quantity: "\"peak memory\", read as one quantity".to_string(),
            actual_quantity: "two: the queue's 20 480 MiB capacity against its 12 374 MiB of \
                              touched pages. One allocation larger than the whole resident peak \
                              is why no amount of care in reading \"peak memory\" distinguishes \
                              them -- only recording which one it is does"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::SymbolicPreprocessingQueue)
        .with_environment(workstation(
            "ZEEBRA_AFFINITY=0-7, max_live_bytes set clear of the entry cap",
        ))
        .with_reproduce("cargo run --release --example f4_memory"),
        CostRow::new(
            "F4 peak RSS at the 10 000 000-entry rung, attributed",
            "f4",
            "fukuoka-mq-III-n20-seed0",
            f4_scaling_d4,
        )
        .with_formulation("full-width grevlex, 200 000 columns, 10 000 000 live entries")
        .with_parameter("live-entry cap", 10_000_000)
        .with_solving_degree(4)
        .with_largest_intermediate(Intermediate::new(
            "the VecDeque<Monomial<20>> pending-monomial queue of symbolic preprocessing",
            6_196_886,
            "monomials at the queue's high water, 473 MB",
        ))
        .with_work("rows in the refused closure", 10_297)
        .with_work("basis terms at peak", 240_551)
        .with_estimated_peak(Figure::predicted(
            6_081_741,
            "the budgeted matrix entries at 16 B each",
            f4_scaling_d4,
        ))
        .with_measured_resident(
            608 * MIB,
            "util::peak_resident_bytes (VmHWM), in-process; the external poller caught 609 MB",
            f4_scaling_d4,
        )
        .with_measured_quantity(
            "the pending-monomial queue's share of peak RSS",
            "basis points",
            7_800,
            "6 196 886 monomials x 80 B against VmHWM",
            f4_scaling_d4,
        )
        .with_attribution(Attribution::WrongQuantity {
            predicted_quantity: "matrix entry storage, 5.8 MB of a 608 MB peak".to_string(),
            actual_quantity: "the same queue at 78%. The queue dominates at both rungs, so this \
                              is not a degree-5 phenomenon -- it is what symbolic preprocessing \
                              costs at every degree, scaling with the closure"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::SymbolicPreprocessingQueue)
        .with_environment(workstation(
            "ZEEBRA_AFFINITY=0-7, max_live_bytes set clear of the entry cap",
        ))
        .with_reproduce("cargo run --release --example f4_memory"),
        // ---- #289: the determinant law ----
        CostRow::new(
            "per-determinant cost at order 1 458, one worker",
            "resultant-elimination",
            "determinant sweep, synthetic bivariate pairs",
            law,
        )
        .with_formulation("degree 1 in the surviving variable, order / 2 in the eliminated one")
        .with_parameter("matrix order", 1_458)
        .with_parameter("workers", 1)
        .with_parameter("determinants x draws", 24)
        .with_largest_intermediate(Intermediate::new(
            "the Sylvester matrix, with L, U, P and a clone of A live",
            1_458,
            "matrix order (17.0 MB of matrix, 68.0 MB live per worker)",
        ))
        .with_predicted_runtime(Figure::with_basis(
            Duration::from_secs_f64(2.493),
            FigureBasis::Fitted {
                law: "8.3216e-10 * order^2.9953".to_string(),
                worst_residual_bp: 370,
                fitted_to: 4_374,
            },
            law,
        ))
        .with_measured_runtime(
            Duration::from_secs_f64(2.404),
            "median of three draws; wall equals core-time at one worker, under tools/benchlock.sh",
            law,
        )
        .with_attribution(Attribution::PredictionHeld)
        .with_limiting_stage(LimitingStage::DeterminantEvaluation)
        .with_environment(workstation("tools/benchlock.sh, one pinned core"))
        .with_next_size(
            NextSizeProjection::of("order 4 374, inside the fitted range").with_runtime(
                Figure::with_basis(
                    Duration::from_secs_f64(66.960),
                    FigureBasis::Fitted {
                        law: "8.3216e-10 * order^2.9953".to_string(),
                        worst_residual_bp: 370,
                        fitted_to: 4_374,
                    },
                    law,
                ),
            ),
        )
        .with_reproduce("cargo run --release --example determinant_sweep"),
        CostRow::new(
            "per-determinant cost at order 13 122",
            "resultant-elimination",
            "determinant sweep, synthetic bivariate pairs",
            law,
        )
        .with_formulation("degree 1 in the surviving variable, order / 2 in the eliminated one")
        .with_parameter("matrix order", 13_122)
        .with_parameter("workers", 1)
        .with_work("upper end of the stated range, in seconds", 1_926)
        .with_predicted_runtime(Figure::with_basis(
            Duration::from_secs(1_833),
            FigureBasis::Extrapolated {
                law: "8.3216e-10 * order^2.9953".to_string(),
                fitted_to: 4_374,
                evaluated_at: 13_122,
            },
            law,
        ))
        .with_limiting_stage(LimitingStage::DeterminantEvaluation)
        .with_environment(workstation("tools/benchlock.sh, one pinned core"))
        .with_next_size(
            NextSizeProjection::of("rf4-rp4 at eight rounds, 531 442 determinants on 32 workers")
                .with_runtime(Figure::with_basis(
                    Duration::from_secs_f64(490.5 * 86_400.0),
                    FigureBasis::Extrapolated {
                        law:
                            "8.3216e-10 * order^2.9953, with the 1.00 / 1.17 / 1.31 width penalty \
                              extrapolated at the same slope beyond 32 workers"
                                .to_string(),
                        fitted_to: 4_374,
                        evaluated_at: 13_122,
                    },
                    law,
                )),
        )
        .with_reproduce("cargo run --release --example determinant_sweep -- --order 13122"),
        CostRow::new(
            "the exponent of the per-determinant cost law above L2",
            "resultant-elimination",
            "determinant sweep, orders 486 / 1 458 / 4 374",
            law,
        )
        .with_formulation("ordinary least squares on (ln order, ln core-time)")
        .with_parameter("orders fitted", 3)
        .with_work("worst residual, basis points", 370)
        .with_work("standard error of the exponent, per 10 000", 285)
        .with_predicted_quantity(Quantity {
            name: "exponent of the cost law".to_string(),
            unit: "per 10 000".to_string(),
            figure: Figure::predicted(
                30_000,
                "Crout LU is O(order^3), so the cost law is cubic",
                "docs/research/resultant-elimination.md 6.5",
            ),
        })
        .with_measured_quantity(
            "exponent of the cost law",
            "per 10 000",
            29_953,
            "fit_power_law over orders 486 / 1 458 / 4 374, exponent +/-0.0285",
            law,
        )
        .with_attribution(Attribution::PredictionHeld)
        .with_limiting_stage(LimitingStage::DeterminantEvaluation)
        .with_environment(workstation("tools/benchlock.sh, one pinned core"))
        .with_reproduce("cargo run --release --example determinant_sweep"),
        CostRow::new(
            "the exponent of the per-determinant cost law below L2",
            "resultant-elimination",
            "determinant sweep, orders 18 / 162",
            law,
        )
        .with_formulation("exact through two points, so no residual and no standard error")
        .with_parameter("orders fitted", 2)
        .with_predicted_quantity(Quantity {
            name: "exponent of the cost law".to_string(),
            unit: "per 10 000".to_string(),
            figure: Figure::predicted(
                30_000,
                "Crout LU is O(order^3), so the cost law is cubic at every order",
                "docs/research/resultant-elimination.md 6.5",
            ),
        })
        .with_measured_quantity(
            "exponent of the cost law",
            "per 10 000",
            27_902,
            "fit_power_law over orders 18 and 162, exact through two points",
            law,
        )
        .with_attribution(Attribution::MagnitudeOnly {
            detail: "genuinely sub-cubic at the bottom: fixed per-determinant cost -- the \
                     coefficient-row evaluations, the (m+n)^2 build, four (m+n)^2 allocations and \
                     the Matrix::new copy -- that an order-18 determinant's 2 000 \
                     multiply-subtract steps cannot amortize and an order-162 determinant's 1.4 \
                     million already can. A single law over all five orders misses by 14.9% with \
                     residual signs -, +, +, +, -, which is curvature and not noise"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::DeterminantEvaluation)
        .with_environment(workstation("tools/benchlock.sh, one pinned core"))
        .with_reproduce("cargo run --release --example determinant_sweep"),
        // ---- #318 and #319: measured, reproducible, unexplained ----
        CostRow::new(
            "order-162 determinant on the 13 123-sample reference route, rf2-rp2",
            "resultant-elimination",
            "poseidon31-cico-t16-rf2-rp2",
            law,
        )
        .with_formulation("the reference interpolation route, one worker")
        .with_parameter("matrix order", 162)
        .with_parameter("samples", 13_123)
        .with_parameter("workers", 1)
        .with_predicted_runtime(Figure::predicted(
            Duration::from_nanos(2_868_000),
            "6.5's figure on record -- 37 634.3 ms / 13 123 -- carried forward as the expectation \
             for the same measurement",
            "docs/research/resultant-elimination.md 6.5",
        ))
        .with_measured_runtime(
            Duration::from_nanos(3_439_000),
            "45 131.0 ms / 13 123 samples, same registered row, same code path, same lock",
            law,
        )
        .with_attribution(Attribution::Unexplained {
            issue: "#318".to_string(),
            detail: "the same measurement months and a commit range apart. Three of four \
                     re-measurements point the same way by about 1.2x and the smallest order \
                     points the other way, so a factor computed between a 6.5 figure and one \
                     taken now carries a ~20% systematic that is not a property of either \
                     implementation"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::DeterminantEvaluation)
        .with_environment(workstation("tools/benchlock.sh, one pinned core"))
        .with_reproduce(
            "cargo run --release --example resultant_cico -- --row poseidon31-cico-t16-rf2-rp2",
        ),
        CostRow::new(
            "core-time penalty at 32 workers, order 1 458",
            "resultant-elimination",
            "determinant sweep, synthetic bivariate pairs",
            law,
        )
        .with_formulation("the same sweep at three widths, 4 determinants a worker")
        .with_parameter("matrix order", 1_458)
        .with_parameter("workers", 32)
        .with_predicted_quantity(Quantity {
            name: "core-time penalty at 32 workers".to_string(),
            unit: "per 10 000".to_string(),
            figure: Figure::predicted(
                10_900,
                "6.6's measured 4-9% out to 32 workers, carried forward as the expectation",
                "docs/research/resultant-elimination.md 6.6",
            ),
        })
        .with_measured_quantity(
            "core-time penalty at 32 workers",
            "per 10 000",
            13_100,
            "3.148 s against 2.404 s at one worker, with 4 determinants a worker so the 68 MB \
             live set's page faults are amortized; 1.52x at one determinant a worker",
            law,
        )
        .with_attribution(Attribution::Unexplained {
            issue: "#319".to_string(),
            detail: "6.6 measured this penalty as 4-9% out to 32 workers and it reproduces as \
                     31-44%. 6.6's own argument -- that the limit is the all-core clock rather \
                     than memory bandwidth -- is if anything strengthened, and the shape still \
                     supports it: the penalty is the same 1.44x at orders 162 and 486, whose \
                     matrices differ by 9x, which a bandwidth limit would not do. The size \
                     disagrees with what is on record and this milestone did not resolve why"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::DeterminantEvaluation)
        .with_environment(Environment {
            concurrency: 32,
            ..workstation("tools/benchlock.sh, 32 workers")
        })
        .with_reproduce("cargo run --release --example determinant_sweep -- --workers 32"),
        // ---- #318 and #319 resolved: 6.13 re-ran each figure's own binary ----
        // Appended rather than written over the two rows above, which is the append-only rule: the
        // M25 rows were honestly unexplained when taken and the resolution is a later measurement,
        // not a correction to an earlier one. These two carry a `commit`, which the transcribed
        // rows cannot -- knowing which commit a figure came from is precisely what made the
        // experiment possible.
        CostRow::new(
            "order-162 determinant on the 13 123-sample reference route, rf2-rp2, at 6.5's own \
             commit",
            "resultant-elimination",
            "poseidon31-cico-t16-rf2-rp2",
            resolved,
        )
        .with_formulation("the reference interpolation route, one worker, 6.5's own binary re-run")
        .with_parameter("matrix order", 162)
        .with_parameter("samples", 13_123)
        .with_parameter("workers", 1)
        .with_predicted_runtime(Figure::predicted(
            Duration::from_nanos(2_868_000),
            "6.5's figure on record -- 37 634.3 ms / 13 123 -- which this row tests by re-running \
             the binary that produced it rather than by bisecting the range after it",
            "docs/research/resultant-elimination.md 6.5",
        ))
        .with_measured_runtime(
            Duration::from_nanos(3_462_000),
            "45 426.8 ms / 13 123 samples at commit 93bb1c2 -- the commit 6.5's figure was taken \
             at -- on one pinned core under the lock with the box otherwise idle. In the same run \
             lagrange_interpolate is 1.039x and the 256 order-18 determinants are 1.00x. 47 944.4 \
             ms for the same measurement at load 14",
            resolved,
        )
        .with_attribution(Attribution::IncomparableFigures {
            detail: "one session against another, which resolves #318. The figure does not \
                     reproduce in the binary that produced it, so no commit in the 435-commit \
                     range can be responsible and the bisection #318 proposed would land on \
                     nothing. Nor is it the all-core clock or any other uniform property of the \
                     machine: stages of the same process on the same core move by 1.00x at a \
                     ~10 kB working set, 1.04-1.06x at 105 kB and 1.15-1.21x at ~840 kB, which is \
                     monotone in the working set and lands exactly where it stops fitting the \
                     private 512 kB L2. Through the real route the two libraries differ by \
                     1.051-1.086x, inside the 5% drift 6.5 recorded between runs of its own \
                     binary, and crout.rs, sylvester_determinant and coefficients_in are \
                     byte-identical across the range. Unlike #319 this does NOT go away on an idle \
                     box -- it is bounded to the CCD-local candidates and not explained further. \
                     Ratios taken inside one session do reproduce: 6.5's 1.40x / 1.23x / 1.25x \
                     came back as 1.41x / 1.18x / 1.20x"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::DeterminantEvaluation)
        .with_environment(Environment {
            commit: "93bb1c2".to_string(),
            cpu: "64 physical, 128 logical, 8 CCDs x 32 MB L3, 512 kB L2 a core".to_string(),
            ..workstation("tools/benchlock.sh, one pinned core")
        })
        .with_reproduce(
            "git worktree add --detach /tmp/era 93bb1c2 && cp examples/determinant_era.rs \
             /tmp/era/examples/ && tools/benchlock.sh era taskset -c 8 \
             .../determinant_era --workers 1 --determinants 13123",
        ),
        CostRow::new(
            "core-time penalty at 32 workers, order 162, at 6.6's own commit",
            "resultant-elimination",
            "poseidon31-cico-t16-rf2-rp2",
            resolved,
        )
        .with_formulation("6.6's own configuration: 13 123 determinants over 32 pinned cores")
        .with_parameter("matrix order", 162)
        .with_parameter("samples", 13_123)
        .with_parameter("workers", 32)
        .with_predicted_quantity(Quantity {
            name: "core-time penalty at 32 workers".to_string(),
            unit: "per 10 000".to_string(),
            figure: Figure::predicted(
                10_870,
                "6.6's 3.270 ms against 3.007 ms at one worker, carried forward as the expectation \
                 for the same configuration",
                "docs/research/resultant-elimination.md 6.6",
            ),
        })
        .with_measured_quantity(
            "core-time penalty at 32 workers",
            "per 10 000",
            10_630,
            "3.662 ms against 3.446 ms at one worker, at commit 93bb1c2 on a 32-core pinned set \
             with the box otherwise idle. 1.072x at 1985504 in the same session; 1.343x at 8 workers \
             and 1.478x at 32 for the same configuration on the same binaries hours earlier, with \
             three other agents' cargo test --release runs resident",
            resolved,
        )
        .with_attribution(Attribution::IncomparableFigures {
            detail: "THE PREDICTION HELD -- 0.978x, and the incomparability is between the two \
                     MEASUREMENTS #319 was opened about, not between this row's own columns. \
                     6.9's 31-44% was ambient load, which resolves #319 against 6.9's own reading \
                     that it was #318 seen through the worker count. 6.6's 4-9% REPRODUCES on an \
                     idle box, on 6.6's own binary (93bb1c2) and on 1985504 alike, so the 31-44% is not a \
                     property of M25's harness, of its synthetic pair or of the batch length: it \
                     is what the same measurement gives while other agents are building. \
                     benchlock.sh serializes benchmarks and not builds, so that load runs straight \
                     through the lock, and nothing in its log recorded it -- it now writes load= \
                     on START and END. The width penalty is 6% and contention is a separate factor \
                     of up to 1.4x on top, which is why CORE_TIME_PER_DOUBLING stays at 0.065. Two \
                     corrections to 6.6's mechanism survive: the all-core clock is excluded by the \
                     working-set shape, and 6.6's working-set bound compares 27 MB against '256 MB \
                     L3' when this part has 8 CCDs of 32 MB shared by 8 cores each, so the figure a \
                     worker is bounded by is 8x smaller. The first-touch component is still real \
                     and still confined to order 1 458, where one worker's 68 MB live set exceeds \
                     its CCD's whole L3"
                .to_string(),
        })
        .with_limiting_stage(LimitingStage::DeterminantEvaluation)
        .with_environment(Environment {
            commit: "93bb1c2".to_string(),
            concurrency: 32,
            cpu: "64 physical, 128 logical, 8 CCDs x 32 MB L3, 512 kB L2 a core".to_string(),
            ..workstation("tools/benchlock.sh, 32 pinned cores")
        })
        .with_reproduce(
            "taskset -c 0-31 .../determinant_era --workers 1,8,32 --determinants 13123",
        ),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn environment() -> Environment {
        Environment {
            commit: "deadbeef".to_string(),
            base_commit: "deadbeef".to_string(),
            patch_id: String::new(),
            machine: "workstation".to_string(),
            cpu: "64 logical, taskset 0-7".to_string(),
            concurrency: 1,
            build: "release, fat LTO, -C target-cpu=x86-64-v3".to_string(),
            policy: "tools/benchlock.sh, one pinned core".to_string(),
        }
    }

    fn row() -> CostRow {
        CostRow::new(
            "six-round symbolic build, peak RSS",
            "resultant-elimination",
            "poseidon31-cico-t16-rf2-rp4",
            "resultant-elimination.md 6.8",
        )
        .with_environment(environment())
    }

    /// A row whose predicted and measured figures are both present reports the arithmetic of them.
    #[test]
    fn test_prediction_error_is_the_arithmetic_of_the_two_columns() {
        let complete = row()
            .with_predicted_peak(Figure::predicted(
                68 * 1024 * 1024,
                "7.4's estimate",
                "MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md 7.4",
            ))
            .with_measured_resident(57_000_000_000, "VmHWM", "resultant-elimination.md 6.8")
            .with_attribution(Attribution::UnlistedRisk {
                detail: "7.5 named the build's time as the risk and not its memory".to_string(),
            });
        complete.check().expect("a legal row");

        let errors = complete.prediction_errors();
        assert_eq!(errors.len(), 1);
        let expected = 57_000_000_000.0 / (68.0 * 1024.0 * 1024.0);
        assert!(
            (errors[0].factor - expected).abs() < 1e-9,
            "the error column must be the quotient of the two columns: {} against {}",
            errors[0].factor,
            expected
        );
        assert!(
            (errors[0].relative_percent - (expected - 1.0) * 100.0).abs() < 1e-6,
            "{}",
            errors[0].relative_percent
        );
        assert!(
            (errors[0].factor - 799.5).abs() < 1.0,
            "the documented 838x is against 68 MB read as 10^6 bytes; against MiB it is {:.0}x",
            errors[0].factor
        );
    }

    /// An error column injected into a stored row has no effect on the error the row reports.
    ///
    /// Nothing in the file is read as an error, so a hand-edited or stale figure cannot become a
    /// published finding.
    #[test]
    fn test_a_stored_error_column_is_recomputed_rather_than_read() {
        let original = row()
            .with_predicted_runtime(Figure::predicted(
                Duration::from_secs(120),
                "9.2's estimate",
                "graeffe-root-finding.md 9.2",
            ))
            .with_measured_runtime(
                Duration::from_millis(15_200),
                "wall clock under tools/benchlock.sh",
                "MILESTONE-PUBLISHED-ATTACK-REPRODUCTION.md 10.1",
            )
            .with_attribution(Attribution::StageNotInScope {
                stage: "a ~100 s r = 2^24 subgroup scan belonging to Zeebra's single-root descent"
                    .to_string(),
            });

        // Inject an error column a reader might believe, under both the hedged name the writer
        // uses and the plausible one it does not.
        let Json::Object(mut fields) = original.to_json() else {
            panic!("a row serialises as an object");
        };
        for (key, value) in fields.iter_mut() {
            if key == "prediction_error" {
                *value = Json::string("1.0000");
            }
        }
        fields.push((
            "derived".to_string(),
            Json::object([("factor", Json::string("1.0000"))]),
        ));
        let tampered = Json::Object(fields).to_json();
        assert!(
            tampered.contains("1.0000"),
            "the injected value is in the text"
        );

        let back = CostRow::from_json(&Json::parse(&tampered).expect("valid")).expect("loads");
        let errors = back.prediction_errors();
        assert_eq!(errors.len(), 1);
        assert!(
            (errors[0].factor - 15.2 / 120.0).abs() < 1e-9,
            "the tampered 1.0 must not survive the load: got {}",
            errors[0].factor
        );
    }

    /// A row with a prediction and no measurement is legal, and reports itself as incomplete.
    #[test]
    fn test_a_prediction_without_a_measurement_is_legal_and_visibly_incomplete() {
        let open = row().with_predicted_runtime(Figure::predicted(
            Duration::from_secs(8 * 3600),
            "an estimate nobody has checked",
            "an issue",
        ));
        open.check().expect("a prediction alone is a legal row");
        assert!(open.has_prediction());
        assert!(!open.has_measurement());
        assert!(!open.is_complete());
        assert!(open.prediction_errors().is_empty());

        let mut board = CostModelBoard::new();
        board.add(open).expect("accepted");
        assert_eq!(board.open_predictions().len(), 1);
        let markdown = board.to_markdown();
        assert!(markdown.contains("_open_"), "{}", markdown);
        assert!(markdown.contains("nothing measured"), "{}", markdown);
        assert!(markdown.contains("Open predictions"), "{}", markdown);
    }

    /// An estimate placed in a measured field is refused as a schema error.
    #[test]
    fn test_an_estimate_in_a_measured_field_is_a_schema_error() {
        let mut bad = row();
        bad.measured_peak_resident_bytes = Some(Figure::predicted(
            16 << 30,
            "16 bytes an entry",
            "f4-resource-scaling.md 2",
        ));
        assert_eq!(
            bad.check(),
            Err(SchemaError::EstimateInAMeasuredField {
                field: "measured_peak_resident_bytes",
                basis: "predicted",
            })
        );
        let mut board = CostModelBoard::new();
        assert!(board.add(bad).is_err(), "the board must not store it");
        assert!(board.rows().is_empty());
    }

    /// A measurement placed in a predicted field is refused as a schema error.
    #[test]
    fn test_a_measurement_in_a_predicted_field_is_a_schema_error() {
        let mut bad = row();
        bad.predicted_peak_bytes = Some(Figure::measured(1 << 30, "VmHWM", "somewhere"));
        assert_eq!(
            bad.check(),
            Err(SchemaError::MeasurementInAPredictedField {
                field: "predicted_peak_bytes"
            })
        );
    }

    /// An unsourced figure is refused, so no number on the board is uncitable.
    #[test]
    fn test_an_unsourced_figure_is_refused() {
        let mut bad = row();
        bad.predicted_runtime = Some(Figure::predicted(Duration::from_secs(1), "a model", ""));
        assert_eq!(
            bad.check(),
            Err(SchemaError::UnsourcedFigure {
                field: "predicted_runtime"
            })
        );
    }

    /// A measured prediction must attribute its difference; an unmeasured one must not.
    #[test]
    fn test_attribution_and_measurement_must_agree() {
        let unmeasured = row()
            .with_predicted_runtime(Figure::predicted(
                Duration::from_secs(1),
                "a model",
                "an issue",
            ))
            .with_attribution(Attribution::PredictionHeld);
        assert_eq!(
            unmeasured.check(),
            Err(SchemaError::AttributionWithoutAMeasurement)
        );

        let unattributed = row()
            .with_predicted_runtime(Figure::predicted(
                Duration::from_secs(1),
                "a model",
                "an issue",
            ))
            .with_measured_runtime(Duration::from_secs(2), "wall clock", "an issue");
        assert_eq!(
            unattributed.check(),
            Err(SchemaError::MeasurementWithoutAnAttribution)
        );
    }

    /// Peak allocated and peak resident are separate columns and both survive a round trip.
    #[test]
    fn test_allocated_and_resident_peaks_do_not_share_a_column() {
        let both = row()
            .with_measured_resident(13_996 * 1_000_000, "VmHWM", "f4-resource-scaling.md 9.2")
            .with_measured_allocated(
                21_674 * 1_000_000,
                "tracking global allocator",
                "f4-resource-scaling.md 9.2",
            )
            .with_attribution(Attribution::PredictionHeld);
        both.check().expect("legal");

        let text = both.to_json().to_json();
        let back = CostRow::from_json(&Json::parse(&text).expect("valid")).expect("round trips");
        assert_eq!(
            back.measured_peak_resident_bytes.as_ref().map(|f| f.value),
            Some(13_996_000_000)
        );
        assert_eq!(
            back.measured_peak_allocated_bytes.as_ref().map(|f| f.value),
            Some(21_674_000_000)
        );
        let markdown = {
            let mut board = CostModelBoard::new();
            board.add(back).expect("accepted");
            board.to_markdown()
        };
        assert!(markdown.contains("resident"), "{}", markdown);
        assert!(markdown.contains("allocated"), "{}", markdown);
    }

    /// An extrapolated figure reports how far past its evidence it reaches.
    #[test]
    fn test_an_extrapolated_figure_reports_its_distance_from_the_evidence() {
        let basis = FigureBasis::Extrapolated {
            law: "8.3216e-10 * order^2.9953".to_string(),
            fitted_to: 4_374,
            evaluated_at: 13_122,
        };
        assert_eq!(basis.tag(), "extrapolated");
        assert!(!basis.is_measurement());
        assert_eq!(basis.times_past_the_evidence(), Some(3.0));
        assert!(basis.detail().contains("3.0x past"), "{}", basis.detail());

        let fitted = FigureBasis::Fitted {
            law: "8.3216e-10 * order^2.9953".to_string(),
            worst_residual_bp: 370,
            fitted_to: 4_374,
        };
        assert_eq!(fitted.times_past_the_evidence(), None);
        assert!(fitted.detail().contains("3.70%"), "{}", fitted.detail());
    }

    /// Every basis variant round-trips through JSON with its payload intact.
    #[test]
    fn test_every_basis_round_trips() {
        for basis in [
            FigureBasis::Measured {
                instrument: "VmHWM".to_string(),
            },
            FigureBasis::Fitted {
                law: "a*n^b".to_string(),
                worst_residual_bp: 370,
                fitted_to: 4_374,
            },
            FigureBasis::Predicted {
                model: "16 B an entry".to_string(),
            },
            FigureBasis::Extrapolated {
                law: "a*n^b".to_string(),
                fitted_to: 4_374,
                evaluated_at: 13_122,
            },
        ] {
            let text = basis.to_json().to_json();
            let back = FigureBasis::from_json(&Json::parse(&text).expect("valid")).expect("reads");
            assert_eq!(back, basis);
        }
    }

    /// An unreadable basis is refused rather than defaulted to measured.
    #[test]
    fn test_an_unreadable_basis_is_refused_rather_than_defaulted() {
        assert_eq!(
            FigureBasis::from_json(&Json::object([("kind", Json::string("vibes"))])),
            Err(SchemaError::MalformedRow {
                field: "basis.kind"
            })
        );
        assert_eq!(
            FigureBasis::from_json(&Json::Object(Vec::new())),
            Err(SchemaError::MalformedRow {
                field: "basis.kind"
            })
        );
    }

    /// Unexplained is a legal attribution and the renderer gives it its own section.
    #[test]
    fn test_unexplained_is_a_legal_attribution() {
        let unexplained = row()
            .with_predicted_runtime(Figure::predicted(
                Duration::from_micros(2_868),
                "the figure on record at 6.5",
                "resultant-elimination.md 6.5",
            ))
            .with_measured_runtime(
                Duration::from_micros(3_439),
                "wall clock / 13 123 samples",
                "resultant-elimination.md 6.9",
            )
            .with_attribution(Attribution::Unexplained {
                issue: "#318".to_string(),
                detail: "the same measurement, path and lock, months apart".to_string(),
            });
        unexplained.check().expect("legal");
        assert!(!unexplained.attribution.is_explained());

        let mut board = CostModelBoard::new();
        board.add(unexplained).expect("accepted");
        let markdown = board.to_markdown();
        assert!(markdown.contains("UNEXPLAINED (#318)"), "{}", markdown);
        assert!(markdown.contains("cause unknown"), "{}", markdown);
    }

    /// A re-measurement appends a second row and the first is left exactly as it was.
    #[test]
    fn test_a_re_measurement_appends_rather_than_overwrites() {
        let first = row()
            .with_measured_runtime(
                Duration::from_micros(2_868),
                "wall clock",
                "resultant-elimination.md 6.5",
            )
            .with_attribution(Attribution::PredictionHeld);
        let mut later = first.clone();
        later.measured_runtime = Some(Figure::measured(
            Duration::from_micros(3_439),
            "wall clock",
            "resultant-elimination.md 6.9",
        ));
        later.environment.commit = "cafebabe".to_string();

        let mut board = CostModelBoard::new();
        board.add(first.clone()).expect("accepted");
        board.add(later.clone()).expect("accepted");

        assert_eq!(board.rows().len(), 2, "both rows are kept");
        assert_eq!(
            board.rows()[0],
            first,
            "the earlier row is untouched by the re-measurement"
        );
        let trail = board.history_of(&first.key());
        assert_eq!(trail.len(), 2, "the trail is both rows under one key");
        assert_eq!(trail[0].environment.commit, "deadbeef");
        assert_eq!(trail[1].environment.commit, "cafebabe");

        // And through the file, in the same order.
        let text = board.to_json().to_json();
        let back = CostModelBoard::load(&Json::parse(&text).expect("valid")).expect("loads");
        assert_eq!(back.rows().len(), 2);
        let commits: Vec<&str> = back
            .rows()
            .iter()
            .map(|row| row.environment.commit.as_str())
            .collect();
        assert_eq!(commits, ["deadbeef", "cafebabe"], "order is preserved");
    }

    /// A malformed stored row is refused by name rather than silently skipped.
    #[test]
    fn test_a_malformed_row_is_refused_by_name() {
        let history = Json::object([(
            "rows",
            Json::Array(vec![Json::object([("schema", Json::int(1))])]),
        )]);
        assert_eq!(
            CostModelBoard::load(&history).err(),
            Some(SchemaError::MalformedRow { field: "claim" })
        );
        assert_eq!(
            CostModelBoard::load(&Json::object([("schema", Json::int(1))])).err(),
            Some(SchemaError::MalformedRow { field: "rows" })
        );
    }

    /// Every limiting stage tag round-trips, so the closed set cannot be widened by a typo.
    #[test]
    fn test_every_limiting_stage_tag_round_trips() {
        for stage in [
            LimitingStage::SymbolicPreprocessingQueue,
            LimitingStage::MatrixEntryStorage,
            LimitingStage::LinearAlgebra,
            LimitingStage::BasisStorage,
            LimitingStage::PolynomialMultiplyTransient,
            LimitingStage::DeterminantEvaluation,
            LimitingStage::EliminantRecovery,
            LimitingStage::RootFinding,
            LimitingStage::OrderConversion,
            LimitingStage::WallClockBudget,
            LimitingStage::NothingBound,
            LimitingStage::NotEstablished,
        ] {
            assert_eq!(LimitingStage::from_tag(stage.tag()), Some(stage));
        }
        assert_eq!(LimitingStage::from_tag("memory"), None);
        assert_eq!(
            LimitingStage::from_tag("the memory of one structure inside one batch"),
            None,
            "the conflation #237 was about is not expressible here"
        );
    }

    /// The register renders readable units and marks an absent figure rather than printing a zero.
    #[test]
    fn test_cells_render_in_readable_units() {
        assert_eq!(bytes_text(512.0), "512 B");
        assert_eq!(bytes_text((2u64 << 20) as f64), "2.0 MiB");
        assert_eq!(bytes_text((3u64 << 30) as f64), "3.00 GiB");
        assert_eq!(factor_text(838.24), "838x");
        assert_eq!(factor_text(1.3417), "1.34x");
        assert_eq!(factor_text(0.1267), "0.127x");
        assert_eq!(
            factor_text(0.0013),
            "1.30e-3x",
            "a two-decimal ratio would round this to 0.00x and report the opposite finding"
        );
        assert_eq!(duration_text(Duration::from_millis(12)), "12.000 ms");
        assert_eq!(duration_text(Duration::from_secs(90)), "1.50 min");
        assert_eq!(duration_text(Duration::from_secs(7_200)), "2.00 h");
        assert_eq!(duration_text(Duration::from_secs(172_800)), "2.00 d");
    }

    /// Every transcribed row is a legal row, and every figure on it is sourced.
    #[test]
    fn test_every_transcribed_row_is_legal_and_sourced() {
        let rows = transcribed_rows();
        assert!(rows.len() >= 18, "{} rows transcribed", rows.len());
        let mut board = CostModelBoard::new();
        for row in rows {
            row.check()
                .unwrap_or_else(|error| panic!("{}: {}", row.claim, error));
            assert!(
                !row.source.is_empty() && row.source.contains(|c: char| c.is_ascii_digit()),
                "{} must cite a section or an issue, not just a file: {}",
                row.claim,
                row.source
            );
            board.add(row).expect("accepted");
        }
        // Three bases are exercised by the seed set; `Fitted` and `Extrapolated` are #289's.
        let bases: Vec<&'static str> = board
            .rows()
            .iter()
            .filter_map(|row| row.predicted_runtime.as_ref())
            .map(|figure| figure.basis.tag())
            .collect();
        for expected in ["predicted", "fitted", "extrapolated"] {
            assert!(
                bases.contains(&expected),
                "{} is not seeded: {:?}",
                expected,
                bases
            );
        }
    }

    /// The transcribed set reproduces the three sharpest factors its sources published.
    ///
    /// The derived column is only trustworthy if it agrees with the documents on the cases those
    /// documents state outright: 838x for the six-round build's memory, 75x for the budget
    /// ladder's accounting, and the one large prediction that held to within 1%.
    #[test]
    fn test_the_transcribed_factors_agree_with_their_sources() {
        let rows = transcribed_rows();
        let factor = |claim: &str, quantity: &str| -> f64 {
            rows.iter()
                .find(|row| row.claim == claim)
                .unwrap_or_else(|| panic!("no row for {}", claim))
                .prediction_errors()
                .into_iter()
                .find(|error| error.quantity == quantity)
                .unwrap_or_else(|| panic!("no {} error on {}", quantity, claim))
                .factor
        };

        let build = factor("six-round symbolic build, peak RSS", "peak memory");
        assert!(
            (build - 838.0).abs() < 1.0,
            "resultant-elimination.md 6.8 publishes 838x, derived {:.1}x",
            build
        );
        let ladder = factor(
            "F4 budget ladder, the memory the entry budget bounds",
            "accounted storage",
        );
        assert!(
            (ladder - 75.0).abs() < 1.0,
            "10.1 publishes 75x, derived {:.1}x",
            ladder
        );
        let held = factor(
            "the six-round build's peak RSS, from the multiply's term-product count",
            "peak memory",
        );
        assert!(
            (held - 1.0).abs() < 0.02,
            "56.6 GB predicted against 57.0 GB measured is the prediction that held, derived {:.3}x",
            held
        );
    }

    /// The committed history declares, in the file, that it is append-only, and its count agrees
    /// with its array.
    ///
    /// A contract string that can drift from the code is a liability — `solved.json`'s went stale
    /// and had to be fixed in #290 — and `row_count` disagreeing with the array is the cheapest
    /// evidence of a rewrite that dropped or reordered rows, which the contract forbids.
    #[test]
    fn test_the_committed_history_declares_its_append_only_contract() {
        let history = Json::parse(include_str!(
            "../../../research/cost-model/results/history.json"
        ))
        .expect("committed history.json parses");

        let contract = history
            .get("contract")
            .and_then(Json::as_str)
            .expect("history.json carries a contract string");
        assert_eq!(
            contract, COST_MODEL_HISTORY_CONTRACT,
            "the committed contract must be the one the writer emits, character for character"
        );
        assert!(contract.contains("APPEND-ONLY"));

        let rows = history.get("rows").expect("a rows array").items();
        let count = history
            .get("row_count")
            .and_then(Json::as_int)
            .expect("a row_count");
        assert_eq!(
            count as usize,
            rows.len(),
            "row_count disagrees with the array, so the file was rewritten rather than appended to"
        );
    }

    /// The committed history loads, is self-consistent, and regenerates byte-for-byte from itself.
    ///
    /// "Regenerable from the retained records alone": the renderer reads only the file, and a
    /// second pass over what it wrote produces the same file.
    #[test]
    fn test_the_committed_history_regenerates_from_itself() {
        let text = include_str!("../../../research/cost-model/results/history.json");
        let board = CostModelBoard::load(&Json::parse(text).expect("parses")).expect("every row");
        assert!(board.rows().len() >= 18);

        let rewritten = board.to_json().to_json() + "\n";
        assert_eq!(
            rewritten, text,
            "a round trip through the register must not change the committed file"
        );

        // Seeding is idempotent: no (key, source) pair appears twice, so `--seed` appends nothing
        // on a second run and the append-only history does not grow duplicates.
        let mut seen: Vec<(String, String)> = Vec::new();
        for row in board.rows() {
            let identity = (row.key(), row.source.clone());
            assert!(
                !seen.contains(&identity),
                "{:?} is recorded twice; --seed would duplicate it",
                identity
            );
            seen.push(identity);
        }
    }

    /// The committed register keeps both measurements of the six-round build's peak RSS.
    ///
    /// The acceptance criterion made concrete on real data: #243 made that build 179x smaller, and
    /// the 838x row is still there. A board that overwrote it would report that the estimate had
    /// always been nearly right, which is the opposite of what happened.
    #[test]
    fn test_the_six_round_build_keeps_both_of_its_measurements() {
        let board = CostModelBoard::load(
            &Json::parse(include_str!(
                "../../../research/cost-model/results/history.json"
            ))
            .expect("parses"),
        )
        .expect("every row");

        let trail = board.history_of(
            "resultant-elimination|poseidon31-cico-t16-rf2-rp4|six-round symbolic build, peak RSS",
        );
        assert_eq!(
            trail.len(),
            2,
            "the re-measurement is a second row, not an edit"
        );

        let factor = |row: &CostRow| {
            row.prediction_errors()
                .into_iter()
                .find(|error| error.quantity == "peak memory")
                .expect("a peak memory pair")
                .factor
        };
        assert!(
            (factor(trail[0]) - 838.0).abs() < 1.0,
            "6.8's 838x must survive #243: {:.1}x",
            factor(trail[0])
        );
        assert!(
            (factor(trail[1]) - 4.7).abs() < 0.1,
            "6.12 publishes \"now wrong by 4.7x\": {:.2}x",
            factor(trail[1])
        );
        assert!(
            trail[0].source != trail[1].source,
            "each row cites the section that published it"
        );
        // 57.0 GB -> 0.32 GB is the shrink the issue turns on, and it falls out of the two rows.
        //
        // 175x here against the published 179x, and the difference is arithmetic rather than
        // disagreement: 6.12 divides a rounded 0.32 GB where the row holds the exact 317 872 kB
        // the two instruments agreed on, and the numerator is itself quoted to three figures.
        // Asserted as a range for that reason -- a register that reproduced 179x exactly from
        // these inputs would be fitting itself to the prose.
        let shrink = trail[0]
            .measured_peak_resident_bytes
            .as_ref()
            .unwrap()
            .value as f64
            / trail[1]
                .measured_peak_resident_bytes
                .as_ref()
                .unwrap()
                .value as f64;
        assert!(
            (170.0..180.0).contains(&shrink),
            "{:.0}x is not the published ~179x to within the rounding of either figure",
            shrink
        );
    }

    /// The committed Markdown is exactly what the renderer produces from the committed records.
    ///
    /// The file promises in its own first lines that it is generated and must not be edited. That
    /// promise is worth nothing unless something checks it: a hand-edited table is the failure
    /// mode a generated table exists to remove, and it is invisible in review.
    #[test]
    fn test_the_committed_markdown_is_what_the_renderer_produces() {
        let board = CostModelBoard::load(
            &Json::parse(include_str!(
                "../../../research/cost-model/results/history.json"
            ))
            .expect("parses"),
        )
        .expect("every row");
        assert_eq!(
            board.to_markdown(),
            include_str!("../../../research/cost-model/COST-MODEL.md"),
            "COST-MODEL.md has drifted from its records; regenerate it with \
             `cargo run --release --example cost_model -- --write`"
        );
    }

    /// The committed register renders the unexplained findings and the open prediction it carries.
    #[test]
    fn test_the_committed_register_renders_its_open_and_unexplained_rows() {
        let text = include_str!("../../../research/cost-model/results/history.json");
        let board = CostModelBoard::load(&Json::parse(text).expect("parses")).expect("every row");
        let markdown = board.to_markdown();

        assert!(
            markdown.contains("UNEXPLAINED (#318)"),
            "#318 is on the board"
        );
        assert!(
            markdown.contains("UNEXPLAINED (#319)"),
            "#319 is on the board"
        );
        assert!(
            markdown.contains("Open predictions"),
            "order 13 122 is a prediction nobody has measured"
        );
        assert!(
            markdown.contains("3.0x past the evidence"),
            "the eight-round projection must say how far past its evidence it reaches"
        );
        assert!(
            board
                .open_predictions()
                .iter()
                .any(|row| row.claim.contains("13 122")),
            "the order-13 122 row must be visibly incomplete rather than absent"
        );
    }

    /// An empty register says so rather than rendering a table of nothing.
    #[test]
    fn test_an_empty_register_says_so() {
        let markdown = CostModelBoard::new().to_markdown();
        assert!(markdown.contains("No rows yet"));
        assert!(!markdown.contains("| claim |"));
    }

    /// A completed run with an attributable peak, as the adapter's input.
    fn measured_run() -> crate::grobner::research::RunRecord {
        use crate::grobner::research::{
            challenge, GrobnerFrontier, RunOutcome, RunRecord, Stage, StageCost,
        };
        let manifest = challenge("poseidon-t2-rf4-rp0-planted").expect("registered");
        let mut run = RunRecord::new(&manifest, "as generated");
        run.outcome = RunOutcome::VerifiedWitness;
        run.verification = "through the permutation".to_string();
        run.stages = vec![
            StageCost::new(Stage::Generation, Duration::from_millis(12)),
            StageCost::new(Stage::Grobner, Duration::from_millis(331)),
            StageCost::new(Stage::Conversion, Duration::from_millis(9)),
        ];
        run.frontier = Some(GrobnerFrontier {
            completed: true,
            max_pair_degree: 7,
            highest_completed_degree: Some(7),
            max_matrix_rows: 1_024,
            max_matrix_columns: 2_048,
            peak_live_nonzeros: 410_000,
            peak_estimated_bytes: 6_560_000,
            pairs_reduced: 1_777,
            elements_added: 247,
            quotient_dimension: Some(81),
        });
        run.measured_peak_resident_bytes = Some(74_500_000);
        run.measured_peak_rows_in_process = Some(1);
        run.environment = environment();
        run.reproduce = "cargo run --release --example scoreboard -- row \
                         poseidon-t2-rf4-rp0-planted --write"
            .to_string();
        run
    }

    /// A run emits a cost row the register accepts, carrying only what the run measured.
    ///
    /// #334: `RunRecord` and `CostRow` compute the same storage pair in two places, and the board
    /// gets the second one only if somebody remembers to transcribe it. The adapter removes the
    /// remembering — and must not, in the process, invent the half a run cannot know.
    #[test]
    fn test_a_run_emits_a_row_carrying_only_its_measurements() {
        let row = CostRow::from_run(&measured_run(), "f4");

        assert_eq!(row.subject, "poseidon-t2-rf4-rp0-planted");
        assert_eq!(row.algorithm, "f4");
        assert_eq!(row.formulation, "as generated");
        assert_eq!(row.solving_degree, Some(7), "the run completed at degree 7");

        // Every stage the run reported, as a measured figure.
        let stages: Vec<&str> = row
            .stage_runtimes
            .iter()
            .map(|(name, _)| name.as_str())
            .collect();
        assert_eq!(stages, ["generation", "grobner", "conversion"]);
        assert!(row.stage_runtimes.iter().all(|(_, f)| f.is_measurement()));
        assert_eq!(
            row.measured_runtime.as_ref().map(|f| f.value),
            Some(Duration::from_millis(352)),
            "the total is the sum of the stages, as the run recorded them"
        );
        assert_eq!(
            row.measured_peak_resident_bytes.as_ref().map(|f| f.value),
            Some(74_500_000)
        );
        assert_eq!(row.environment.commit, "deadbeef");
        assert!(row.reproduce.contains("--example scoreboard"));

        // Requirement 1: the predicted half stays empty, so the row is open rather than closed.
        assert!(
            !row.has_prediction(),
            "a run has no prediction to report: {:?}",
            row
        );
        assert!(row.has_measurement());
        assert!(!row.is_complete());
        assert_eq!(row.attribution, Attribution::NoMeasurementYet);

        // Requirement 2: the limiting stage is never guessed.
        assert_eq!(row.limiting_stage, LimitingStage::NotEstablished);

        // And the register takes it.
        let mut board = CostModelBoard::new();
        board.add(row).expect("an emitted row is schema-legal");
        assert_eq!(
            board.open_predictions().len(),
            0,
            "it has no prediction yet"
        );
    }

    /// The adapter does not read the crossed budget as the limiting structure.
    ///
    /// #237 is the case: the entry budget was crossed and 88.4% of the peak was the symbolic
    /// queue, which has no matrix in it at all. An adapter that mapped `max_live_nonzeros` to
    /// `MatrixEntryStorage` would have recorded the wrong structure with the schema's full
    /// authority.
    #[test]
    fn test_a_crossed_budget_does_not_become_a_limiting_stage() {
        use crate::grobner::research::{Limit, RunOutcome, Stage};

        let mut run = measured_run();
        run.outcome = RunOutcome::StoppedAtLimit(Limit {
            resource: "max_live_nonzeros".to_string(),
            detail: "the entry budget of 20000000 was crossed".to_string(),
            degree: Some(11),
            last_completed_stage: Stage::Grobner,
        });
        run.frontier = Some(crate::grobner::research::GrobnerFrontier {
            completed: false,
            ..run.frontier.clone().expect("a frontier")
        });

        let row = CostRow::from_run(&run, "f4");
        assert_eq!(row.limiting_stage, LimitingStage::NotEstablished);
        assert_eq!(
            row.solving_degree, None,
            "a run that stopped did not establish a solving degree, it reached a degree"
        );
    }

    /// A peak measured over a process that ran several rows is not emitted as this row's.
    ///
    /// `measured_peak_is_attributable` is false for a multi-row process: `VmHWM` is a ceiling over
    /// all of them. Copying it into a `measured_` field would turn a bound into a measurement,
    /// which is the error the whole memory vocabulary exists to refuse.
    #[test]
    fn test_a_shared_process_peak_is_not_emitted_as_a_measurement() {
        let mut run = measured_run();
        run.measured_peak_rows_in_process = Some(7);
        let row = CostRow::from_run(&run, "f4");
        assert!(
            row.measured_peak_resident_bytes.is_none(),
            "a seven-row process reports a ceiling, not this row's peak"
        );
        // The stage runtimes are still the row's own, so it is still worth emitting.
        assert!(row.has_measurement());
        CostModelBoard::new().add(row).expect("schema-legal");
    }

    /// A run that measured nothing emits a row that claims nothing, and is still legal.
    #[test]
    fn test_a_run_with_no_stages_emits_a_row_with_no_figures() {
        use crate::grobner::research::{challenge, RunRecord};

        let manifest = challenge("poseidon-t2-rf4-rp0-planted").expect("registered");
        let mut run = RunRecord::new(&manifest, "as generated");
        run.environment = environment();
        let row = CostRow::from_run(&run, "f4");
        assert!(row.stage_runtimes.is_empty());
        assert!(row.measured_runtime.is_none());
        assert!(!row.has_measurement());
        assert_eq!(row.attribution, Attribution::NoMeasurementYet);
        CostModelBoard::new()
            .add(row)
            .expect("a row that claims nothing is legal");
    }

    /// An emitted row round-trips through the register's JSON unchanged.
    #[test]
    fn test_an_emitted_row_round_trips() {
        let row = CostRow::from_run(&measured_run(), "f4");
        let text = row.to_json().to_json();
        let back = CostRow::from_json(&Json::parse(&text).expect("valid")).expect("round trips");
        assert_eq!(back, row);
    }

    /// Naming no run refuses the selection rather than returning every retained run.
    ///
    /// #532's decision made mechanical: the register is curated, so there is no sweep to reach by
    /// accident. The refusal lives in the library rather than in the example's argument parsing,
    /// because a parser that collected no stems must not be the thing standing between an
    /// operator and 80 appended rows.
    #[test]
    fn test_naming_no_run_is_refused_rather_than_selecting_every_run() {
        let runs = vec![measured_run()];
        assert_eq!(
            select_runs_by_stem(&runs, &[]).unwrap_err(),
            RunSelectionError::NoSelector
        );
    }

    /// A named stem selects exactly that run, and a stem that matches nothing is an error.
    ///
    /// A mistyped selector that silently emitted nothing is the other half of the hazard: the
    /// operator would read "emitted 0 rows" as "already up to date".
    #[test]
    fn test_a_named_stem_selects_its_run_and_an_unmatched_stem_is_refused() {
        let runs = vec![measured_run()];
        let stem = runs[0].run_file_stem();

        let selection =
            select_runs_by_stem(&runs, std::slice::from_ref(&stem)).expect("the stem matches");
        assert_eq!(selection.runs.len(), 1);
        assert_eq!(selection.runs[0].run_file_stem(), stem);
        assert!(selection.shadowed.is_empty());

        assert_eq!(
            select_runs_by_stem(&runs, &["no-such-run".to_string()]).unwrap_err(),
            RunSelectionError::UnknownRun {
                stem: "no-such-run".to_string()
            }
        );
    }

    /// Each re-measurement of one problem at one commit is separately selectable — #540.
    ///
    /// The register's `source` is its only link back to evidence. Before the stem carried a
    /// digest, a re-run replaced its predecessor's record file, so the earlier run's figures had
    /// no addressable source and `SelectedRuns::shadowed` existed to report them. Now the two runs
    /// are two files and two stems, and `shadowed` stays empty: a row may be emitted for either,
    /// and each cites a file that holds it.
    #[test]
    fn test_each_remeasurement_of_one_problem_is_separately_selectable() {
        let mut first = measured_run();
        first.stages[1] = crate::grobner::research::StageCost::new(
            crate::grobner::research::Stage::Grobner,
            Duration::from_millis(360),
        );
        let second = measured_run();
        let (first_stem, second_stem) = (first.run_file_stem(), second.run_file_stem());
        assert_ne!(
            first_stem, second_stem,
            "two measurements of one problem at one commit are two records"
        );

        let runs = vec![first, second];
        for (stem, expected) in [(&first_stem, 360), (&second_stem, 331)] {
            let selection =
                select_runs_by_stem(&runs, std::slice::from_ref(stem)).expect("the stem matches");
            assert_eq!(selection.runs.len(), 1);
            assert_eq!(
                selection.runs[0].stages[1].elapsed,
                Duration::from_millis(expected),
                "the stem selects the run whose record file holds it"
            );
            assert!(
                selection.shadowed.is_empty(),
                "nothing is shadowed once every run has its own file: {:?}",
                selection.shadowed
            );
        }
    }

    /// Naming one stem twice selects it once, so a repeated selector cannot double-append.
    #[test]
    fn test_a_stem_named_twice_is_selected_once() {
        let runs = vec![measured_run()];
        let stem = runs[0].run_file_stem();
        let selection =
            select_runs_by_stem(&runs, &[stem.clone(), stem]).expect("the stem matches");
        assert_eq!(selection.runs.len(), 1);
    }

    /// Sixteen retained runs share a record-file stem with another, so they are not addressable.
    ///
    /// The blocker behind #532's decision, pinned to the committed data rather than left in prose:
    /// a register holding a row per run would need one per run and the record tree can name one
    /// per stem. If a
    /// run identity lands (#540) these numbers change and this test is where that shows up.
    #[test]
    fn test_every_retained_run_is_addressable_by_its_own_record_file() {
        use crate::grobner::research::{registry, Scoreboard};

        let history = Json::parse(include_str!(
            "../../../research/scoreboard/results/history.json"
        ))
        .expect("parses");
        let scoreboard = Scoreboard::load(&history, &registry()).expect("every retained run");
        let stems = retained_run_stems(scoreboard.runs());

        let addressable = stems.len();
        let repeats: usize = stems.iter().map(|(_, count)| count - 1).sum();
        assert_eq!(
            addressable + repeats,
            scoreboard.runs().len(),
            "every retained run is either a stem or a repeat of one"
        );
        // #540: the stem carries the measurement's digest, so two runs of one problem at one
        // commit are different names. A repeat here would be two runs that are byte-identical as
        // records, which are interchangeable and so genuinely one addressable thing — but there
        // are none in the committed history, and this asserts the stronger statement.
        assert_eq!(
            repeats, 0,
            "every retained run has a record file that holds it; see #540"
        );
        assert_eq!(addressable, scoreboard.runs().len(), "one stem per run");
    }
}
