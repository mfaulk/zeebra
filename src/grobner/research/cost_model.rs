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
//! about whether a derivation invariant holds and [`research::manifest::Provenance`](super::Provenance)
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
//! Prediction error is **derived** by [`CostRow::prediction_errors`] and never authored. The stored
//! form carries it for a machine consumer's convenience and [`CostRow::from_json`] ignores what is
//! there, so a typo in the file cannot become a published finding.

use std::{collections::BTreeMap, fmt::Write as _, time::Duration};

use super::{Environment, Json};

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
    /// **A legitimate attribution.** #318 and #319 are both of this kind and both belong on the
    /// board: a schema that forced a cause would have one invented for it.
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

    /// The error as JSON, under a name that cannot be mistaken for an input.
    fn to_json(&self) -> Json {
        Json::object([
            ("quantity", Json::string(&self.quantity)),
            ("predicted", Json::string(&self.predicted)),
            ("measured", Json::string(&self.measured)),
            // Rendered as text because `Json` has no float, and because this object is a
            // convenience for a reader rather than an input: `from_json` recomputes it.
            ("factor", Json::string(format!("{:.4}", self.factor))),
            (
                "relative_percent",
                Json::string(format!("{:+.2}", self.relative_percent)),
            ),
        ])
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
                |bytes| bytes_text(bytes),
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
                |bytes| bytes_text(bytes),
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
        let errors = self.prediction_errors();
        if !errors.is_empty() {
            // Under `derived` so that no reader and no reimplementation mistakes it for an input.
            fields.push((
                "derived",
                Json::object([
                    (
                        "note",
                        Json::string(
                            "computed from the predicted and measured fields; recomputed on load \
                             and never read back",
                        ),
                    ),
                    (
                        "prediction_errors",
                        Json::Array(errors.iter().map(PredictionError::to_json).collect()),
                    ),
                ]),
            ));
        } else {
            fields.push((
                "derived",
                Json::object([(
                    "note",
                    Json::string("no prediction on this row has been measured yet"),
                )]),
            ));
        }
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
                let errors = row.prediction_errors();
                let _ = writeln!(
                    out,
                    "| {} | `{}` | {} | {} | {} | {} | `{}` | {} | {} |",
                    row.claim,
                    row.subject,
                    predicted_cell(row),
                    measured_cell(row),
                    error_cell(&errors),
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
            "{} {} {}",
            quantity.figure.value, quantity.unit, quantity.name
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
            "{} {} {}",
            quantity.figure.value, quantity.unit, quantity.name
        ));
    }
    if parts.is_empty() {
        "— _nothing measured_".to_string()
    } else {
        parts.join("; ")
    }
}

/// The derived error cell, or a note that there is nothing to divide.
fn error_cell(errors: &[PredictionError]) -> String {
    if errors.is_empty() {
        return "_open_".to_string();
    }
    errors
        .iter()
        .map(|error| format!("{}: **{:.2}x**", error.quantity, error.factor))
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
/// Takes `f64` because [`PredictionError`] renders both sides of a ratio through it.
fn bytes_text(bytes: f64) -> String {
    const GIB: f64 = (1u64 << 30) as f64;
    const MIB: f64 = (1u64 << 20) as f64;
    if bytes >= GIB {
        format!("{:.2} GB", bytes / GIB)
    } else if bytes >= MIB {
        format!("{:.1} MB", bytes / MIB)
    } else {
        format!("{:.0} B", bytes)
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
        format!("{:.1} ms", seconds * 1e3)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn environment() -> Environment {
        Environment {
            commit: "deadbeef".to_string(),
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

    /// A stored error column is ignored on load and recomputed from the predicted and measured
    /// columns, so a hand-edited `derived` object cannot become a published finding.
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

        // Rewrite the stored `derived` object with a figure nobody computed.
        let Json::Object(mut fields) = original.to_json() else {
            panic!("a row serialises as an object");
        };
        for (key, value) in fields.iter_mut() {
            if key == "derived" {
                *value = Json::object([(
                    "prediction_errors",
                    Json::Array(vec![Json::object([
                        ("quantity", Json::string("runtime")),
                        ("factor", Json::string("1.0000")),
                    ])]),
                )]);
            }
        }
        let tampered = Json::Object(fields).to_json();
        assert!(tampered.contains("1.0000"), "the tampered value is stored");

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
        assert_eq!(bytes_text((2u64 << 20) as f64), "2.0 MB");
        assert_eq!(bytes_text((3u64 << 30) as f64), "3.00 GB");
        assert_eq!(duration_text(Duration::from_millis(12)), "12.0 ms");
        assert_eq!(duration_text(Duration::from_secs(90)), "1.50 min");
        assert_eq!(duration_text(Duration::from_secs(7_200)), "2.00 h");
        assert_eq!(duration_text(Duration::from_secs(172_800)), "2.00 d");
        assert_eq!(error_cell(&[]), "_open_");
    }

    /// An empty register says so rather than rendering a table of nothing.
    #[test]
    fn test_an_empty_register_says_so() {
        let markdown = CostModelBoard::new().to_markdown();
        assert!(markdown.contains("No rows yet"));
        assert!(!markdown.contains("| claim |"));
    }
}
