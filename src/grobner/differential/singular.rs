//! Singular as an external algebraic oracle, driven by a script and parsed from its output.
//!
//! Singular's `std` is Buchberger/slimgb lineage, so its answers are independent of Zeebra's F4 in
//! *algorithm* and not only in implementation. A second F4 would agree with Zeebra's partly because
//! both implement F4, which is not what an oracle is for.
//!
//! # What this will not do
//! **An oracle that did not answer is never agreement.** Singular exits 0 after a script error —
//! it prints `   ? ...` and carries on — so a successful exit status proves nothing. Every run is
//! required to reach a `@done` marker *and* to have printed no error line, and a timeout, a
//! missing binary, an unsupported characteristic, or a self-inconsistent answer each produce an
//! [`OracleError`] rather than a comparison that quietly passed.
//!
//! # Conventions, each verified rather than assumed
//! * `lp` with variables declared `(x1,x2,...)` orders `x1 > x2 > ...`, and so does Zeebra's
//!   `MonomialOrder::Lexicographic` with `parse(s, ["x1","x2",...])`. `dp` is degree-reverse-lex,
//!   matching `GradedReverseLexicographic`.
//! * `short = 0` prints `x1^2` and `2*x1` rather than `x12` and `2x1`. Zeebra's parser accepts the
//!   former and not the latter.
//! * Coefficients print as the symmetric representative, so `-x2` rather than `6*x2` modulo 7.
//!   Zeebra's parser reads a signed coefficient.
//! * `option(redSB)` is set because `fglm` requires a *reduced* standard basis for its source and
//!   `std` does not produce one unless asked. It also makes `std`'s output the unique reduced
//!   basis, which is what lets a comparison be an equality rather than a containment test.
//! * Each list element is printed on its own marked line rather than the whole ideal at once, so
//!   that no answer has to be split on a separator a coefficient might contain.
//!
//! # Extension fields
//! Singular's `(2^8, a)` Galois fields take their minimal polynomial from an internal table that
//! a script cannot choose, and the choice matters: `Gf256` reduces modulo `x^8+x^4+x^3+x+1` and
//! `Gf256Mq` modulo `x^8+x^4+x^3+x^2+1`, so the same byte has two different squares. The harness
//! therefore declares an *algebraic extension* of the prime field — `ring R = (2,a),...` with
//! `minpoly = a^8+a^4+a^3+a+1` — which is the only form in which the modulus is the harness's to
//! state. Singular echoes `minpoly` back and the echo is **compared** with what was asked for, so
//! a ring that silently reduced by something else is an [`OracleError::ModulusMismatch`] and not a
//! comparison.
//!
//! The two sides do not spell an extension element the same way: Zeebra writes the decimal of its
//! coefficient bit pattern and Singular writes `(a^3+a)`. Every polynomial crossing the boundary
//! is rewritten by [`CaseField::to_singular`] on the way out and [`CaseField::from_singular`] on
//! the way back, so a [`DifferentialCase`] is always in Zeebra's syntax and a committed fixture
//! needs no conversion step to be read.

use std::{
    fmt::{Display, Formatter},
    io,
    path::{Path, PathBuf},
    time::Duration,
};

use super::{
    comparison::DifferentialCase,
    field::{CaseField, FieldTextError},
};
use crate::grobner::external::process::{
    read_output, Invocation, ProcessMeasurement, SpawnError, Supervisor,
};

/// The largest characteristic Singular's prime fields accept.
///
/// A property of Singular and not of the mathematics: `ring R = p,...` requires `p < 2^31`. Zeebra
/// is exercised at Goldilocks and above by its own cross-field agreement, which is the argument
/// §9.1 of the FGLM milestone document sets out.
pub const MAX_CHARACTERISTIC: u64 = 1 << 31;

/// Why the oracle did not produce an answer.
///
/// Every variant is a failure to compare. None of them may be reported as agreement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OracleError {
    /// Singular could not be started: not installed, or not on the path given.
    Unavailable { binary: String, reason: String },

    /// The run exceeded its time limit and was killed.
    Timeout { limit: Duration },

    /// Singular printed an error line. Carries the first one.
    Reported { message: String },

    /// The run ended without reaching the `@done` marker.
    Incomplete,

    /// An expected marker was absent from an otherwise complete run.
    MissingMarker { marker: &'static str },

    /// A marker's value was not of the shape the parser expects.
    Unparsable { marker: &'static str, value: String },

    /// The characteristic is outside what Singular's prime fields accept.
    UnsupportedField { characteristic: u64 },

    /// Singular's ring reduces by a different polynomial than the one it was given.
    ///
    /// **Not a disagreement about mathematics.** Two fields of the same order and different
    /// moduli are both right about their own arithmetic, and nothing can be concluded from
    /// comparing one with the other — so this is an oracle failure, like a timeout.
    ModulusMismatch { asked: u64, reported: String },

    /// A polynomial could not be rewritten between the two sides' syntaxes.
    Untranslatable { reason: String },

    /// Singular's own `std` under lex and its own `fglm` disagreed.
    ///
    /// The oracle contradicting itself. Nothing can be concluded about Zeebra from such a run, so
    /// it is an error and not a finding.
    SelfInconsistent { detail: String },

    /// The filesystem work the run needs failed.
    Io { reason: String },
}

impl Display for OracleError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unavailable { binary, reason } => {
                write!(f, "cannot run {}: {}", binary, reason)
            }
            Self::Timeout { limit } => {
                write!(f, "Singular exceeded its {:?} limit and was killed", limit)
            }
            Self::Reported { message } => write!(f, "Singular reported an error: {}", message),
            Self::Incomplete => write!(f, "Singular stopped before the end of the script"),
            Self::MissingMarker { marker } => {
                write!(f, "Singular printed no {} marker", marker)
            }
            Self::Unparsable { marker, value } => {
                write!(f, "Singular's {} marker reads {:?}", marker, value)
            }
            Self::UnsupportedField { characteristic } => write!(
                f,
                "Singular's prime fields stop below {}, so GF({}) is out of reach",
                MAX_CHARACTERISTIC, characteristic
            ),
            Self::ModulusMismatch { asked, reported } => write!(
                f,
                "the ring was given the modulus {} and reports {}, so the two sides are not in \
                 the same field",
                asked, reported
            ),
            Self::Untranslatable { reason } => write!(f, "{}", reason),
            Self::SelfInconsistent { detail } => {
                write!(f, "Singular disagrees with itself: {}", detail)
            }
            Self::Io { reason } => write!(f, "{}", reason),
        }
    }
}

impl std::error::Error for OracleError {}

impl From<io::Error> for OracleError {
    fn from(e: io::Error) -> Self {
        Self::Io {
            reason: e.to_string(),
        }
    }
}

impl From<FieldTextError> for OracleError {
    fn from(e: FieldTextError) -> Self {
        Self::Untranslatable {
            reason: e.to_string(),
        }
    }
}

impl From<SpawnError> for OracleError {
    fn from(e: SpawnError) -> Self {
        match e {
            SpawnError::Unavailable { binary, reason } => Self::Unavailable { binary, reason },
            SpawnError::Io { reason } => Self::Io { reason },
        }
    }
}

/// What to ask Singular about one ideal.
#[derive(Clone, Debug)]
pub struct OracleQuery<'a> {
    /// A stable identifier, carried through to the case and to any fixture written from it.
    pub name: String,

    /// The field, modulus included.
    pub field: CaseField,

    /// Variable names, declared to Singular in this order.
    ///
    /// None of them may be `a`, which the extension ring reserves for its parameter.
    pub variables: &'a [&'a str],

    /// The generators, in **Zeebra's** syntax. The oracle rewrites them for its own.
    pub system: &'a [String],

    /// The border monomials whose normal forms to ask for, as text.
    ///
    /// Supplied by the caller because they are a property of *Zeebra's* standard monomial basis.
    /// If that basis is wrong the list is wrong too, which is why the bases themselves are
    /// compared separately rather than this being the only check.
    pub border_monomials: &'a [String],
}

/// Something that can answer [`OracleQuery`]s.
///
/// A trait and not just [`SingularOracle`] so that the comparison can be driven by a recorded
/// answer in a test, with no subprocess and no Singular installation, through exactly the code
/// path the live harness uses.
pub trait Oracle {
    /// Everything the comparison needs about the queried ideal.
    fn interrogate(&mut self, query: &OracleQuery<'_>) -> Result<DifferentialCase, OracleError>;
}

/// A Singular installation, and the scratch directory its scripts and output go in.
#[derive(Clone, Debug)]
pub struct SingularOracle {
    binary: String,
    timeout: Duration,
    work_dir: PathBuf,
    keep_files: bool,
    runs: u64,
}

impl SingularOracle {
    /// An oracle using `binary`, with scratch files under `work_dir`.
    ///
    /// The directory is created if it does not exist. Scripts and raw output are deleted after
    /// each run unless `keep_files`, which is what a failing case wants: the script and the output
    /// are what reproduce it by hand.
    pub fn new(
        binary: impl Into<String>,
        work_dir: impl Into<PathBuf>,
        timeout: Duration,
        keep_files: bool,
    ) -> Result<Self, OracleError> {
        let work_dir = work_dir.into();
        std::fs::create_dir_all(&work_dir)?;
        Ok(Self {
            binary: binary.into(),
            timeout,
            work_dir,
            keep_files,
            runs: 0,
        })
    }

    /// One oracle per job, each with its own scratch subdirectory `worker-<i>` under `work_dir`.
    ///
    /// **The subdirectory is what makes concurrency safe.** A run's scratch files are named from
    /// this oracle's own `runs` counter, so two oracles in one directory would hand the same
    /// `run-<pid>-<n>` stem to two concurrent Singular processes — each overwriting the other's
    /// script and parsing the other's output. Used at one job too, so that the layout does not
    /// depend on the degree of concurrency.
    pub fn fleet(
        binary: impl Into<String>,
        work_dir: impl AsRef<Path>,
        timeout: Duration,
        keep_files: bool,
        jobs: usize,
    ) -> Result<Vec<Self>, OracleError> {
        assert!(jobs >= 1, "a fleet needs at least one oracle");
        let binary = binary.into();
        let work_dir = work_dir.as_ref();
        (0..jobs)
            .map(|worker| {
                Self::new(
                    binary.clone(),
                    work_dir.join(format!("worker-{}", worker)),
                    timeout,
                    keep_files,
                )
            })
            .collect()
    }

    /// Singular's build number, which also proves the binary runs.
    ///
    /// Worth calling before a sweep: the alternative is discovering that Singular is absent once
    /// per system for however many systems were asked for.
    pub fn version(&mut self) -> Result<String, OracleError> {
        let output =
            self.run("printf(\"@version %s\", system(\"version\"));\nprintf(\"@done\");\nexit;\n")?;
        marker(&output, "@version")
            .map(str::to_string)
            .ok_or(OracleError::MissingMarker { marker: "@version" })
    }

    /// Everything the comparison needs about one ideal.
    ///
    /// # Errors
    /// Any [`OracleError`]. In particular [`OracleError::SelfInconsistent`] if Singular's `std`
    /// under lex disagrees with its own `fglm`, and [`OracleError::ModulusMismatch`] if an
    /// extension ring does not reduce by the modulus it was given — each of which makes the whole
    /// run unusable rather than making Zeebra wrong.
    pub fn interrogate(
        &mut self,
        query: &OracleQuery<'_>,
    ) -> Result<DifferentialCase, OracleError> {
        if query.field.characteristic() >= MAX_CHARACTERISTIC {
            return Err(OracleError::UnsupportedField {
                characteristic: query.field.characteristic(),
            });
        }
        if let Some(offender) = query
            .variables
            .iter()
            .find(|name| **name == super::field::EXTENSION_PARAMETER)
        {
            return Err(OracleError::Untranslatable {
                reason: format!(
                    "{:?} is the name an extension ring gives its parameter, so a variable cannot \
                     use it",
                    offender
                ),
            });
        }

        let script = self.script(query)?;
        let output = self.run(&script)?;

        // Before anything is read from the ring: a ring reducing by a different polynomial is a
        // different field, and every answer below would be about that field instead. Asserted
        // rather than assumed — Singular is entitled to normalize or reject a `minpoly`.
        if let Some(CaseField::Binary { modulus }) = Some(query.field).filter(|f| f.degree() > 1) {
            let reported = marker(&output, "@minpoly")
                .ok_or(OracleError::MissingMarker { marker: "@minpoly" })?;
            let parsed = CaseField::read_binary_polynomial(reported).map_err(|_| {
                OracleError::ModulusMismatch {
                    asked: modulus,
                    reported: reported.to_string(),
                }
            })?;
            if parsed != modulus {
                return Err(OracleError::ModulusMismatch {
                    asked: modulus,
                    reported: reported.to_string(),
                });
            }
        }

        // Every polynomial Singular printed, back in Zeebra's syntax. The identity over a prime
        // field, so the recorded prime corpus is byte-for-byte what it was.
        let translate = |values: Vec<String>| -> Result<Vec<String>, OracleError> {
            values
                .iter()
                .map(|value| query.field.from_singular(value).map_err(OracleError::from))
                .collect()
        };

        let integer = |marker_name: &'static str| -> Result<i64, OracleError> {
            let value = marker(&output, marker_name).ok_or(OracleError::MissingMarker {
                marker: marker_name,
            })?;
            value.parse().map_err(|_| OracleError::Unparsable {
                marker: marker_name,
                value: value.to_string(),
            })
        };

        let vdim = integer("@vdim")?;
        let oracle_system = translate(collect(&output, "@gen", integer("@gensize")?, "@gen")?)?;
        let grevlex_basis = translate(collect(&output, "@gb", integer("@gbsize")?, "@gb")?)?;
        let lex_basis = translate(collect(&output, "@lex", integer("@lexsize")?, "@lex")?)?;

        let (quotient_dimension, standard_monomials, border_normal_forms) = if vdim < 0 {
            (None, Vec::new(), Vec::new())
        } else {
            // Monomials, so nothing in them is a coefficient — but translated anyway, because a
            // list that is supposed to hold monomials and does not is better caught here.
            let standard = translate(collect(
                &output,
                "@kbase",
                integer("@kbasesize")?,
                "@kbase",
            )?)?;

            // Singular's own cross-check: `fglm` is a third algorithm, so a disagreement with its
            // `std` under lex means the oracle is unsound on this input and nothing can be
            // concluded from it.
            let fglm = translate(collect(&output, "@fglm", integer("@fglmsize")?, "@fglm")?)?;
            if sorted(&fglm) != sorted(&lex_basis) {
                return Err(OracleError::SelfInconsistent {
                    detail: format!(
                        "std under lp gives {:?} and fglm gives {:?}",
                        lex_basis, fglm
                    ),
                });
            }

            let mut normal_forms: Vec<(String, String)> = Vec::new();
            for line in markers(&output, "@nf") {
                match line.split_once(" ; ") {
                    // The monomial is echoed as the script sent it, so it is already Zeebra's
                    // text; only the normal form came out of the ring.
                    Some((monomial, normal_form)) => normal_forms.push((
                        monomial.to_string(),
                        query.field.from_singular(normal_form)?,
                    )),
                    None => {
                        return Err(OracleError::Unparsable {
                            marker: "@nf",
                            value: line.to_string(),
                        })
                    }
                }
            }
            if normal_forms.len() != query.border_monomials.len() {
                return Err(OracleError::Unparsable {
                    marker: "@nf",
                    value: format!(
                        "{} normal forms for {} border monomials",
                        normal_forms.len(),
                        query.border_monomials.len()
                    ),
                });
            }

            (Some(vdim as usize), standard, normal_forms)
        };

        Ok(DifferentialCase {
            name: query.name.clone(),
            field: query.field,
            variables: query.variables.iter().map(|v| v.to_string()).collect(),
            system: query.system.to_vec(),
            oracle_system: Some(oracle_system),
            quotient_dimension,
            grevlex_basis,
            standard_monomials,
            border_normal_forms,
            // Recorded even when positive-dimensional: Singular's lex basis of such an ideal is
            // a perfectly good answer, it is only the *conversion* that has nothing to compare.
            lex_basis: Some(lex_basis),
        })
    }

    /// The script for one query.
    ///
    /// `int` is ring-independent in Singular, so `vd` declared before any ring is still readable
    /// after `setring` — which is what lets the lex section know whether to call `fglm`. Verified,
    /// not assumed.
    ///
    /// **`minpoly` is set in every ring and echoed from the first.** It is a property of a ring and
    /// not of the session, so the lex ring needs its own; and it is printed so that the modulus the
    /// two sides reduce by can be compared rather than assumed.
    ///
    /// # Errors
    /// [`OracleError::Untranslatable`] if a generator cannot be written in Singular's syntax for
    /// this field.
    fn script(&self, query: &OracleQuery<'_>) -> Result<String, OracleError> {
        let coefficients = query.field.singular_coefficients();
        let minpoly = query.field.singular_minpoly();
        let vars = query.variables.join(",");
        let generators = query
            .system
            .iter()
            .map(|generator| query.field.to_singular(generator))
            .collect::<Result<Vec<String>, FieldTextError>>()?
            .join(",");

        // `minpoly` must be assigned after the ring exists and before anything is built in it.
        let declare = |name: &str, order: &str| -> String {
            let mut out = format!("ring {} = {},({}),{};\n", name, coefficients, vars, order);
            if let Some(minpoly) = &minpoly {
                out.push_str(&format!("minpoly = {};\n", minpoly));
            }
            out.push_str("short = 0;\n");
            out
        };

        let mut script = String::new();
        script.push_str("option(redSB);\n");
        script.push_str("int vd;\nint k;\n");
        script.push_str(&declare("Rsrc", "dp"));
        if minpoly.is_some() {
            script.push_str("printf(\"@minpoly %s\", minpoly);\n");
        }
        script.push_str(&format!("ideal I = {};\n", generators));
        // Echoed before anything is computed from it. An oracle that read the system differently
        // has not disagreed about mathematics, and nothing it says afterwards means anything — so
        // what it read is the first thing the comparison checks. See `Check::OracleInput`.
        script.push_str("printf(\"@gensize %s\", ncols(I));\n");
        script.push_str("for (k = 1; k <= ncols(I); k++) { printf(\"@gen %s\", I[k]); }\n");
        script.push_str("ideal G = std(I);\n");
        script.push_str("vd = vdim(G);\n");
        script.push_str("printf(\"@vdim %s\", vd);\n");
        script.push_str("printf(\"@gbsize %s\", ncols(G));\n");
        script.push_str("for (k = 1; k <= ncols(G); k++) { printf(\"@gb %s\", G[k]); }\n");

        // Guarded: `kbase` on a positive-dimensional ideal does not error, it returns something
        // that is not a basis of a finite quotient. Asking only when `vdim` says the quotient is
        // finite is what keeps the answer meaningful.
        script.push_str("if (vd >= 0)\n{\n");
        script.push_str("  ideal B = kbase(G);\n");
        script.push_str("  printf(\"@kbasesize %s\", ncols(B));\n");
        script.push_str("  for (k = 1; k <= ncols(B); k++) { printf(\"@kbase %s\", B[k]); }\n");
        for monomial in query.border_monomials {
            script.push_str(&format!(
                "  printf(\"@nf %s ; %s\", \"{}\", reduce({}, G));\n",
                monomial, monomial
            ));
        }
        script.push_str("}\n");

        script.push_str(&declare("Rlex", "lp"));
        script.push_str("ideal Glex = std(fetch(Rsrc, I));\n");
        script.push_str("printf(\"@lexsize %s\", ncols(Glex));\n");
        script.push_str("for (k = 1; k <= ncols(Glex); k++) { printf(\"@lex %s\", Glex[k]); }\n");
        script.push_str("if (vd >= 0)\n{\n");
        script.push_str("  ideal Gfglm = fglm(Rsrc, G);\n");
        script.push_str("  printf(\"@fglmsize %s\", ncols(Gfglm));\n");
        script.push_str(
            "  for (k = 1; k <= ncols(Gfglm); k++) { printf(\"@fglm %s\", Gfglm[k]); }\n",
        );
        script.push_str("}\n");
        script.push_str("printf(\"@done\");\nexit;\n");
        Ok(script)
    }

    /// Run a script and return its combined output.
    fn run(&mut self, script: &str) -> Result<String, OracleError> {
        self.run_measured(script).map(|(output, _)| output)
    }

    /// Run a script, returning its combined output and what the run cost.
    ///
    /// The one place a Singular process is started, shared with
    /// [`SingularSolver`](crate::grobner::external::SingularSolver) so that the competitive
    /// harness and the differential harness cannot drift into two different invocations of the
    /// same tool.
    ///
    /// Output goes to a file rather than a pipe, and the wait is a poll rather than a read: a
    /// child whose pipe fills while the parent is not reading blocks forever, which is exactly the
    /// case a timeout exists for and exactly the case a pipe would deadlock in. Both properties
    /// now come from [`Supervisor`], along with the measurement.
    pub(crate) fn run_measured(
        &mut self,
        script: &str,
    ) -> Result<(String, ProcessMeasurement), OracleError> {
        self.runs += 1;
        let stem = format!("run-{}-{}", std::process::id(), self.runs);
        let script_path = self.work_dir.join(format!("{}.sing", stem));
        let output_path = self.work_dir.join(format!("{}.out", stem));

        std::fs::write(&script_path, script)?;

        let invocation = Invocation::new(&self.binary, &self.work_dir, &output_path)
            .arg("-q")
            .arg("--no-warn")
            .arg(&script_path);
        let measurement = match Supervisor::new(self.timeout)
            .with_poll_interval(Duration::from_millis(5))
            .run(&invocation)
        {
            Ok(measurement) => measurement,
            Err(e) => {
                self.discard(&script_path, &output_path);
                return Err(OracleError::from(e));
            }
        };

        let output = read_output(&output_path);
        if measurement.timed_out {
            // Kept regardless of `keep_files`: a timeout is the one outcome where the script is
            // the whole evidence and there is no parsed answer to report instead.
            return Err(OracleError::Timeout {
                limit: self.timeout,
            });
        }
        self.discard(&script_path, &output_path);

        if let Some(message) = error_line(&output) {
            return Err(OracleError::Reported { message });
        }
        if marker(&output, "@done").is_none() && !output.contains("@done") {
            return Err(OracleError::Incomplete);
        }
        Ok((output, measurement))
    }

    /// Remove a run's files unless they were asked to be kept.
    fn discard(&self, script: &Path, output: &Path) {
        if self.keep_files {
            return;
        }
        let _ = std::fs::remove_file(script);
        let _ = std::fs::remove_file(output);
    }

    /// Where this oracle's scratch files go.
    pub fn work_dir(&self) -> &Path {
        &self.work_dir
    }

    /// The binary this oracle runs, for an error message that names it.
    pub fn binary(&self) -> &str {
        &self.binary
    }

    /// The time limit this oracle enforces per run.
    pub fn timeout(&self) -> Duration {
        self.timeout
    }
}

impl Oracle for SingularOracle {
    fn interrogate(&mut self, query: &OracleQuery<'_>) -> Result<DifferentialCase, OracleError> {
        SingularOracle::interrogate(self, query)
    }
}

/// Singular's first error line, if it printed one.
///
/// Singular exits 0 after a script error, so this and not the status is what says a run failed.
/// The lines look like `   ? \`x3\` is not defined`.
pub(crate) fn error_line(output: &str) -> Option<String> {
    output
        .lines()
        .map(str::trim_start)
        .find(|line| line.starts_with('?'))
        .map(|line| line.trim_start_matches(['?', ' ']).to_string())
}

/// The value of the first line beginning with `marker `.
pub(crate) fn marker<'a>(output: &'a str, name: &str) -> Option<&'a str> {
    markers(output, name).into_iter().next()
}

/// The values of every line beginning with `marker `, in the order printed.
pub(crate) fn markers<'a>(output: &'a str, name: &str) -> Vec<&'a str> {
    let prefix = format!("{} ", name);
    output
        .lines()
        .filter_map(|line| line.strip_prefix(&prefix))
        .map(str::trim)
        .collect()
}

/// `expected` lines of a marker, with zeros dropped, or an error if the count was wrong.
///
/// The slot count Singular reported and the number of lines it printed must agree. They can differ
/// for a reason worth catching: `printf("%s", ideal)` on an empty ideal prints `0`, so a list whose
/// elements were printed individually is the only kind whose emptiness is unambiguous — and that is
/// only true if the count is checked.
///
/// **Zeros are dropped, after the count has been checked.** The count is `ncols` and not `size`,
/// because those differ: `size` counts an ideal's *non-zero* generators and `ncols` its slots, so
/// `ideal I = 0, x1^2` has `size` 1 and `ncols` 2 with `I[1]` the zero — and a loop bounded by
/// `size` prints the zero and skips `x1^2`. Found by the harness's own oracle-input check, on seed
/// 55915 over GF(2). Iterating the slots keeps the count meaningful; dropping the zeros afterwards
/// is right because none of these lists — a generating set, a reduced basis, a monomial basis — has
/// a zero as a meaningful element.
pub(crate) fn collect(
    output: &str,
    name: &str,
    expected: i64,
    marker_name: &'static str,
) -> Result<Vec<String>, OracleError> {
    let values = markers(output, name);
    let expected = usize::try_from(expected).map_err(|_| OracleError::Unparsable {
        marker: marker_name,
        value: expected.to_string(),
    })?;
    if values.len() != expected {
        return Err(OracleError::Unparsable {
            marker: marker_name,
            value: format!(
                "{} values for a reported size of {}",
                values.len(),
                expected
            ),
        });
    }
    Ok(values
        .into_iter()
        .filter(|value| *value != "0")
        .map(str::to_string)
        .collect())
}

/// A list of polynomial strings, sorted, for comparing two of Singular's own answers.
///
/// Textual and therefore weaker than comparing values: it would call `x1+x2` and `x2+x1` different
/// bases. Singular prints a polynomial canonically under the ring's order, so the two answers
/// being compared here are printed the same way — and a false [`OracleError::SelfInconsistent`]
/// costs a discarded run, where a false agreement would cost a missed bug.
fn sorted(basis: &[String]) -> Vec<String> {
    let mut basis = basis.to_vec();
    basis.sort();
    basis
}

#[cfg(test)]
mod tests {
    use super::{
        collect, error_line, marker, markers, sorted, CaseField, OracleError, OracleQuery,
        SingularOracle,
    };
    use std::{collections::BTreeSet, path::PathBuf, time::Duration};

    /// A fleet gives every worker its own existing scratch directory, under the one asked for.
    ///
    /// Scratch names are a per-oracle counter, so two workers in one directory would collide.
    /// Needs no Singular: the directories are the whole claim.
    #[test]
    fn test_a_fleet_gives_every_worker_its_own_scratch_directory() {
        let root = std::env::temp_dir().join(format!(
            "zeebra-fleet-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let oracles = SingularOracle::fleet("Singular", &root, Duration::from_secs(1), false, 6)
            .expect("a writable scratch directory");
        assert_eq!(oracles.len(), 6);

        let directories: BTreeSet<PathBuf> = oracles
            .iter()
            .map(|oracle| oracle.work_dir().to_path_buf())
            .collect();
        assert_eq!(directories.len(), 6, "two workers share a directory");
        for directory in &directories {
            assert!(
                directory.is_dir(),
                "{} was not created",
                directory.display()
            );
            assert!(directory.starts_with(&root));
        }

        let _ = std::fs::remove_dir_all(&root);
    }

    /// A fleet of one still gets its own subdirectory, so the layout does not depend on `--jobs`.
    #[test]
    fn test_a_fleet_of_one_is_still_a_subdirectory() {
        let root = std::env::temp_dir().join(format!(
            "zeebra-fleet-one-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let oracles = SingularOracle::fleet("Singular", &root, Duration::from_secs(1), false, 1)
            .expect("a writable scratch directory");
        assert_eq!(oracles[0].work_dir(), root.join("worker-0"));
        let _ = std::fs::remove_dir_all(&root);
    }

    /// An extension query declares its modulus in every ring and echoes it from the first.
    ///
    /// `minpoly` is a property of a ring and not of the session, so the lex ring needs its own;
    /// and the echo is what lets the modulus be compared instead of assumed. A prime query must
    /// carry neither, or the recorded prime corpus would have been swept under a different script.
    #[test]
    fn test_an_extension_query_declares_and_echoes_its_modulus() {
        let oracle = SingularOracle::new(
            "Singular",
            std::env::temp_dir(),
            Duration::from_secs(1),
            false,
        )
        .expect("a writable scratch directory");
        let variables = ["x1", "x2"];
        let system = ["10*x1^2+x2".to_string()];
        let query = |field: CaseField| OracleQuery {
            name: "t".to_string(),
            field,
            variables: &variables,
            system: &system,
            border_monomials: &[],
        };

        let extension = oracle
            .script(&query(CaseField::binary(0x11B)))
            .expect("the system is translatable");
        assert_eq!(
            extension.matches("minpoly = a^8+a^4+a^3+a+1;").count(),
            2,
            "every ring needs its own minpoly: {}",
            extension
        );
        assert!(extension.contains("ring Rsrc = (2,a),(x1,x2),dp;"));
        assert!(extension.contains("ring Rlex = (2,a),(x1,x2),lp;"));
        assert!(extension.contains("printf(\"@minpoly %s\", minpoly);"));
        // The coefficient crossed into Singular's syntax: `10` is the bit pattern of a^3 + a.
        assert!(
            extension.contains("ideal I = (a^3+a)*x1^2+x2;"),
            "the generator was not rewritten: {}",
            extension
        );

        let prime = oracle
            .script(&query(CaseField::prime(13)))
            .expect("a prime field needs no rewriting");
        assert!(prime.contains("ring Rsrc = 13,(x1,x2),dp;"));
        assert!(!prime.contains("minpoly"));
        assert!(prime.contains("ideal I = 10*x1^2+x2;"));
    }

    /// A variable named after the extension parameter is refused, not silently shadowed.
    #[test]
    fn test_a_variable_named_like_the_extension_parameter_is_refused() {
        let mut oracle = SingularOracle::new(
            "Singular",
            std::env::temp_dir(),
            Duration::from_secs(1),
            false,
        )
        .expect("a writable scratch directory");
        let variables = ["a", "x2"];
        let system = ["a+x2".to_string()];
        let error = oracle
            .interrogate(&OracleQuery {
                name: "t".to_string(),
                field: CaseField::binary(0x11B),
                variables: &variables,
                system: &system,
                border_monomials: &[],
            })
            .expect_err("`a` is the extension parameter, so it cannot also be a variable");
        assert!(
            matches!(error, OracleError::Untranslatable { .. }),
            "{:?}",
            error
        );
    }

    /// An error line is found wherever Singular put it, with the marker stripped.
    #[test]
    fn test_an_error_line_is_detected() {
        let output = "@vdim 4\n   ? `x3` is not defined\n@done\n";
        assert_eq!(error_line(output).as_deref(), Some("`x3` is not defined"));
    }

    /// Clean output has no error line, including output that merely contains a question mark.
    #[test]
    fn test_clean_output_has_no_error_line() {
        assert_eq!(error_line("@vdim 4\n@done\n"), None);
        assert_eq!(error_line("@nf x1^2 ; x1*? \n@done\n"), None);
    }

    /// A marker's value is the rest of its line, trimmed.
    #[test]
    fn test_a_marker_reads_the_rest_of_its_line() {
        let output = "@vdim 8\n@gb x1^2-1\n@gb x2-x1\n";
        assert_eq!(marker(output, "@vdim"), Some("8"));
        assert_eq!(markers(output, "@gb"), vec!["x1^2-1", "x2-x1"]);
    }

    /// A marker that is a prefix of another does not collect the other's lines.
    ///
    /// `@gb` and `@gbsize` differ only by a suffix, so the space in the prefix is load-bearing.
    #[test]
    fn test_a_marker_does_not_match_a_longer_one() {
        let output = "@gbsize 2\n@gb x1\n@gb x2\n";
        assert_eq!(markers(output, "@gb"), vec!["x1", "x2"]);
        assert_eq!(marker(output, "@gbsize"), Some("2"));
    }

    /// A list whose line count disagrees with the reported size is an error, not a short list.
    #[test]
    fn test_a_short_list_is_an_error() {
        let output = "@gbsize 3\n@gb x1\n@gb x2\n";
        assert!(matches!(
            collect(output, "@gb", 3, "@gb"),
            Err(OracleError::Unparsable { marker: "@gb", .. })
        ));
    }

    /// A reported size of zero means the empty list, unambiguously.
    #[test]
    fn test_an_empty_list_is_empty() {
        assert_eq!(
            collect("@kbasesize 0\n", "@kbase", 0, "@kbase"),
            Ok(Vec::new())
        );
    }

    /// A zero slot is dropped, after the count has been checked against it.
    ///
    /// `ideal I = 0, x1^2` has two slots and one non-zero generator, and Singular's `size` reports
    /// the second — so the slots are what is iterated and the zeros are removed afterwards.
    #[test]
    fn test_a_zero_slot_is_dropped_after_the_count_is_checked() {
        let output = "@gensize 2\n@gen 0\n@gen x1^2\n";
        assert_eq!(
            collect(output, "@gen", 2, "@gensize"),
            Ok(vec!["x1^2".to_string()])
        );
        // The count is against the slots, so a list whose zero was not printed is still an error.
        assert!(matches!(
            collect("@gensize 2\n@gen x1^2\n", "@gen", 2, "@gensize"),
            Err(OracleError::Unparsable { .. })
        ));
    }

    /// A negative reported size is an error rather than a wrapped length.
    #[test]
    fn test_a_negative_size_is_an_error() {
        assert!(matches!(
            collect("@gbsize -1\n", "@gb", -1, "@gbsize"),
            Err(OracleError::Unparsable {
                marker: "@gbsize",
                ..
            })
        ));
    }

    /// Sorting is by text and is order-insensitive, which is all the self-check needs.
    #[test]
    fn test_sorting_normalizes_list_order() {
        let a = vec!["x2^2-1".to_string(), "x1-x2".to_string()];
        let b = vec!["x1-x2".to_string(), "x2^2-1".to_string()];
        assert_eq!(sorted(&a), sorted(&b));
    }
}
