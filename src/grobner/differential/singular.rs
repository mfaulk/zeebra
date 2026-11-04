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

use std::{
    fmt::{Display, Formatter},
    fs::File,
    io,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant},
};

use super::comparison::DifferentialCase;

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

/// What to ask Singular about one ideal.
#[derive(Clone, Debug)]
pub struct OracleQuery<'a> {
    /// A stable identifier, carried through to the case and to any fixture written from it.
    pub name: String,

    /// The field's characteristic.
    pub characteristic: u64,

    /// Variable names, declared to Singular in this order.
    pub variables: &'a [&'a str],

    /// The generators, in a syntax both Zeebra and Singular parse.
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
    /// under lex disagrees with its own `fglm`, which makes the whole run unusable rather than
    /// making Zeebra wrong.
    pub fn interrogate(
        &mut self,
        query: &OracleQuery<'_>,
    ) -> Result<DifferentialCase, OracleError> {
        if query.characteristic >= MAX_CHARACTERISTIC {
            return Err(OracleError::UnsupportedField {
                characteristic: query.characteristic,
            });
        }

        let script = self.script(query);
        let output = self.run(&script)?;

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
        let grevlex_basis = collect(&output, "@gb", integer("@gbsize")?, "@gb")?;
        let lex_basis = collect(&output, "@lex", integer("@lexsize")?, "@lex")?;

        let (quotient_dimension, standard_monomials, border_normal_forms) = if vdim < 0 {
            (None, Vec::new(), Vec::new())
        } else {
            let standard = collect(&output, "@kbase", integer("@kbasesize")?, "@kbase")?;

            // Singular's own cross-check: `fglm` is a third algorithm, so a disagreement with its
            // `std` under lex means the oracle is unsound on this input and nothing can be
            // concluded from it.
            let fglm = collect(&output, "@fglm", integer("@fglmsize")?, "@fglm")?;
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
                    Some((monomial, normal_form)) => {
                        normal_forms.push((monomial.to_string(), normal_form.to_string()))
                    }
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
            characteristic: query.characteristic,
            variables: query.variables.iter().map(|v| v.to_string()).collect(),
            system: query.system.to_vec(),
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
    fn script(&self, query: &OracleQuery<'_>) -> String {
        let p = query.characteristic;
        let vars = query.variables.join(",");
        let generators = query.system.join(",");

        let mut script = String::new();
        script.push_str("option(redSB);\n");
        script.push_str("int vd;\nint k;\n");
        script.push_str(&format!("ring Rsrc = {},({}),dp;\n", p, vars));
        script.push_str("short = 0;\n");
        script.push_str(&format!("ideal I = {};\n", generators));
        script.push_str("ideal G = std(I);\n");
        script.push_str("vd = vdim(G);\n");
        script.push_str("printf(\"@vdim %s\", vd);\n");
        script.push_str("printf(\"@gbsize %s\", size(G));\n");
        script.push_str("for (k = 1; k <= size(G); k++) { printf(\"@gb %s\", G[k]); }\n");

        // Guarded: `kbase` on a positive-dimensional ideal does not error, it returns something
        // that is not a basis of a finite quotient. Asking only when `vdim` says the quotient is
        // finite is what keeps the answer meaningful.
        script.push_str("if (vd >= 0)\n{\n");
        script.push_str("  ideal B = kbase(G);\n");
        script.push_str("  printf(\"@kbasesize %s\", size(B));\n");
        script.push_str("  for (k = 1; k <= size(B); k++) { printf(\"@kbase %s\", B[k]); }\n");
        for monomial in query.border_monomials {
            script.push_str(&format!(
                "  printf(\"@nf %s ; %s\", \"{}\", reduce({}, G));\n",
                monomial, monomial
            ));
        }
        script.push_str("}\n");

        script.push_str(&format!("ring Rlex = {},({}),lp;\n", p, vars));
        script.push_str("short = 0;\n");
        script.push_str("ideal Glex = std(fetch(Rsrc, I));\n");
        script.push_str("printf(\"@lexsize %s\", size(Glex));\n");
        script.push_str("for (k = 1; k <= size(Glex); k++) { printf(\"@lex %s\", Glex[k]); }\n");
        script.push_str("if (vd >= 0)\n{\n");
        script.push_str("  ideal Gfglm = fglm(Rsrc, G);\n");
        script.push_str("  printf(\"@fglmsize %s\", size(Gfglm));\n");
        script
            .push_str("  for (k = 1; k <= size(Gfglm); k++) { printf(\"@fglm %s\", Gfglm[k]); }\n");
        script.push_str("}\n");
        script.push_str("printf(\"@done\");\nexit;\n");
        script
    }

    /// Run a script and return its combined output.
    ///
    /// Output goes to a file rather than a pipe, and the wait is a poll rather than a read: a
    /// child whose pipe fills while the parent is not reading blocks forever, which is exactly the
    /// case a timeout exists for and exactly the case a pipe would deadlock in.
    fn run(&mut self, script: &str) -> Result<String, OracleError> {
        self.runs += 1;
        let stem = format!("run-{}-{}", std::process::id(), self.runs);
        let script_path = self.work_dir.join(format!("{}.sing", stem));
        let output_path = self.work_dir.join(format!("{}.out", stem));

        std::fs::write(&script_path, script)?;
        let output_file = File::create(&output_path)?;
        let error_file = output_file.try_clone()?;

        let child = Command::new(&self.binary)
            .arg("-q")
            .arg("--no-warn")
            .arg(&script_path)
            .current_dir(&self.work_dir)
            .stdin(Stdio::null())
            .stdout(Stdio::from(output_file))
            .stderr(Stdio::from(error_file))
            .spawn();

        let mut child = match child {
            Ok(child) => child,
            Err(e) => {
                self.discard(&script_path, &output_path);
                return Err(OracleError::Unavailable {
                    binary: self.binary.clone(),
                    reason: e.to_string(),
                });
            }
        };

        let deadline = Instant::now() + self.timeout;
        let timed_out = loop {
            match child.try_wait()? {
                Some(_) => break false,
                None if Instant::now() >= deadline => {
                    // Killed and reaped: leaving it would accumulate one zombie per timeout over
                    // a sweep of hundreds of systems.
                    let _ = child.kill();
                    let _ = child.wait();
                    break true;
                }
                None => std::thread::sleep(Duration::from_millis(5)),
            }
        };

        let output = std::fs::read_to_string(&output_path).unwrap_or_default();
        if timed_out {
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
        Ok(output)
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
fn error_line(output: &str) -> Option<String> {
    output
        .lines()
        .map(str::trim_start)
        .find(|line| line.starts_with('?'))
        .map(|line| line.trim_start_matches(['?', ' ']).to_string())
}

/// The value of the first line beginning with `marker `.
fn marker<'a>(output: &'a str, name: &str) -> Option<&'a str> {
    markers(output, name).into_iter().next()
}

/// The values of every line beginning with `marker `, in the order printed.
fn markers<'a>(output: &'a str, name: &str) -> Vec<&'a str> {
    let prefix = format!("{} ", name);
    output
        .lines()
        .filter_map(|line| line.strip_prefix(&prefix))
        .map(str::trim)
        .collect()
}

/// `expected` values of a marker, or an error naming the marker whose count was wrong.
///
/// The size Singular reported and the number of lines it printed must agree. They can differ for a
/// reason worth catching: `printf("%s", ideal)` on an empty ideal prints `0`, so a list whose
/// elements were printed individually is the only kind whose emptiness is unambiguous — and that
/// is only true if the count is checked.
fn collect(
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
    Ok(values.into_iter().map(str::to_string).collect())
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
    use super::{collect, error_line, marker, markers, sorted, OracleError};

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
