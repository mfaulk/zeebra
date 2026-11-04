//! Recorded oracle answers, as committed Rust literals.
//!
//! The repository already takes this approach for the FGLM lex bases: a Singular script emits Rust
//! source, the source is committed, and ordinary tests check against it. The same convention is
//! used here rather than a serialized data format, for the same two reasons — the fixtures are
//! type-checked by the compiler, and CI needs no parser and no new dependency to read them.
//!
//! A fixture holds *everything* the comparison checks, not only the final lex basis: the source
//! basis, the quotient dimension, the standard monomials, and the normal form of every border
//! monomial. So a committed fixture exercises the multiplication operators column by column with
//! no Singular installation present.

use super::comparison::DifferentialCase;

/// One ideal and every answer an oracle gave about it.
///
/// The `&'static` mirror of [`DifferentialCase`], so that a generated module is a table of
/// literals rather than a pile of `String::from` calls.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DifferentialFixture {
    /// A stable identifier. Generated fixtures are named after their seed, prime and variable
    /// count, so the name alone reproduces the system.
    pub name: &'static str,

    /// The field's characteristic.
    pub characteristic: u64,

    /// Variable names, in declaration order.
    pub variables: &'static [&'static str],

    /// The generators of the ideal.
    pub system: &'static [&'static str],

    /// `dim R/I`, or `None` where the oracle called the ideal positive-dimensional.
    pub quotient_dimension: Option<usize>,

    /// The oracle's reduced grevlex Gröbner basis.
    pub grevlex_basis: &'static [&'static str],

    /// The oracle's standard monomials.
    pub standard_monomials: &'static [&'static str],

    /// `(border monomial, its normal form)` per distinct border monomial.
    pub border_normal_forms: &'static [(&'static str, &'static str)],

    /// The oracle's reduced lex Gröbner basis, or `None` where it was not recorded.
    pub lex_basis: Option<&'static [&'static str]>,
}

impl DifferentialFixture {
    /// The owned form the comparison works on.
    pub fn to_case(&self) -> DifferentialCase {
        DifferentialCase {
            name: self.name.to_string(),
            characteristic: self.characteristic,
            variables: self.variables.iter().map(|v| v.to_string()).collect(),
            system: self.system.iter().map(|s| s.to_string()).collect(),
            quotient_dimension: self.quotient_dimension,
            grevlex_basis: self.grevlex_basis.iter().map(|s| s.to_string()).collect(),
            standard_monomials: self
                .standard_monomials
                .iter()
                .map(|s| s.to_string())
                .collect(),
            border_normal_forms: self
                .border_normal_forms
                .iter()
                .map(|(monomial, normal_form)| (monomial.to_string(), normal_form.to_string()))
                .collect(),
            lex_basis: self
                .lex_basis
                .map(|basis| basis.iter().map(|s| s.to_string()).collect()),
        }
    }
}

/// A generated Rust module holding `cases` as a table of [`DifferentialFixture`]s.
///
/// Emitted rather than written by hand, and marked as such: a fixture edited by hand is no longer
/// a record of what an independent implementation said, which is the only thing that makes it
/// worth committing.
pub fn emit_fixture_module(cases: &[DifferentialCase], singular_version: &str) -> String {
    let mut out = String::new();

    out.push_str("//! Oracle answers recorded from Singular, committed as literals.\n");
    out.push_str("//!\n");
    out.push_str("//! **Generated. Do not edit by hand.** Regenerate with\n");
    out.push_str("//!\n");
    out.push_str("//! ```text\n");
    out.push_str("//! cargo run --release --bin zeebra-differential -- \\\n");
    out.push_str("//!     --fixtures src/grobner/differential/fixtures.rs\n");
    out.push_str("//! ```\n");
    out.push_str("//!\n");
    out.push_str(&format!(
        "//! Singular build {}. Each case records the source basis, the quotient dimension, the\n",
        singular_version
    ));
    out.push_str("//! standard monomials, the normal form of every border monomial, and the lex\n");
    out.push_str("//! basis — so verifying one exercises the multiplication operators column by\n");
    out.push_str("//! column without Singular being installed.\n");
    out.push('\n');
    out.push_str("use super::fixture::DifferentialFixture;\n");
    out.push('\n');
    out.push_str(&format!(
        "/// {} ideals, with every answer Singular gave about them.\n",
        cases.len()
    ));
    out.push_str("pub(super) const FIXTURES: &[DifferentialFixture] = &[\n");
    for case in cases {
        out.push_str(&emit_fixture(case));
    }
    out.push_str("];\n");
    out
}

/// One case as a `DifferentialFixture` literal, indented for a table.
pub fn emit_fixture(case: &DifferentialCase) -> String {
    let mut out = String::new();
    out.push_str("    DifferentialFixture {\n");
    out.push_str(&format!("        name: {:?},\n", case.name));
    out.push_str(&format!(
        "        characteristic: {},\n",
        case.characteristic
    ));
    out.push_str(&format!(
        "        variables: &[{}],\n",
        quoted(&case.variables)
    ));
    out.push_str(&format!("        system: &[{}],\n", quoted(&case.system)));
    out.push_str(&format!(
        "        quotient_dimension: {},\n",
        match case.quotient_dimension {
            Some(dimension) => format!("Some({})", dimension),
            None => "None".to_string(),
        }
    ));
    out.push_str(&format!(
        "        grevlex_basis: &[{}],\n",
        quoted(&case.grevlex_basis)
    ));
    out.push_str(&format!(
        "        standard_monomials: &[{}],\n",
        quoted(&case.standard_monomials)
    ));
    out.push_str(&format!(
        "        border_normal_forms: &[{}],\n",
        case.border_normal_forms
            .iter()
            .map(|(monomial, normal_form)| format!("({:?}, {:?})", monomial, normal_form))
            .collect::<Vec<String>>()
            .join(", ")
    ));
    out.push_str(&format!(
        "        lex_basis: {},\n",
        match &case.lex_basis {
            Some(basis) => format!("Some(&[{}])", quoted(basis)),
            None => "None".to_string(),
        }
    ));
    out.push_str("    },\n");
    out
}

/// A failing case as a snippet to paste into the fixture table, under a comment saying what it is.
///
/// Carries the original seed and system even when the case has been minimized: a shrunk system is
/// no longer what the seed generates, and the seed is the only thing that reproduces the run that
/// found the failure.
pub fn emit_failure(case: &DifferentialCase, disagreement: &str, provenance: &str) -> String {
    let mut out = String::new();
    out.push_str("// A case Zeebra and Singular disagreed about. Paste into\n");
    out.push_str("// src/grobner/differential/fixtures.rs once the disagreement is understood —\n");
    out.push_str("// as a fixture it is a regression test, as a file here it is only a report.\n");
    out.push_str("//\n");
    out.push_str(&format!("// {}\n", disagreement));
    out.push_str("//\n");
    for line in provenance.lines() {
        out.push_str(&format!("// {}\n", line));
    }
    out.push_str(&emit_fixture(case));
    out
}

/// A comma-separated list of Rust string literals.
fn quoted(items: &[String]) -> String {
    items
        .iter()
        .map(|item| format!("{:?}", item))
        .collect::<Vec<String>>()
        .join(", ")
}

#[cfg(test)]
mod tests {
    use super::{emit_fixture_module, quoted, DifferentialFixture};
    use crate::grobner::differential::comparison::DifferentialCase;

    fn case() -> DifferentialCase {
        DifferentialCase {
            name: "seed-1-p13-n2".to_string(),
            characteristic: 13,
            variables: vec!["x1".to_string(), "x2".to_string()],
            system: vec!["x1^2-1".to_string(), "x2-x1".to_string()],
            quotient_dimension: Some(2),
            grevlex_basis: vec!["x2-x1".to_string(), "x1^2-1".to_string()],
            standard_monomials: vec!["x1".to_string(), "1".to_string()],
            border_normal_forms: vec![("x1^2".to_string(), "1".to_string())],
            lex_basis: Some(vec!["x2-x1".to_string(), "x1^2-1".to_string()]),
        }
    }

    /// A fixture round-trips to a case and back to the same values.
    #[test]
    fn test_a_fixture_converts_to_a_case() {
        let fixture = DifferentialFixture {
            name: "seed-1-p13-n2",
            characteristic: 13,
            variables: &["x1", "x2"],
            system: &["x1^2-1", "x2-x1"],
            quotient_dimension: Some(2),
            grevlex_basis: &["x2-x1", "x1^2-1"],
            standard_monomials: &["x1", "1"],
            border_normal_forms: &[("x1^2", "1")],
            lex_basis: Some(&["x2-x1", "x1^2-1"]),
        };
        assert_eq!(fixture.to_case(), case());
    }

    /// An emitted module names every field of every case.
    #[test]
    fn test_the_emitted_module_names_every_field() {
        let emitted = emit_fixture_module(&[case()], "44105");
        for field in [
            "name:",
            "characteristic:",
            "variables:",
            "system:",
            "quotient_dimension:",
            "grevlex_basis:",
            "standard_monomials:",
            "border_normal_forms:",
            "lex_basis:",
        ] {
            assert!(emitted.contains(field), "{} is missing", field);
        }
        assert!(emitted.contains("Do not edit by hand"));
        assert!(emitted.contains("Singular build 44105"));
    }

    /// A positive-dimensional case emits `None` for the dimension rather than a sentinel number.
    #[test]
    fn test_a_positive_dimensional_case_emits_none() {
        let mut positive = case();
        positive.quotient_dimension = None;
        positive.standard_monomials.clear();
        positive.border_normal_forms.clear();
        let emitted = emit_fixture_module(&[positive], "44105");
        assert!(emitted.contains("quotient_dimension: None"));
        assert!(emitted.contains("standard_monomials: &[]"));
    }

    /// Strings are emitted as Rust literals, escaped.
    #[test]
    fn test_strings_are_emitted_as_literals() {
        assert_eq!(
            quoted(&["x1^2".to_string(), "x2".to_string()]),
            "\"x1^2\", \"x2\""
        );
    }
}
