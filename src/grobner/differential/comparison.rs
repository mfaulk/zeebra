//! What an oracle said about an ideal, and whether Zeebra agrees with it.
//!
//! One comparison implementation, used two ways. The live harness fills a [`DifferentialCase`]
//! from Singular and checks it; an ordinary test fills the same structure from a committed fixture
//! and checks that. So CI runs exactly the comparison the development machine runs, against
//! recorded answers instead of a subprocess, and the two cannot drift.
//!
//! The checks go from the source basis outwards to the lex basis, and the first failure stops.
//! That order matters: a wrong quotient dimension explains every later disagreement, so reporting
//! it alone is more useful than reporting all of them.
//!
//! **Operator columns are checked individually**, against the oracle's normal form for the
//! monomial each column stands for, rather than inferred from the final lex basis agreeing. A
//! column has a precise mathematical answer and is the natural unit for an external comparison.

use std::collections::{HashMap, HashSet};

use crate::{
    grobner::{
        f4_with_options,
        fglm::{
            fglm_to_lex_with_options, BorderIndex, FglmError, FglmOptions, QuotientAlgebra,
            QuotientBasis,
        },
        F4Options,
    },
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

use super::text::{monomial_to_string, polynomial_to_string};

/// The order the source basis is computed under, on both sides.
pub const SOURCE_ORDER: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// The order the conversion targets, on both sides.
pub const TARGET_ORDER: MonomialOrder = MonomialOrder::Lexicographic;

/// Which comparison failed.
///
/// Ordered as the checks run, so a `Check` also says how far the comparison got.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Check {
    /// The case's own text could not be parsed. A defect in the harness or the fixture, not a
    /// finding about Zeebra — but reported rather than swallowed.
    Parse,

    /// The case was stated over a different field than the one it is being checked in.
    Field,

    /// The oracle read a different system than it was sent.
    ///
    /// A finding about the *interface*, not about either implementation's mathematics, and the
    /// first thing checked because nothing after it means anything if it fails. It is not
    /// hypothetical: Singular sums bare integer literals in 32-bit arithmetic before coercing them
    /// into the ring, so at `p = 2^31 - 1` a polynomial with two constant terms reads back as a
    /// different polynomial. The generator now emits canonical polynomials, and this verifies that
    /// rather than trusting it.
    OracleInput,

    /// Zeebra's grevlex Gröbner basis against the oracle's.
    SourceBasis,

    /// `dim R/I` against the oracle's `vdim`, including which of the two called it infinite.
    QuotientDimension,

    /// The standard monomials against the oracle's `kbase`.
    StandardMonomials,

    /// The oracle was asked about a different set of border monomials than Zeebra has.
    BorderCoverage,

    /// A border monomial's normal form against the oracle's `reduce`.
    BorderNormalForm,

    /// A multiplication-operator column against the oracle's normal form for its monomial.
    OperatorColumn,

    /// The lex basis against the oracle's.
    LexBasis,
}

impl Check {
    /// A short name for reports and file names.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Parse => "parse",
            Self::Field => "field",
            Self::OracleInput => "oracle-input",
            Self::SourceBasis => "source-basis",
            Self::QuotientDimension => "quotient-dimension",
            Self::StandardMonomials => "standard-monomials",
            Self::BorderCoverage => "border-coverage",
            Self::BorderNormalForm => "border-normal-form",
            Self::OperatorColumn => "operator-column",
            Self::LexBasis => "lex-basis",
        }
    }
}

/// A check that failed, and enough detail to reproduce it by hand.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Disagreement {
    /// Which check.
    pub check: Check,

    /// What Zeebra produced and what the oracle produced, in that order, as text.
    pub detail: String,
}

impl std::fmt::Display for Disagreement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.check.name(), self.detail)
    }
}

/// What a passing comparison covered, so that "agreed" can be distinguished from "checked little".
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Agreement {
    /// Elements in the agreed grevlex basis.
    pub source_basis_elements: usize,

    /// `dim R/I`, or `None` if both sides called the ideal positive-dimensional.
    pub quotient_dimension: Option<usize>,

    /// Border monomials whose normal forms were compared.
    pub border_monomials: usize,

    /// Operator columns compared, which is `N * D`.
    pub operator_columns: usize,

    /// Elements in the agreed lex basis, or `None` if there was no conversion to compare.
    pub lex_basis_elements: Option<usize>,
}

/// Everything an oracle said about one ideal.
///
/// The text is the interface. Every polynomial is a string in the same syntax Zeebra's parser and
/// Singular both accept, so a case can be read, pasted into either system, and committed as a
/// fixture without a conversion step in between.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DifferentialCase {
    /// A stable identifier, used in reports and fixture file names.
    pub name: String,

    /// The field's characteristic. Checked against the field the case is verified in.
    pub characteristic: u64,

    /// Variable names, in the order both sides declare them. Length is the variable count.
    pub variables: Vec<String>,

    /// The generators of the ideal.
    pub system: Vec<String>,

    /// The generators as the oracle echoed them back, if it was asked.
    ///
    /// `None` for a recorded fixture, which inherits the check from the sweep that produced it;
    /// always `Some` from a live oracle. Compared against [`Self::system`] as *polynomials* rather
    /// than as text, since an oracle is entitled to print the same polynomial differently.
    pub oracle_system: Option<Vec<String>>,

    /// `dim R/I` per the oracle, or `None` if the oracle called the ideal positive-dimensional.
    ///
    /// `Some(0)` is the unit ideal, which is a distinct and interesting case: the quotient is the
    /// zero space and the lex basis is `{1}`.
    pub quotient_dimension: Option<usize>,

    /// The oracle's reduced Gröbner basis under [`SOURCE_ORDER`].
    pub grevlex_basis: Vec<String>,

    /// The oracle's standard monomials. Empty when the quotient is the zero space, and when the
    /// ideal is positive-dimensional and the oracle was not asked.
    pub standard_monomials: Vec<String>,

    /// `(border monomial, its normal form)` per distinct border monomial.
    pub border_normal_forms: Vec<(String, String)>,

    /// The oracle's reduced Gröbner basis under [`TARGET_ORDER`], or `None` if it was not asked —
    /// which is the positive-dimensional case, where there is no conversion to compare.
    pub lex_basis: Option<Vec<String>>,
}

/// Zeebra's answers, checked against the case's.
///
/// `options` is what the quotient algebra and the conversion are built with, so a caller can point
/// the whole comparison at a strategy under development. The resource limits in it are the
/// caller's business; the comparison reports a limit that fires as a disagreement on the check it
/// fired in, since the oracle produced an answer and Zeebra did not.
///
/// # Errors
/// The first [`Check`] that disagreed, with the two answers in the detail. Includes
/// [`Check::Parse`] and [`Check::Field`], which are defects in the case rather than findings about
/// Zeebra, so that neither is mistaken for agreement.
pub fn verify_case<const N: usize, F: FiniteField>(
    case: &DifferentialCase,
    options: &FglmOptions,
) -> Result<Agreement, Disagreement> {
    let fail = |check: Check, detail: String| Disagreement { check, detail };

    if u128::from(case.characteristic) != F::characteristic() {
        return Err(fail(
            Check::Field,
            format!(
                "the case is over GF({}) and is being checked over GF({})",
                case.characteristic,
                F::characteristic()
            ),
        ));
    }
    if case.variables.len() != N {
        return Err(fail(
            Check::Field,
            format!(
                "the case has {} variables and is being checked with {}",
                case.variables.len(),
                N
            ),
        ));
    }

    let names: Vec<&str> = case.variables.iter().map(String::as_str).collect();
    let array = <[&str; N]>::try_from(names.as_slice()).expect("checked just above");
    let parse = |source: &str| -> Result<MultivariatePolynomial<N, F>, Disagreement> {
        MultivariatePolynomial::parse(source, array)
            .map_err(|e| fail(Check::Parse, format!("cannot parse {:?}: {}", source, e)))
    };

    let system: Vec<MultivariatePolynomial<N, F>> = case
        .system
        .iter()
        .map(|s| parse(s))
        .collect::<Result<_, _>>()?;

    let mut agreement = Agreement::default();

    // ---- what the oracle read ---------------------------------------------------------------
    //
    // First, because nothing after it means anything if the two sides are not discussing the same
    // ideal.
    //
    // Compared as *polynomials*, canonically rendered and sorted, and with zero generators dropped
    // from both sides. Three conventions an oracle is entitled to and none of which changes the
    // ideal: printing `x1-887778612` for what was sent as `1259705035+x1`, listing the generators
    // in its own order, and dropping a zero generator — `<0, f>` is `<f>`, and Singular's `size`
    // does not count one.

    if let Some(echoed) = &case.oracle_system {
        let canonical = |sources: &[String]| -> Result<Vec<String>, Disagreement> {
            let mut rendered: Vec<String> = Vec::new();
            for source in sources {
                let polynomial = parse(source)?;
                if polynomial.is_zero() {
                    continue;
                }
                rendered.push(polynomial_to_string(&polynomial, &names, SOURCE_ORDER));
            }
            rendered.sort();
            Ok(rendered)
        };

        let sent = canonical(&case.system)?;
        let read = canonical(echoed)?;
        if sent != read {
            return Err(fail(
                Check::OracleInput,
                format!(
                    "sent [{}] and the oracle read [{}]",
                    sent.join(", "),
                    read.join(", ")
                ),
            ));
        }
    }

    // ---- the source basis -------------------------------------------------------------------

    let f4_options = F4Options::default();
    let zeebra_source = match f4_with_options(&system, SOURCE_ORDER, &f4_options) {
        Ok((basis, _)) => basis,
        Err(e) => {
            return Err(fail(
                Check::SourceBasis,
                format!("Zeebra's F4 could not finish under grevlex: {}", e),
            ))
        }
    };
    let oracle_source: Vec<MultivariatePolynomial<N, F>> = case
        .grevlex_basis
        .iter()
        .map(|s| parse(s))
        .collect::<Result<_, _>>()?;

    compare_bases(
        &zeebra_source,
        &oracle_source,
        SOURCE_ORDER,
        &names,
        Check::SourceBasis,
    )?;
    agreement.source_basis_elements = zeebra_source.len();

    // ---- the quotient dimension -------------------------------------------------------------

    let quotient = QuotientBasis::new(&zeebra_source, SOURCE_ORDER, options.max_quotient_dimension);
    let quotient = match (quotient, case.quotient_dimension) {
        (Ok(quotient), Some(dimension)) if quotient.dimension() == dimension => quotient,
        (Ok(quotient), Some(dimension)) => {
            return Err(fail(
                Check::QuotientDimension,
                format!(
                    "Zeebra says dim R/I = {} and the oracle says {}",
                    quotient.dimension(),
                    dimension
                ),
            ))
        }
        (Ok(quotient), None) => {
            return Err(fail(
                Check::QuotientDimension,
                format!(
                    "Zeebra says dim R/I = {} and the oracle says the ideal is \
                     positive-dimensional",
                    quotient.dimension()
                ),
            ))
        }
        (Err(FglmError::PositiveDimensional), None) => {
            // Both sides call the quotient infinite, and there is nothing further to compare:
            // no standard monomials, no operators, no conversion. The agreement is in the
            // rejection, which is itself worth checking — see §11 of the milestone document.
            agreement.quotient_dimension = None;
            return Ok(agreement);
        }
        (Err(FglmError::PositiveDimensional), Some(dimension)) => {
            return Err(fail(
                Check::QuotientDimension,
                format!(
                    "Zeebra says the ideal is positive-dimensional and the oracle says \
                     dim R/I = {}",
                    dimension
                ),
            ))
        }
        (Err(e), _) => {
            return Err(fail(
                Check::QuotientDimension,
                format!("Zeebra could not enumerate the standard monomials: {}", e),
            ))
        }
    };
    agreement.quotient_dimension = Some(quotient.dimension());

    // ---- the standard monomials --------------------------------------------------------------

    let oracle_standard: Vec<Monomial<N>> = case
        .standard_monomials
        .iter()
        .map(|s| single_monomial(&parse(s)?, s))
        .collect::<Result<_, _>>()?;

    let zeebra_set: HashSet<Monomial<N>> = quotient.monomials().iter().copied().collect();
    let oracle_set: HashSet<Monomial<N>> = oracle_standard.iter().copied().collect();
    if zeebra_set != oracle_set {
        return Err(fail(
            Check::StandardMonomials,
            format!(
                "Zeebra's standard monomials are {} and the oracle's are {}",
                render_monomials(quotient.monomials(), &names),
                render_monomials(&oracle_standard, &names),
            ),
        ));
    }

    // ---- the border ---------------------------------------------------------------------------

    let zeebra_border = BorderIndex::new(&quotient).monomials().to_vec();
    let oracle_border: HashMap<Monomial<N>, MultivariatePolynomial<N, F>> = case
        .border_normal_forms
        .iter()
        .map(|(monomial, normal_form)| {
            Ok((
                single_monomial(&parse(monomial)?, monomial)?,
                parse(normal_form)?,
            ))
        })
        .collect::<Result<_, Disagreement>>()?;

    // A fixture that omits a border monomial would otherwise pass by not being asked about it.
    let zeebra_border_set: HashSet<Monomial<N>> = zeebra_border.iter().copied().collect();
    let oracle_border_set: HashSet<Monomial<N>> = oracle_border.keys().copied().collect();
    if zeebra_border_set != oracle_border_set {
        let missing: Vec<Monomial<N>> = zeebra_border
            .iter()
            .filter(|m| !oracle_border_set.contains(m))
            .copied()
            .collect();
        let extra: Vec<Monomial<N>> = oracle_border_set
            .difference(&zeebra_border_set)
            .copied()
            .collect();
        return Err(fail(
            Check::BorderCoverage,
            format!(
                "the oracle was not asked about {} and was asked about {}, which is not on \
                 Zeebra's border",
                render_monomials(&missing, &names),
                render_monomials(&extra, &names),
            ),
        ));
    }

    for monomial in &zeebra_border {
        let term = MultivariatePolynomial::new(&[(*monomial, F::one())]);
        let zeebra_normal_form = term.normal_form(&zeebra_source, SOURCE_ORDER);
        let oracle_normal_form = &oracle_border[monomial];
        if zeebra_normal_form != *oracle_normal_form {
            return Err(fail(
                Check::BorderNormalForm,
                format!(
                    "NF({}): Zeebra says {} and the oracle says {}",
                    monomial_to_string(monomial, &names),
                    polynomial_to_string(&zeebra_normal_form, &names, SOURCE_ORDER),
                    polynomial_to_string(oracle_normal_form, &names, SOURCE_ORDER),
                ),
            ));
        }
    }
    agreement.border_monomials = zeebra_border.len();

    // ---- the multiplication operators --------------------------------------------------------

    let algebra = match QuotientAlgebra::new(&zeebra_source, SOURCE_ORDER, options) {
        Ok(algebra) => algebra,
        Err(e) => {
            return Err(fail(
                Check::OperatorColumn,
                format!("Zeebra could not build the quotient algebra: {}", e),
            ))
        }
    };

    for i in 0..N {
        for (j, monomial) in quotient.monomials().iter().enumerate() {
            let product = *monomial * Monomial::univariate(i, 1);
            // The column's answer per the oracle: a unit vector where the product stayed standard,
            // and the oracle's own normal form where it did not. Reconstructed rather than asked
            // for, because the two sources of truth are exactly the ones checked above.
            let expected = match quotient.index_of(&product) {
                Some(index) => {
                    MultivariatePolynomial::new(&[(quotient.monomials()[index], F::one())])
                }
                None => oracle_border[&product].clone(),
            };
            let from_column = algebra.polynomial(&algebra.operator(i).column(j));
            if from_column != expected {
                return Err(fail(
                    Check::OperatorColumn,
                    format!(
                        "column {} of T_{} stands for {}: Zeebra says {} and the oracle says {}",
                        j,
                        i,
                        monomial_to_string(&product, &names),
                        polynomial_to_string(&from_column, &names, SOURCE_ORDER),
                        polynomial_to_string(&expected, &names, SOURCE_ORDER),
                    ),
                ));
            }
        }
    }
    agreement.operator_columns = N * quotient.dimension();

    // ---- the lex basis ------------------------------------------------------------------------

    let oracle_lex = match &case.lex_basis {
        Some(basis) => basis,
        // Zero-dimensional and yet no lex basis recorded: the case is incomplete, and saying so is
        // better than reporting agreement on a check that did not run.
        None => {
            return Err(fail(
                Check::LexBasis,
                "the oracle recorded no lex basis for a zero-dimensional ideal".to_string(),
            ))
        }
    };
    let oracle_lex: Vec<MultivariatePolynomial<N, F>> = oracle_lex
        .iter()
        .map(|s| parse(s))
        .collect::<Result<_, _>>()?;

    let zeebra_lex = match fglm_to_lex_with_options(&zeebra_source, SOURCE_ORDER, options) {
        Ok((basis, _)) => basis,
        Err(e) => {
            return Err(fail(
                Check::LexBasis,
                format!("Zeebra's conversion failed: {}", e),
            ))
        }
    };

    compare_bases(
        &zeebra_lex,
        &oracle_lex,
        TARGET_ORDER,
        &names,
        Check::LexBasis,
    )?;
    agreement.lex_basis_elements = Some(zeebra_lex.len());

    Ok(agreement)
}

/// Two reduced Gröbner bases of the same ideal and order, compared as values.
///
/// A reduced Gröbner basis is unique, so this is an equality once both sides are sorted the same
/// way — not a containment test. Sorting is by leading monomial descending, which is what Zeebra's
/// engines return and what Singular's output is normalized to here.
fn compare_bases<const N: usize, F: FiniteField>(
    zeebra: &[MultivariatePolynomial<N, F>],
    oracle: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    names: &[&str],
    check: Check,
) -> Result<(), Disagreement> {
    let sorted = |basis: &[MultivariatePolynomial<N, F>]| -> Vec<MultivariatePolynomial<N, F>> {
        let mut basis: Vec<MultivariatePolynomial<N, F>> =
            basis.iter().filter(|p| !p.is_zero()).cloned().collect();
        basis.sort_by(|a, b| order.cmp(&b.leading_monomial(order), &a.leading_monomial(order)));
        basis
    };

    let zeebra = sorted(zeebra);
    let oracle = sorted(oracle);
    if zeebra == oracle {
        return Ok(());
    }

    let render = |basis: &[MultivariatePolynomial<N, F>]| -> String {
        format!(
            "[{}]",
            basis
                .iter()
                .map(|p| polynomial_to_string(p, names, order))
                .collect::<Vec<String>>()
                .join(", ")
        )
    };
    Err(Disagreement {
        check,
        detail: format!(
            "Zeebra says {} and the oracle says {}",
            render(&zeebra),
            render(&oracle)
        ),
    })
}

/// The single monomial of a polynomial that should have exactly one term with coefficient one.
fn single_monomial<const N: usize, F: FiniteField>(
    polynomial: &MultivariatePolynomial<N, F>,
    source: &str,
) -> Result<Monomial<N>, Disagreement> {
    let terms: Vec<(&Monomial<N>, &F)> = polynomial.terms().iter().collect();
    match terms.as_slice() {
        [(monomial, coefficient)] if coefficient.is_one() => Ok(**monomial),
        _ => Err(Disagreement {
            check: Check::Parse,
            detail: format!("{:?} is not a monic monomial", source),
        }),
    }
}

/// A list of monomials as text, for a disagreement's detail. Deterministically ordered.
fn render_monomials<const N: usize>(monomials: &[Monomial<N>], names: &[&str]) -> String {
    let mut rendered: Vec<String> = monomials
        .iter()
        .map(|m| monomial_to_string(m, names))
        .collect();
    rendered.sort();
    format!("[{}]", rendered.join(", "))
}
