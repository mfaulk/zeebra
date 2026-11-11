//! One generated system, through Zeebra and through the oracle, compared.
//!
//! The variable count is a const generic and the field is a type, so a harness that varies either
//! at runtime has to dispatch into a fixed set of monomorphizations. [`check_generated`] is that
//! dispatch, and it is the only place in this module that knows which `(N, F)` pairs exist:
//! everything above it works in strings and [`CaseField`]s, and everything below it is generic.
//!
//! The field arm is keyed on a [`CaseField`] and not on a characteristic, because a characteristic
//! does not determine a field: GF(2) and GF(2^8) share one, and two degree-8 moduli give two
//! fields of the same order in which the same byte has two different products. Each arm's type is
//! then checked against the spec by [`CaseField::matches`] inside the comparison, so a dispatch
//! table that paired a spec with the wrong type would fail rather than compare.

use crate::{
    fields::{Gf256, Gf256Mq, PrimeFieldElement64},
    grobner::{
        f4_with_options,
        fglm::{BorderIndex, FglmError, FglmOptions, QuotientBasis},
        F4Options,
    },
    KnownOrder, MultivariatePolynomial,
};

use super::{
    comparison::{verify_case_with, Agreement, DifferentialCase, Disagreement, SOURCE_ORDER},
    field::CaseField,
    generator::GeneratedSystem,
    singular::{Oracle, OracleError, OracleQuery},
    text::monomial_to_string,
};

/// Variable counts the harness can check, as const generics.
pub const SUPPORTED_VARIABLES: &[usize] = &[2, 3, 4, 5];

/// Fields the harness can check, as field types.
///
/// Two and three are here because they are where an implementation that assumed an odd
/// characteristic, or that `2` is invertible, goes wrong. The largest prime is the biggest
/// Singular's prime fields accept.
///
/// **Both degree-8 binary fields are here, and that is not redundancy.** GF(2^8) modulo the AES
/// polynomial is [`Gf256`], the field HFE is posed over; GF(2^8) modulo
/// `x^8+x^4+x^3+x^2+1` is [`Gf256Mq`], the field the **Fukuoka MQ
/// Challenge** is posed over. They have the same characteristic and the same order and are not the
/// same field, so a harness that supported one would silently decline the other's systems.
pub const SUPPORTED_FIELDS: &[CaseField] = &[
    CaseField::prime(2),
    CaseField::prime(3),
    CaseField::prime(7),
    CaseField::prime(13),
    CaseField::prime(65537),
    CaseField::prime(2147483647),
    CaseField::binary(GF256_MODULUS),
    CaseField::binary(GF256MQ_MODULUS),
];

/// `x^8 + x^4 + x^3 + x + 1`, which is [`Gf256`]'s modulus.
///
/// Named rather than inlined so that the dispatch arm and the supported-field list cannot name
/// two different degree-8 polynomials — which would be a field mismatch the dispatch could not
/// see, since both are GF(2^8).
pub const GF256_MODULUS: u64 = 0x11B;

/// `x^8 + x^4 + x^3 + x^2 + 1`, which is [`Gf256Mq`]'s modulus.
///
/// **The Fukuoka MQ Challenge's**, and a different field from [`GF256_MODULUS`] rather than a
/// different spelling of it: `0x57 * 0x83` is `0xc1` modulo `0x11B` and `0x52` modulo `0x11D`
/// (`docs/research/boolean-solving.md` §4). Named for the same reason its neighbour is — two
/// degree-8 polynomials are indistinguishable by characteristic and order, so a dispatch that
/// inlined them could not see a mismatch between the arm and the supported-field list.
pub const GF256MQ_MODULUS: u64 = 0x11D;

/// What checking one system found.
#[derive(Clone, Debug)]
pub enum SystemOutcome {
    /// Zeebra and the oracle agreed on everything that was compared.
    Agreed {
        /// The oracle's answers, ready to be committed as a fixture.
        case: DifferentialCase,
        /// What the agreement covered.
        agreement: Agreement,
    },

    /// They disagreed. The case is kept so the failure can be saved and reproduced.
    Disagreed {
        /// The oracle's answers, including the one that disagreed.
        case: DifferentialCase,
        /// Which check, and both answers.
        disagreement: Disagreement,
    },

    /// The oracle did not answer. **Not agreement**, and counted separately.
    OracleFailed {
        /// Why.
        error: OracleError,
    },

    /// Zeebra could not get far enough to be compared — a parse failure, or an F4 limit.
    ///
    /// Distinguished from a disagreement because nothing was compared, and from an oracle failure
    /// because the fault is on this side.
    ZeebraFailed {
        /// What stopped it.
        detail: String,
    },

    /// The combination of variable count and characteristic is not one the harness instantiates.
    Unsupported {
        /// Why this system was not checked.
        detail: String,
    },
}

impl SystemOutcome {
    /// Whether this outcome is agreement. Everything else, including an oracle failure, is not.
    pub fn agreed(&self) -> bool {
        matches!(self, Self::Agreed { .. })
    }

    /// A one-line summary for a progress line.
    pub fn summary(&self) -> String {
        match self {
            Self::Agreed { agreement, .. } => match agreement.quotient_dimension {
                None => "agreed: positive-dimensional, rejected by both".to_string(),
                Some(0) => "agreed: unit ideal".to_string(),
                Some(d) => format!(
                    "agreed: D = {}, {} border monomials, {} columns",
                    d, agreement.border_monomials, agreement.operator_columns
                ),
            },
            Self::Disagreed { disagreement, .. } => format!("DISAGREED {}", disagreement),
            Self::OracleFailed { error } => format!("oracle failed: {}", error),
            Self::ZeebraFailed { detail } => format!("Zeebra failed: {}", detail),
            Self::Unsupported { detail } => format!("skipped: {}", detail),
        }
    }
}

/// Check one system at a known variable count and field.
///
/// `verify_case_with` recomputes the source basis and the standard monomials rather than being
/// handed the ones found here. That is deliberate duplication: it keeps the comparison runnable
/// against a committed fixture with no oracle present, so CI exercises the same comparison code
/// this does. The systems are small enough that computing a basis twice costs nothing worth saving.
/// It is recomputed under `f4`, so the duplication does not quietly change the configuration.
pub fn check_system<const N: usize, F: KnownOrder>(
    system: &GeneratedSystem,
    oracle: &mut impl Oracle,
    options: &FglmOptions,
    f4: &F4Options,
) -> SystemOutcome {
    let names = system.variable_names();
    let array = match <[&str; N]>::try_from(names.as_slice()) {
        Ok(array) => array,
        Err(_) => {
            return SystemOutcome::Unsupported {
                detail: format!("{} variables checked as {}", names.len(), N),
            }
        }
    };

    let rendered = system.render();
    let mut polynomials: Vec<MultivariatePolynomial<N, F>> = Vec::with_capacity(rendered.len());
    for text in &rendered {
        match MultivariatePolynomial::parse(text, array) {
            Ok(polynomial) => polynomials.push(polynomial),
            Err(e) => {
                return SystemOutcome::ZeebraFailed {
                    detail: format!("cannot parse {:?}: {}", text, e),
                }
            }
        }
    }

    let source = match f4_with_options(&polynomials, SOURCE_ORDER, f4) {
        Ok((basis, _)) => basis,
        Err(e) => {
            return SystemOutcome::ZeebraFailed {
                detail: format!("F4 could not finish under grevlex: {}", e),
            }
        }
    };

    // The border is a property of Zeebra's standard monomials, so the oracle has to be told which
    // monomials to reduce. A wrong basis here gives a wrong question — which is why the bases
    // themselves are compared, rather than this being the only check.
    let border: Vec<String> =
        match QuotientBasis::new(&source, SOURCE_ORDER, options.max_quotient_dimension) {
            Ok(quotient) => BorderIndex::new(&quotient)
                .monomials()
                .iter()
                .map(|monomial| monomial_to_string(monomial, &names))
                .collect(),
            Err(FglmError::PositiveDimensional) => Vec::new(),
            Err(e) => {
                return SystemOutcome::ZeebraFailed {
                    detail: format!("cannot enumerate the standard monomials: {}", e),
                }
            }
        };

    let query = OracleQuery {
        name: system.name(),
        field: system.field,
        variables: &names,
        system: &rendered,
        border_monomials: &border,
    };

    let case = match oracle.interrogate(&query) {
        Ok(case) => case,
        Err(error) => return SystemOutcome::OracleFailed { error },
    };

    // `verify_case_with` and not `verify_case`: the comparison has to recompute the source basis
    // under the *same* `f4` this function used, or the sweep would check a default-configuration
    // basis against the oracle and report agreement about a configuration it never ran.
    match verify_case_with::<N, F>(&case, options, f4) {
        Ok(agreement) => SystemOutcome::Agreed { case, agreement },
        Err(disagreement) => SystemOutcome::Disagreed { case, disagreement },
    }
}

/// Dispatch on the field for a fixed variable count.
macro_rules! by_field {
    ($n:literal, $body:ident, $system:expr, $oracle:expr, $options:expr, $f4:expr) => {
        match $system.field {
            CaseField::Prime { characteristic: 2 } => {
                $body::<$n, PrimeFieldElement64<2>>($system, $oracle, $options, $f4)
            }
            CaseField::Prime { characteristic: 3 } => {
                $body::<$n, PrimeFieldElement64<3>>($system, $oracle, $options, $f4)
            }
            CaseField::Prime { characteristic: 7 } => {
                $body::<$n, PrimeFieldElement64<7>>($system, $oracle, $options, $f4)
            }
            CaseField::Prime { characteristic: 13 } => {
                $body::<$n, PrimeFieldElement64<13>>($system, $oracle, $options, $f4)
            }
            CaseField::Prime {
                characteristic: 65537,
            } => $body::<$n, PrimeFieldElement64<65537>>($system, $oracle, $options, $f4),
            CaseField::Prime {
                characteristic: 2147483647,
            } => $body::<$n, PrimeFieldElement64<2147483647>>($system, $oracle, $options, $f4),
            CaseField::Binary {
                modulus: GF256_MODULUS,
            } => $body::<$n, Gf256>($system, $oracle, $options, $f4),
            CaseField::Binary {
                modulus: GF256MQ_MODULUS,
            } => $body::<$n, Gf256Mq>($system, $oracle, $options, $f4),
            other => SystemOutcome::Unsupported {
                detail: format!("GF({}) is not one of {:?}", other, SUPPORTED_FIELDS),
            },
        }
    };
}

/// Check a generated system, dispatching on its variable count and field.
///
/// An unsupported combination is [`SystemOutcome::Unsupported`] and never silence: a sweep that
/// asked for six variables should see that it got none, not that everything agreed.
pub fn check_generated(
    system: &GeneratedSystem,
    oracle: &mut impl Oracle,
    options: &FglmOptions,
    f4: &F4Options,
) -> SystemOutcome {
    match system.variables.len() {
        2 => by_field!(2, check_system, system, oracle, options, f4),
        3 => by_field!(3, check_system, system, oracle, options, f4),
        4 => by_field!(4, check_system, system, oracle, options, f4),
        5 => by_field!(5, check_system, system, oracle, options, f4),
        other => SystemOutcome::Unsupported {
            detail: format!(
                "{} variables is not one of {:?}",
                other, SUPPORTED_VARIABLES
            ),
        },
    }
}

/// Dispatch on the field for a fixed variable count, for a recorded case.
macro_rules! verify_by_field {
    ($n:literal, $case:expr, $options:expr, $f4:expr) => {
        match $case.field {
            CaseField::Prime { characteristic: 2 } => {
                verify_case_with::<$n, PrimeFieldElement64<2>>($case, $options, $f4)
            }
            CaseField::Prime { characteristic: 3 } => {
                verify_case_with::<$n, PrimeFieldElement64<3>>($case, $options, $f4)
            }
            CaseField::Prime { characteristic: 7 } => {
                verify_case_with::<$n, PrimeFieldElement64<7>>($case, $options, $f4)
            }
            CaseField::Prime { characteristic: 13 } => {
                verify_case_with::<$n, PrimeFieldElement64<13>>($case, $options, $f4)
            }
            CaseField::Prime {
                characteristic: 65537,
            } => verify_case_with::<$n, PrimeFieldElement64<65537>>($case, $options, $f4),
            CaseField::Prime {
                characteristic: 2147483647,
            } => verify_case_with::<$n, PrimeFieldElement64<2147483647>>($case, $options, $f4),
            CaseField::Binary {
                modulus: GF256_MODULUS,
            } => verify_case_with::<$n, Gf256>($case, $options, $f4),
            CaseField::Binary {
                modulus: GF256MQ_MODULUS,
            } => verify_case_with::<$n, Gf256Mq>($case, $options, $f4),
            other => Err(Disagreement {
                check: super::comparison::Check::Field,
                detail: format!("GF({}) is not one of {:?}", other, SUPPORTED_FIELDS),
            }),
        }
    };
}

/// Verify a recorded case, dispatching on its variable count and field.
///
/// The no-oracle path: a committed fixture already holds the oracle's answers, so this is the whole
/// comparison with no subprocess involved. It is what CI runs.
pub fn verify_recorded(
    case: &DifferentialCase,
    options: &FglmOptions,
) -> Result<Agreement, Disagreement> {
    verify_recorded_with(case, options, &F4Options::default())
}

/// Verify a recorded case under a chosen F4 configuration.
///
/// The configured counterpart of [`verify_recorded`]: the source basis, and so every check built
/// on it, comes from `f4`. A fixture is a recorded oracle answer and does not depend on how Zeebra
/// reaches its own, which is what makes this a usable offline check of a strategy.
pub fn verify_recorded_with(
    case: &DifferentialCase,
    options: &FglmOptions,
    f4: &F4Options,
) -> Result<Agreement, Disagreement> {
    match case.variables.len() {
        2 => verify_by_field!(2, case, options, f4),
        3 => verify_by_field!(3, case, options, f4),
        4 => verify_by_field!(4, case, options, f4),
        5 => verify_by_field!(5, case, options, f4),
        other => Err(Disagreement {
            check: super::comparison::Check::Field,
            detail: format!(
                "{} variables is not one of {:?}",
                other, SUPPORTED_VARIABLES
            ),
        }),
    }
}
