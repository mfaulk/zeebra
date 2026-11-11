use zeebra::{
    fields::Zp13,
    grobner::{
        f4,
        fglm::{
            fglm_to_lex_with_options, ConversionRoute, ConversionStrategy, FglmError, FglmOptions,
            WiedemannFallback,
        },
    },
    MonomialOrder, MultivariatePolynomial,
};

const SOURCE: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
type F = Zp13;

fn basis<const N: usize>(text: &[&str], names: [&str; N]) -> Vec<MultivariatePolynomial<N, F>> {
    let system: Vec<_> = text
        .iter()
        .map(|s| MultivariatePolynomial::parse(s, names).unwrap())
        .collect();
    f4(&system, SOURCE).unwrap()
}

fn options(strategy: ConversionStrategy) -> FglmOptions {
    FglmOptions {
        conversion_strategy: strategy,
        ..FglmOptions::recommended()
    }
}

// A successful scalar projection produces the same reduced lex basis as classical FGLM.
#[test]
fn certified_wiedemann_agrees_with_classical_conversion() {
    let source = basis(&["x - y^2", "y^7 - 1"], ["x", "y"]);
    let (fast, stats) =
        fglm_to_lex_with_options(&source, SOURCE, &options(ConversionStrategy::Wiedemann)).unwrap();
    let (classical, _) =
        fglm_to_lex_with_options(&source, SOURCE, &options(ConversionStrategy::Classical)).unwrap();
    assert_eq!(fast, classical);
    assert_eq!(stats.conversion_route, ConversionRoute::Wiedemann);
    assert!(stats.wiedemann_attempts > 0);
    assert_eq!(stats.memory.span_cells, 0);
    assert_eq!(stats.memory.accepted_vector_cells, 0);
    for relation in fast {
        assert!(relation.normal_form(&source, SOURCE).is_zero());
    }
}

// Nonradical shape-position ideals retain multiplicities rather than using squarefree recovery.
#[test]
fn nonradical_shape_relations_are_certified() {
    let source = basis(&["x - y", "y^3 - 3*y^2 + 3*y - 1"], ["x", "y"]);
    let (fast, stats) =
        fglm_to_lex_with_options(&source, SOURCE, &options(ConversionStrategy::Wiedemann)).unwrap();
    let (classical, _) =
        fglm_to_lex_with_options(&source, SOURCE, &options(ConversionStrategy::Classical)).unwrap();
    assert_eq!(fast, classical);
    assert_eq!(stats.conversion_route, ConversionRoute::Wiedemann);
}

// A nonseparating last variable falls back to the full classical lex basis and reports why.
#[test]
fn nonshape_ideals_fall_back_explicitly() {
    let source = basis(&["x^2", "y^2"], ["x", "y"]);
    let (fast, stats) =
        fglm_to_lex_with_options(&source, SOURCE, &options(ConversionStrategy::Wiedemann)).unwrap();
    let (classical, _) =
        fglm_to_lex_with_options(&source, SOURCE, &options(ConversionStrategy::Classical)).unwrap();
    assert_eq!(fast, classical);
    assert_eq!(stats.conversion_route, ConversionRoute::Classical);
    assert_eq!(
        stats.wiedemann_fallback,
        Some(WiedemannFallback::NonCyclicProjection)
    );
    assert_eq!(stats.wiedemann_attempts, 3);
}

// A sparse shape quotient converts inside a budget too small for the quadratic classical blocks.
#[test]
fn adaptive_conversion_avoids_the_quadratic_span_allocation() {
    let source = basis(&["t^128 - 1"], ["t"]);
    let options = FglmOptions {
        max_span_entries: 12_000,
        max_span_bytes: 192_000,
        ..options(ConversionStrategy::Adaptive)
    };
    let (fast, stats) = fglm_to_lex_with_options(&source, SOURCE, &options).unwrap();
    assert_eq!(fast, source);
    assert_eq!(stats.conversion_route, ConversionRoute::Wiedemann);
    assert!(stats.memory.krylov_workspace_cells <= options.max_span_entries);
    let classical = FglmOptions {
        conversion_strategy: ConversionStrategy::Classical,
        ..options
    };
    assert!(matches!(
        fglm_to_lex_with_options(&source, SOURCE, &classical),
        Err(FglmError::SpanStorageExceeded { .. })
    ));
}

// Tiny workspace budgets refuse both routes without bypassing the existing storage error.
#[test]
fn workspace_limits_are_enforced_before_the_fast_attempt() {
    let source = basis(&["t^128 - 1"], ["t"]);
    let opts = FglmOptions {
        max_span_entries: 1,
        ..options(ConversionStrategy::Wiedemann)
    };
    assert!(matches!(
        fglm_to_lex_with_options(&source, SOURCE, &opts),
        Err(FglmError::SpanStorageExceeded { .. })
    ));
    let opts = FglmOptions {
        max_span_bytes: 1,
        ..options(ConversionStrategy::Wiedemann)
    };
    assert!(matches!(
        fglm_to_lex_with_options(&source, SOURCE, &opts),
        Err(FglmError::SpanBytesExceeded { .. })
    ));
}

// The unit ideal and positive-dimensional inputs keep their existing result contracts.
#[test]
fn degenerate_ideals_preserve_the_existing_contract() {
    let unit = basis(&["x", "x - 1"], ["x"]);
    let (converted, stats) =
        fglm_to_lex_with_options(&unit, SOURCE, &options(ConversionStrategy::Wiedemann)).unwrap();
    assert_eq!(converted, unit);
    assert_eq!(stats.conversion_route, ConversionRoute::Classical);
    let infinite = basis(&["x*y"], ["x", "y"]);
    assert_eq!(
        fglm_to_lex_with_options(&infinite, SOURCE, &options(ConversionStrategy::Wiedemann)),
        Err(FglmError::PositiveDimensional)
    );
}

// Recommended options select the certified route automatically for a sparse large quotient.
#[test]
fn recommended_options_select_wiedemann_on_a_sparse_shape_quotient() {
    let source = basis(&["t^128 - 1"], ["t"]);
    let (converted, stats) =
        fglm_to_lex_with_options(&source, SOURCE, &FglmOptions::recommended()).unwrap();
    assert_eq!(converted, source);
    assert_eq!(stats.conversion_route, ConversionRoute::Wiedemann);
}
