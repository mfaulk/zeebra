use zeebra::{
    fields::Zp32003,
    grobner::{
        certify_submitted_basis_with_witnesses, verify_ideal_membership, MembershipLimits,
        MembershipStatus, WitnessError,
    },
    MonomialOrder, MultivariatePolynomial,
};

type P = MultivariatePolynomial<2, Zp32003>;
fn p(text: &str) -> P {
    P::parse(text, ["x", "y"]).unwrap()
}

// Exact cofactor identities bind the original generator positions and coefficients.
#[test]
fn membership_checks_the_exact_ordered_identity() {
    let generators = [p("x"), p("y")];
    let cofactors = [p("y"), p("2")];
    let limits = MembershipLimits::default();
    assert_eq!(
        verify_ideal_membership(&generators, &p("x*y+2*y"), &cofactors, &limits),
        Ok(MembershipStatus::Verified)
    );
    assert_eq!(
        verify_ideal_membership(&generators, &p("x*y+y"), &cofactors, &limits),
        Ok(MembershipStatus::Invalid)
    );
    assert_eq!(
        verify_ideal_membership(&generators, &p("x*y+2*y"), &[p("2"), p("y")], &limits),
        Ok(MembershipStatus::Invalid)
    );
    assert_eq!(
        verify_ideal_membership(&[p("y"), p("x")], &p("x*y+2*y"), &cofactors, &limits),
        Ok(MembershipStatus::Invalid)
    );
    assert!(matches!(
        verify_ideal_membership(&generators, &p("x"), &[p("1"), p("0"), p("0")], &limits),
        Err(WitnessError::CofactorCount { .. })
    ));
    assert!(matches!(
        verify_ideal_membership(&generators, &p("x"), &[], &limits),
        Err(WitnessError::CofactorCount { .. })
    ));
}

// A proper ideal cannot be certified with the forged submitted basis [1].
#[test]
fn submitted_unit_basis_needs_reverse_inclusion() {
    let report = certify_submitted_basis_with_witnesses(
        &[p("x")],
        &[p("1")],
        Some(&[vec![p("1")]]),
        MonomialOrder::Lexicographic,
        &MembershipLimits::default(),
    )
    .unwrap();
    assert_eq!(report.membership, MembershipStatus::Invalid);
    assert!(!report.is_complete());
}

// Both inclusions and reduced Gröbner checks are needed even when all witnesses hold.
#[test]
fn combined_certification_requires_every_obligation() {
    let limits = MembershipLimits::default();
    let generators = [p("x"), p("y")];
    let valid = certify_submitted_basis_with_witnesses(
        &generators,
        &generators,
        Some(&[vec![p("1"), p("0")], vec![p("0"), p("1")]]),
        MonomialOrder::Lexicographic,
        &limits,
    )
    .unwrap();
    assert!(valid.is_complete());
    let truncated = certify_submitted_basis_with_witnesses(
        &generators,
        &[p("x")],
        Some(&[vec![p("1"), p("0")]]),
        MonomialOrder::Lexicographic,
        &limits,
    )
    .unwrap();
    assert!(!truncated.is_complete());
    let missing = certify_submitted_basis_with_witnesses(
        &generators,
        &generators,
        None,
        MonomialOrder::Lexicographic,
        &limits,
    )
    .unwrap();
    assert_eq!(missing.membership, MembershipStatus::Missing);
    assert!(!missing.is_complete());
}

// Empty, zero, duplicate and unit generators retain their positional meaning.
#[test]
fn degenerate_ideals_and_duplicate_generators() {
    let limits = MembershipLimits::default();
    assert_eq!(
        verify_ideal_membership(&[], &p("0"), &[], &limits),
        Ok(MembershipStatus::Verified)
    );
    assert_eq!(
        verify_ideal_membership(&[], &p("1"), &[], &limits),
        Ok(MembershipStatus::Invalid)
    );
    let zero = certify_submitted_basis_with_witnesses(
        &[p("0")],
        &[],
        Some(&[]),
        MonomialOrder::Lexicographic,
        &limits,
    )
    .unwrap();
    assert!(zero.is_complete());
    let unit = certify_submitted_basis_with_witnesses(
        &[p("1"), p("0")],
        &[p("1")],
        Some(&[vec![p("1"), p("123")]]),
        MonomialOrder::Lexicographic,
        &limits,
    )
    .unwrap();
    assert!(unit.is_complete());
    assert_eq!(
        verify_ideal_membership(&[p("x"), p("x")], &p("3*x"), &[p("1"), p("2")], &limits),
        Ok(MembershipStatus::Verified)
    );
    assert!(matches!(
        certify_submitted_basis_with_witnesses(
            &[p("x")],
            &[p("x")],
            Some(&[]),
            MonomialOrder::Lexicographic,
            &limits
        ),
        Err(WitnessError::RowCount { .. })
    ));
}

// Valid membership identities cannot replace Buchberger or reducedness checks.
#[test]
fn witnesses_do_not_prove_grobner_or_reducedness() {
    let generators = [p("x*y-1"), p("y^2-1")];
    let report = certify_submitted_basis_with_witnesses(
        &generators,
        &generators,
        Some(&[vec![p("1"), p("0")], vec![p("0"), p("1")]]),
        MonomialOrder::Lexicographic,
        &MembershipLimits::default(),
    )
    .unwrap();
    assert_eq!(report.membership, MembershipStatus::Verified);
    assert!(!report.is_complete());
    let nonmonic = certify_submitted_basis_with_witnesses(
        &[p("x")],
        &[p("2*x")],
        Some(&[vec![p("2")]]),
        MonomialOrder::Lexicographic,
        &MembershipLimits::default(),
    )
    .unwrap();
    assert!(!nonmonic.is_complete());
}

// Resource exhaustion is inconclusive and cannot become successful evidence.
#[test]
fn witness_limits_are_distinct_from_false_identities() {
    use zeebra::grobner::WitnessLimit;
    for (limits, expected) in [
        (
            MembershipLimits {
                max_term_products: 0,
                ..MembershipLimits::default()
            },
            WitnessLimit::TermProducts,
        ),
        (
            MembershipLimits {
                max_live_terms: 0,
                ..MembershipLimits::default()
            },
            WitnessLimit::LiveTerms,
        ),
        (
            MembershipLimits {
                max_input_terms: 0,
                ..MembershipLimits::default()
            },
            WitnessLimit::InputTerms,
        ),
        (
            MembershipLimits {
                max_wall_time: std::time::Duration::ZERO,
                ..MembershipLimits::default()
            },
            WitnessLimit::WallTime,
        ),
    ] {
        assert_eq!(
            verify_ideal_membership(&[p("x")], &p("x"), &[p("1")], &limits),
            Ok(MembershipStatus::ResourceLimited(expected))
        );
    }
}

// Exponent overflow and weighted-order arity mismatch return typed input errors.
#[test]
fn invalid_shapes_never_reach_panicking_arithmetic() {
    use zeebra::{fields::Zp32003, Monomial, One, WeightedTieBreak};
    let huge = P::new(&[(Monomial::new(&[u32::MAX, 0]), Zp32003::one())]);
    assert_eq!(
        verify_ideal_membership(&[huge], &p("0"), &[p("x")], &MembershipLimits::default()),
        Err(WitnessError::ExponentOverflow)
    );
    let order = MonomialOrder::weighted(&[1], WeightedTieBreak::Lexicographic).unwrap();
    assert!(matches!(
        certify_submitted_basis_with_witnesses(
            &[p("x")],
            &[p("x")],
            Some(&[vec![p("1")]]),
            order,
            &MembershipLimits::default()
        ),
        Err(WitnessError::OrderArity { .. })
    ));
}

// Exact verification also runs over a cryptographically wide coefficient field.
#[test]
fn wide_field_witnesses() {
    use zeebra::fields::Bn254Fr;
    type W = MultivariatePolynomial<2, Bn254Fr>;
    let parse = |text| W::parse(text, ["x", "y"]).unwrap();
    assert_eq!(
        verify_ideal_membership(
            &[parse("x^2-y"), parse("x*y-1")],
            &parse("y^2-x"),
            &[parse("-y"), parse("x")],
            &MembershipLimits::default()
        ),
        Ok(MembershipStatus::Verified)
    );
}

// Coefficient-product budgets are shared across all basis witness rows.
#[test]
fn combined_rows_share_the_product_budget() {
    use zeebra::grobner::WitnessLimit;
    let generators = [p("x"), p("y")];
    let rows = [vec![p("1"), p("0")], vec![p("0"), p("1")]];
    let limits = MembershipLimits {
        max_term_products: 1,
        ..MembershipLimits::default()
    };
    for (target, row) in generators.iter().zip(&rows) {
        assert_eq!(
            verify_ideal_membership(&generators, target, row, &limits),
            Ok(MembershipStatus::Verified)
        );
    }
    let combined = certify_submitted_basis_with_witnesses(
        &generators,
        &generators,
        Some(&rows),
        MonomialOrder::Lexicographic,
        &limits,
    )
    .unwrap();
    assert_eq!(
        combined.membership,
        MembershipStatus::ResourceLimited(WitnessLimit::TermProducts)
    );
    assert!(!combined.is_complete());
    assert!(combined.certification.is_none());
}
