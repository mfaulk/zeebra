use std::time::Instant;
use zeebra::{
    fields::{Bn254Fr, Zp32003},
    grobner::{
        certify_submitted_basis, certify_submitted_basis_with_witnesses, MembershipLimits,
        MembershipStatus, WitnessLimit,
    },
    util::peak_resident_bytes,
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

fn run<F: FiniteField>(field: &str) {
    let p = |text| MultivariatePolynomial::<3, F>::parse(text, ["x", "y", "z"]).unwrap();
    let generators = [p("x^2-y"), p("x*y-1")];
    let basis = [p("x-y^2"), p("y^3-1")];
    let rows = [vec![p("y"), p("-x")], vec![p("-y^2"), p("x*y+1")]];
    let order = MonomialOrder::Lexicographic;
    let at = Instant::now();
    let old = certify_submitted_basis(&generators, &basis, order);
    let existing = at.elapsed();
    assert!(old.checks_passed() && !old.is_complete());
    let report = certify_submitted_basis_with_witnesses(
        &generators,
        &basis,
        Some(&rows),
        order,
        &MembershipLimits::default(),
    )
    .unwrap();
    assert!(report.is_complete());
    let terms: usize = rows.iter().flatten().map(|p| p.terms().len()).sum();
    println!(
        "field={field} existing_ns={} witness_ns={} cofactor_terms={terms} peak_process_bytes={:?}",
        existing.as_nanos(),
        report.witness_elapsed.as_nanos(),
        peak_resident_bytes()
    );
    let limited = certify_submitted_basis_with_witnesses(
        &generators,
        &basis,
        Some(&rows),
        order,
        &MembershipLimits {
            max_term_products: 0,
            ..MembershipLimits::default()
        },
    )
    .unwrap();
    assert_eq!(
        limited.membership,
        MembershipStatus::ResourceLimited(WitnessLimit::TermProducts)
    );
    assert!(!limited.is_complete());
    println!("field={field} zero_product_budget={:?}", limited.membership);
    assert!(certify_submitted_basis_with_witnesses(
        &[p("1")],
        &[p("1")],
        Some(&[vec![p("1")]]),
        order,
        &MembershipLimits::default()
    )
    .unwrap()
    .is_complete());
}

fn main() {
    run::<Zp32003>("GF32003");
    run::<Bn254Fr>("BN254Fr");
}
