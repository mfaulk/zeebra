//! The signature engine's output must equal the shipping F4's reduced basis coefficient for
//! coefficient (RFC §4 step 5); a plausible leading-term set is not evidence.

use proptest::prelude::*;

use super::{
    corpus::{correctness_constructions, Construction},
    sig_f4, sig_f4_reported,
    signature::{mask, Signature, SyzygySource, SyzygyStore},
    SigF4Error, SigF4Options,
};
use crate::{
    fields::{PrimeFieldElement64, Zp13, Zp32003},
    grobner::{
        benchmark_systems::{cyclic, eco, katsura},
        f4::{certify_f4_output, f4, F4Error},
        reference::buchberger_reference,
    },
    poly::MonomialOrder,
    FiniteField, Monomial, MultivariatePolynomial,
};

type Goldilocks = PrimeFieldElement64<18446744069414584321>;
const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;
const GRADED: [MonomialOrder; 2] = [
    MonomialOrder::GradedReverseLexicographic,
    MonomialOrder::GradedLexicographic,
];

fn agrees_with_f4<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) {
    let expected = f4(system, order).expect("shipping F4 finishes");
    let (result, statistics) = sig_f4_reported(system, order, &SigF4Options::checked());
    let actual = result.expect("signature engine finishes");
    assert_eq!(actual, expected, "reduced bases differ under {order:?}");
    let report = certify_f4_output(system, &actual, order);
    assert!(report.checks_passed(), "{:?}", report.first_failure());
    assert!(statistics.signature_basis_elements >= actual.len());
}

fn monomial<const N: usize>(exponents: [u32; N]) -> Monomial<N> {
    Monomial::new(&exponents)
}

/// Shifted signatures order by monomial first and break ties by index (Schreyer, RFC §3.1).
#[test]
fn test_signatures_compare_by_shifted_monomial_then_index() {
    let low = Signature::new(monomial([1, 0]), 1);
    let high = Signature::new(monomial([2, 0]), 0);
    assert!(low.cmp_in(&high, GREVLEX).is_lt());
    let same_low_index = Signature::new(monomial([2, 0]), 0);
    let same_high_index = Signature::new(monomial([2, 0]), 1);
    assert!(same_low_index.cmp_in(&same_high_index, GREVLEX).is_lt());
    assert!(high.cmp_in(&same_low_index, GREVLEX).is_eq());
}

/// Signature divisibility requires the same index and monomial divisibility.
#[test]
fn test_signature_divisibility_needs_the_same_index() {
    let s = Signature::new(monomial([1, 1]), 2);
    assert!(s.divides(&Signature::new(monomial([2, 1]), 2)));
    assert!(!s.divides(&Signature::new(monomial([2, 1]), 1)));
    assert!(!s.divides(&Signature::new(monomial([2, 0]), 2)));
}

/// The syzygy store keeps only minimal generators and reports which source covers a signature.
#[test]
fn test_syzygy_store_is_minimal_and_attributes_sources() {
    let mut store = SyzygyStore::<2>::new(2);
    assert!(store.insert(Signature::new(monomial([2, 1]), 0), SyzygySource::Koszul));
    assert!(store.insert(Signature::new(monomial([1, 0]), 0), SyzygySource::ZeroRow));
    // Dominated by the second entry, so it is not kept.
    assert!(!store.insert(Signature::new(monomial([3, 0]), 0), SyzygySource::Koszul));
    assert_eq!(
        store.len(),
        1,
        "the first entry is a multiple of the second"
    );
    assert_eq!(
        store.covering(&Signature::new(monomial([4, 4]), 0)),
        Some(SyzygySource::ZeroRow)
    );
    assert_eq!(store.covering(&Signature::new(monomial([4, 4]), 1)), None);
}

/// When two stored signatures cover a query, the earlier-inserted one names the source, also after
/// a removal compacts the bucket.
#[test]
fn test_syzygy_store_attributes_the_earliest_covering_entry() {
    let mut store = SyzygyStore::<3>::new(1);
    assert!(store.insert(Signature::new(monomial([5, 0, 0]), 0), SyzygySource::Koszul));
    assert!(store.insert(
        Signature::new(monomial([0, 1, 0]), 0),
        SyzygySource::ZeroRow
    ));
    assert!(store.insert(Signature::new(monomial([0, 0, 1]), 0), SyzygySource::Koszul));
    // Removes the first entry, so the zero-row entry becomes the earliest.
    assert!(store.insert(Signature::new(monomial([4, 0, 0]), 0), SyzygySource::Koszul));
    assert_eq!(store.len(), 3);
    let both = Signature::new(monomial([0, 1, 1]), 0);
    assert_eq!(store.covering(&both), Some(SyzygySource::ZeroRow));
    assert_eq!(
        store.covering(&Signature::new(monomial([4, 0, 1]), 0)),
        Some(SyzygySource::Koszul)
    );
}

/// Across more entries than one filter word holds, covering still names the earliest entry, in
/// the first word, a later word and the remainder.
#[test]
fn test_syzygy_store_finds_the_earliest_cover_past_one_word() {
    let mut store = SyzygyStore::<2>::new(1);
    for i in 0..20u32 {
        let source = if i % 3 == 0 {
            SyzygySource::ZeroRow
        } else {
            SyzygySource::Koszul
        };
        assert!(store.insert(Signature::new(monomial([i, 19 - i]), 0), source));
    }
    assert_eq!(store.len(), 20, "the entries are pairwise incomparable");
    let cover = |a, b| store.covering(&Signature::new(monomial([a, b]), 0));
    assert_eq!(cover(19, 19), Some(SyzygySource::ZeroRow), "entry 0");
    assert_eq!(cover(19, 18), Some(SyzygySource::Koszul), "entry 1");
    assert_eq!(cover(19, 10), Some(SyzygySource::ZeroRow), "entry 9");
    assert_eq!(cover(19, 1), Some(SyzygySource::ZeroRow), "entry 18");
    assert_eq!(cover(19, 0), Some(SyzygySource::Koszul), "entry 19");
    assert_eq!(cover(8, 9), None);
}

/// The divisibility mask sets, per variable band, one bit per exponent level up to the band width.
#[test]
fn test_mask_matches_its_per_level_definition() {
    fn reference<const N: usize>(m: &Monomial<N>) -> u64 {
        let band = (64 / N.max(1)).max(1);
        let mut mask = 0u64;
        for (v, &e) in m.exponents().iter().enumerate() {
            for k in 0..(e as usize).min(band) {
                if v * band + k < 64 {
                    mask |= 1 << (v * band + k);
                }
            }
        }
        mask
    }
    for e in 0..9u32 {
        let twelve = monomial([e, 0, 1, 2, 3, 4, 5, 6, 7, 8, e, 9]);
        assert_eq!(mask(&twelve), reference(&twelve));
        let one = monomial([e * 9]);
        assert_eq!(mask(&one), reference(&one));
        let seventy = Monomial::<70>::new(&[e; 70]);
        assert_eq!(mask(&seventy), reference(&seventy));
    }
}

/// Pair and rejection counts by mechanism on Eco-7 and Katsura-7 stay at the values the M30
/// engine produced, so bookkeeping changes cannot move which pairs are rejected or why.
#[test]
fn test_rejection_counts_by_mechanism_are_pinned() {
    let counts = |s: &super::SigF4Statistics| {
        [
            s.pairs_created,
            s.pairs_singular,
            s.rejected_product,
            s.rejected_koszul,
            s.rejected_zero_row,
            s.rejected_rewrite,
            s.rejected_duplicate,
            s.targets,
            s.reducer_rows,
            s.reductions_to_zero,
            s.coefficient_products as usize,
            s.signature_basis_elements,
            s.syzygy_signatures,
        ]
    };
    let eco = sig_f4_reported(&eco::<7, Goldilocks>(), GREVLEX, &SigF4Options::default()).1;
    let katsura = sig_f4_reported(
        &katsura::<7, Goldilocks>(),
        GREVLEX,
        &SigF4Options::default(),
    )
    .1;
    assert_eq!(counts(&eco), ECO_7);
    assert_eq!(counts(&katsura), KATSURA_7);
}

const ECO_7: [usize; 13] = [2192, 19, 807, 643, 486, 118, 52, 93, 528, 26, 31033, 67, 57];
const KATSURA_7: [usize; 13] = [1270, 5, 507, 471, 149, 62, 25, 63, 427, 12, 79774, 51, 54];

/// Katsura-4 agrees with the shipping F4 over GF(32003) and Goldilocks under both graded orders.
#[test]
fn test_katsura_4_matches_f4() {
    for order in GRADED {
        agrees_with_f4(&katsura::<4, Zp32003>(), order);
        agrees_with_f4(&katsura::<4, Goldilocks>(), order);
    }
}

/// Small systems also equal the independent Buchberger reference, not only the shipping F4.
#[test]
fn test_small_systems_match_the_buchberger_reference() {
    for order in GRADED {
        let system = katsura::<3, Zp13>();
        assert_eq!(
            sig_f4(&system, order).unwrap(),
            buchberger_reference(&system, order)
        );
        let system = cyclic::<3, Zp32003>();
        assert_eq!(
            sig_f4(&system, order).unwrap(),
            buchberger_reference(&system, order)
        );
    }
}

/// Positive-dimensional cyclic-4 and the non-regular Eco-5 agree with the shipping F4.
#[test]
fn test_positive_dimensional_and_non_regular_inputs_match_f4() {
    agrees_with_f4(&cyclic::<4, Zp32003>(), GREVLEX);
    agrees_with_f4(&cyclic::<4, Goldilocks>(), GREVLEX);
    agrees_with_f4(&eco::<5, Goldilocks>(), GREVLEX);
}

/// Every predeclared correctness construction (RFC §10.1) agrees with F4 at both fields.
#[test]
fn test_correctness_constructions_match_f4() {
    for construction in correctness_constructions() {
        match construction.variables() {
            4 => {
                agrees_with_f4(&construction.system::<4, Zp32003>(), GREVLEX);
                agrees_with_f4(&construction.system::<4, Goldilocks>(), GREVLEX);
            }
            10 => {
                agrees_with_f4(&construction.system::<10, Zp32003>(), GREVLEX);
                agrees_with_f4(&construction.system::<10, Goldilocks>(), GREVLEX);
            }
            n => panic!("no arity {n} instantiation for {}", construction.name),
        }
    }
}

/// The construction digests are pinned before any timing, as RFC §10.1 requires.
#[test]
fn test_correctness_construction_digests_are_pinned() {
    let digests: Vec<(&str, u64, String)> = correctness_constructions()
        .iter()
        .flat_map(|c: &Construction| {
            [32_003, 18_446_744_069_414_584_321]
                .into_iter()
                .map(move |p| (c.name, p, c.instance(p).digest()))
        })
        .collect();
    let expected: Vec<(&str, u64, String)> = super::corpus::PINNED_DIGESTS
        .iter()
        .map(|(name, p, digest)| (*name, *p, digest.to_string()))
        .collect();
    assert_eq!(digests, expected);
}

/// Lex and other non-graded orders are refused with a typed error rather than computed.
#[test]
fn test_non_graded_orders_are_unsupported() {
    let system = katsura::<3, Zp13>();
    assert!(matches!(
        sig_f4(&system, MonomialOrder::Lexicographic),
        Err(SigF4Error::Unsupported { .. })
    ));
}

/// Degenerate inputs follow F4's contract: zero ideal empty, inconsistent system `{1}`.
#[test]
fn test_degenerate_inputs_follow_the_f4_contract() {
    let zero = MultivariatePolynomial::<2, Zp13>::zero();
    assert_eq!(
        sig_f4(std::slice::from_ref(&zero), GREVLEX).unwrap(),
        Vec::new()
    );
    let x = MultivariatePolynomial::<2, Zp13>::parse("x", ["x", "y"]).unwrap();
    let x_minus_one = MultivariatePolynomial::<2, Zp13>::parse("x - 1", ["x", "y"]).unwrap();
    assert_eq!(
        sig_f4(&[x.clone(), x_minus_one, zero], GREVLEX).unwrap(),
        vec![MultivariatePolynomial::one()]
    );
    assert_eq!(
        sig_f4(&[x.clone(), x.scale(&Zp13::new(3))], GREVLEX).unwrap(),
        vec![x]
    );
}

/// A basis-size budget surfaces as the shipping F4's typed error.
#[test]
fn test_basis_budget_returns_a_typed_error() {
    let options = SigF4Options {
        max_basis_elements: Some(3),
        ..SigF4Options::default()
    };
    let (result, _) = sig_f4_reported(&katsura::<4, Zp32003>(), GREVLEX, &options);
    assert!(matches!(
        result,
        Err(SigF4Error::Budget(F4Error::TooManyBasisElements {
            limit: 3,
            ..
        }))
    ));
}

/// A zero wall budget stops after the first batch with the shipping F4's typed error.
#[test]
fn test_wall_budget_returns_a_typed_error() {
    let options = SigF4Options {
        max_wall_time: Some(std::time::Duration::ZERO),
        ..SigF4Options::default()
    };
    let (result, statistics) = sig_f4_reported(&katsura::<5, Zp32003>(), GREVLEX, &options);
    assert!(matches!(
        result,
        Err(SigF4Error::Budget(F4Error::TimeBudgetExceeded { .. }))
    ));
    assert_eq!(statistics.batches, 1, "one batch is always reduced");
}

/// The counters partition as RFC §10.1 reports them: zero-row work is part of the total.
#[test]
fn test_statistics_are_internally_consistent() {
    let (result, s) = sig_f4_reported(&katsura::<5, Zp32003>(), GREVLEX, &SigF4Options::default());
    let basis = result.unwrap();
    assert!(s.products_on_zero_rows + s.products_on_singular_rows <= s.coefficient_products);
    assert_eq!(s.zero_rows, s.reductions_to_zero);
    assert_eq!(
        s.rows_adding_no_rank,
        s.reductions_to_zero + s.singular_rows,
        "a target adds no rank when it ends zero or singular"
    );
    assert_eq!(s.signature_basis_elements, s.elements_added);
    assert!(s.signature_basis_elements >= basis.len());
    assert_eq!(s.reduced_basis_elements, basis.len());
    assert!(s.targets >= s.elements_added + s.rows_adding_no_rank);
    assert!(s.signature_metadata_bytes > 0);
}

/// Every criterion fires on Katsura-6, so the equality tests are not passing on a criterion-free
/// engine, and fewer targets reduce to zero than pairs are rejected.
#[test]
fn test_every_criterion_rejects_something_on_katsura_6() {
    let (result, s) = sig_f4_reported(&katsura::<6, Zp32003>(), GREVLEX, &SigF4Options::checked());
    result.unwrap();
    assert!(s.rejected_koszul > 0, "{s:?}");
    assert!(s.rejected_rewrite > 0, "{s:?}");
    assert!(s.rejected_product > 0, "{s:?}");
    assert!(s.reductions_to_zero < s.rejected_rewrite + s.rejected_koszul);
}

/// Design 2's parallel pre-reduction returns the same basis and does the same work-avoiding
/// decisions as the serial design 1, on a field that crosses threads.
#[test]
fn test_parallel_pre_reduction_matches_the_serial_engine() {
    let system = katsura::<6, Goldilocks>();
    let (serial, s) = sig_f4_reported(&system, GREVLEX, &SigF4Options::checked());
    let options = SigF4Options {
        workers: 4,
        ..SigF4Options::checked()
    };
    let (parallel, p) = sig_f4_reported(&system, GREVLEX, &options);
    assert_eq!(parallel.unwrap(), serial.unwrap());
    assert_eq!(
        (p.targets, p.reductions_to_zero, p.elements_added),
        (s.targets, s.reductions_to_zero, s.elements_added)
    );
    assert_eq!(p.rejected_rewrite, s.rejected_rewrite);
}

fn polynomial_strategy<F: FiniteField + 'static>(
    modulus: u64,
) -> impl Strategy<Value = MultivariatePolynomial<3, F>> {
    prop::collection::vec(((0u32..3, 0u32..3, 0u32..3), 1..modulus), 1..5).prop_map(|terms| {
        let terms: Vec<(Monomial<3>, F)> = terms
            .into_iter()
            .map(|((a, b, c), v)| (Monomial::new(&[a, b, c]), F::new(v)))
            .collect();
        MultivariatePolynomial::new(&terms)
    })
}

/// Interreduction sweeps tails against the fixed closure (#879), so its live entries never exceed
/// the built matrix plus one dense working row, and the basis still equals F4's.
#[test]
fn test_interreduction_never_grows_past_its_construction() {
    for system in [eco::<7, Goldilocks>(), katsura::<7, Goldilocks>()] {
        let expected = f4(&system, GREVLEX).unwrap();
        let (result, statistics) = sig_f4_reported(&system, GREVLEX, &SigF4Options::checked());
        assert_eq!(result.unwrap(), expected);
        assert!(statistics.interreduction_nonzeros > 0, "a matrix was built");
        assert!(
            statistics.interreduction_peak_nonzeros
                <= statistics.interreduction_nonzeros + statistics.interreduction_columns,
            "peak {} against {} built over {} columns",
            statistics.interreduction_peak_nonzeros,
            statistics.interreduction_nonzeros,
            statistics.interreduction_columns
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(96))]

    /// Random small systems over GF(13) agree with F4 under both graded orders.
    #[test]
    fn test_random_systems_over_gf13_match_f4(
        system in prop::collection::vec(polynomial_strategy::<Zp13>(13), 1..5),
        grlex in any::<bool>(),
    ) {
        let order = GRADED[usize::from(grlex)];
        let expected = f4(&system, order).unwrap();
        let actual = sig_f4_reported(&system, order, &SigF4Options::checked()).0.unwrap();
        prop_assert_eq!(actual, expected);
    }

    /// Random small systems over GF(32003) agree with F4 under grevlex.
    #[test]
    fn test_random_systems_over_gf32003_match_f4(
        system in prop::collection::vec(polynomial_strategy::<Zp32003>(32003), 2..6),
    ) {
        let expected = f4(&system, GREVLEX).unwrap();
        let actual = sig_f4_reported(&system, GREVLEX, &SigF4Options::checked()).0.unwrap();
        prop_assert_eq!(actual, expected);
    }
}

/// The #939 symbolic split has one record per batch, its components fit inside its total, and it
/// clocks one reducer lookup per column.
#[cfg(feature = "research-sigf4-split")]
#[test]
fn test_symbolic_split_covers_every_batch() {
    let system = katsura::<6, Goldilocks>();
    for workers in [1, 4] {
        let options = SigF4Options {
            workers,
            ..SigF4Options::checked()
        };
        let (_, s) = sig_f4_reported(&system, GREVLEX, &options);
        let log = &s.split.symbolic;
        assert_eq!(log.len(), s.batches);
        for b in log {
            assert!(b.reducer_search + b.multiply + b.interning + b.column_sort <= b.total);
            assert!(b.terms > 0);
        }
        let searches: u64 = log.iter().map(|b| b.searches).sum();
        let columns: u64 = s.split.batches.iter().map(|b| b.columns as u64).sum();
        assert_eq!(searches, columns);
    }
}

/// #970's ledger: every element-adding row's products land on a kept or a redundant element,
/// redundant elements are those the reduced basis drops, and each batch counts its entries.
#[cfg(feature = "research-sigf4-split")]
#[test]
fn test_element_ledger_splits_products_into_kept_and_redundant() {
    let system = katsura::<6, Goldilocks>();
    for workers in [1, 4] {
        let options = SigF4Options {
            workers,
            ..SigF4Options::checked()
        };
        let (_, s) = sig_f4_reported(&system, GREVLEX, &options);
        let log = &s.split;
        assert_eq!(
            log.redundant_elements,
            s.signature_basis_elements - s.reduced_basis_elements
        );
        assert!(log.redundant_elements > 0);
        assert_eq!(
            log.products_on_kept_elements + log.products_on_redundant_elements,
            s.coefficient_products - s.products_on_zero_rows - s.products_on_singular_rows
        );
        for b in &log.batches {
            assert!(b.entries >= (b.targets + b.reducers) as u64);
        }
    }
}

/// The #901 split accounts for every coefficient product, per batch, at one and four workers.
#[cfg(feature = "research-sigf4-split")]
#[test]
fn test_elimination_split_accounts_for_every_product() {
    let system = katsura::<6, Goldilocks>();
    for workers in [1, 4] {
        let options = SigF4Options {
            workers,
            ..SigF4Options::checked()
        };
        let (_, s) = sig_f4_reported(&system, GREVLEX, &options);
        let log = &s.split;
        assert_eq!(log.batches.len(), s.batches);
        let sum: u64 = log
            .batches
            .iter()
            .map(|b| b.parallel_products + b.serial_reducer_products + b.cascade_products)
            .sum();
        assert_eq!(sum, s.coefficient_products);
        assert_eq!(
            log.batches.iter().map(|b| b.targets).sum::<usize>(),
            s.targets
        );
        assert!(log.batches.iter().any(|b| b.cascade_products > 0));
        if workers == 1 {
            assert!(log.batches.iter().all(|b| b.parallel_products == 0));
        } else {
            assert!(log.batches.iter().any(|b| b.parallel_products > 0));
        }
    }
}
