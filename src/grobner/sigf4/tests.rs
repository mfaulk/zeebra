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
        benchmark_systems::{cyclic, eco, katsura, noon, reimer},
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

/// [`SigF4Options::checked`] accepting graded-lex (#1049): every system here is small, so #961
/// does not apply.
fn checked_any_graded() -> SigF4Options {
    SigF4Options {
        allow_graded_lex: true,
        ..SigF4Options::checked()
    }
}

fn agrees_with_f4<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
) {
    let expected = f4(system, order).expect("shipping F4 finishes");
    let (result, statistics) = sig_f4_reported(system, order, &checked_any_graded());
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

/// Pair and rejection counts by mechanism on Eco-7 and Katsura-7 stay pinned, so bookkeeping
/// changes cannot move which pairs are rejected or why. Re-pinned for #961, whose promoted reducer
/// rows reduce in their own batch pairs a later batch used to take.
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

const ECO_7: [usize; 13] = [2126, 19, 772, 629, 493, 120, 38, 92, 462, 26, 28322, 66, 57];
const KATSURA_7: [usize; 13] = [1030, 5, 417, 383, 137, 26, 19, 58, 377, 12, 79607, 46, 54];

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
            sig_f4_reported(&system, order, &checked_any_graded())
                .0
                .unwrap(),
            buchberger_reference(&system, order)
        );
        let system = cyclic::<3, Zp32003>();
        assert_eq!(
            sig_f4_reported(&system, order, &checked_any_graded())
                .0
                .unwrap(),
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

/// Graded-lex is refused unless the caller opts in (#1049): #961's memory and stall behaviour is
/// otherwise reachable by forcing the engine past the dispatcher.
#[test]
fn test_graded_lex_requires_opt_in() {
    let system = katsura::<3, Zp13>();
    let grlex = MonomialOrder::GradedLexicographic;
    assert!(matches!(
        sig_f4(&system, grlex),
        Err(SigF4Error::Unsupported { .. })
    ));
    let (result, _) = sig_f4_reported(&system, grlex, &SigF4Options::default());
    assert!(matches!(result, Err(SigF4Error::Unsupported { .. })));
    let opted_in = SigF4Options {
        allow_graded_lex: true,
        ..SigF4Options::checked()
    };
    let (result, _) = sig_f4_reported(&system, grlex, &opted_in);
    assert_eq!(result.unwrap(), f4(&system, grlex).unwrap());
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

/// The serial cascades (design 1 at one worker, design 2's pre-reduction at four) charge the live
/// budget (#962): a small limit is a typed refusal that abandons the batch unsettled, at two
/// fields, and a finished run reports a peak above it and within the default limit.
#[test]
fn test_serial_cascade_charges_the_live_budget() {
    fn charged<F: FiniteField>() {
        let system = katsura::<5, F>();
        for workers in [1, 4] {
            let serial = SigF4Options {
                workers,
                parallel_cascade: false,
                ..SigF4Options::checked()
            };
            let tight = SigF4Options {
                max_live_bytes: Some(2_000),
                ..serial.clone()
            };
            let (result, s) = sig_f4_reported(&system, GREVLEX, &tight);
            assert!(
                matches!(
                    result,
                    Err(SigF4Error::Budget(F4Error::TooManyLiveBytes {
                        limit: 2_000,
                        ..
                    }))
                ),
                "{workers} workers: {result:?}"
            );
            assert_eq!(
                s.batch_trace.len() + 1,
                s.batches,
                "the refused batch is abandoned before any target is settled"
            );
            let (result, s) = sig_f4_reported(&system, GREVLEX, &serial);
            result.expect("the default budget suffices");
            assert!(s.claim_peak_live_bytes > 2_000, "{workers} workers");
            assert!(s.claim_peak_live_bytes <= serial.max_live_bytes.expect("default is set"));
        }
    }
    charged::<Zp32003>();
    charged::<Goldilocks>();
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

/// Final interreduction runs in the engine's column space, not through polynomials, and its
/// reduced basis is the shipping F4's on every family and field here (#971 G2-2).
#[test]
fn test_interreduction_runs_in_the_engines_columns() {
    let (_, s) = sig_f4_reported(&katsura::<6, Zp32003>(), GREVLEX, &SigF4Options::default());
    assert!(s.interreduction_in_columns);
    assert!(s.interreduction_columns > 0);
    agrees_with_f4(&katsura::<6, Goldilocks>(), GREVLEX);
    agrees_with_f4(&eco::<7, Wide>(), GREVLEX);
    agrees_with_f4(&cyclic::<5, Wide>(), MonomialOrder::GradedLexicographic);
    agrees_with_f4(&noon::<5, Zp32003>(), GREVLEX);
}

/// A refused column-space interreduction falls back to the polynomial route with the same basis.
#[test]
fn test_refused_column_interreduction_falls_back_to_polynomials() {
    let system = katsura::<6, Goldilocks>();
    let options = SigF4Options {
        interreduction_live_entries: Some(10),
        ..SigF4Options::default()
    };
    let (fallback, s) = sig_f4_reported(&system, GREVLEX, &options);
    assert!(!s.interreduction_in_columns);
    assert_eq!(fallback.unwrap(), f4(&system, GREVLEX).unwrap());
}

/// Hashing new elements' terms is clocked on its own, inside bookkeeping (#971 Gate C).
#[test]
fn test_element_hashing_is_clocked_inside_bookkeeping() {
    let (result, s) = sig_f4_reported(&katsura::<6, Zp32003>(), GREVLEX, &SigF4Options::default());
    result.unwrap();
    assert!(s.element_hashing > std::time::Duration::ZERO);
    assert!(s.element_hashing <= s.bookkeeping);
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
        let actual = sig_f4_reported(&system, order, &checked_any_graded()).0.unwrap();
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
/// redundant elements are those the reduced basis drops, each batch counts its entries, and the
/// minimal selection before interreduction is clocked.
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
        assert!(log.minimal_selection > std::time::Duration::ZERO);
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

/// FNV-1a over a trace's text: stable across toolchains, unlike `DefaultHasher`.
fn fnv1a(text: &str) -> u64 {
    text.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| {
        (h ^ u64::from(b)).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

/// Every batch's rows and outcomes, the reduced basis and the matrix shape, digested.
fn trace_digest<const N: usize, F: FiniteField>(
    system: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    options: &SigF4Options,
) -> u64 {
    let (result, s) = sig_f4_reported(system, order, options);
    let basis = result.expect("signature engine finishes");
    let text = format!(
        "{:?}|{:?}|{:?}",
        s.batch_trace,
        basis,
        (
            s.targets,
            s.reducer_rows,
            s.coefficient_products,
            s.max_matrix_rows,
            s.max_matrix_columns
        )
    );
    fnv1a(&text)
}

type Wide = PrimeFieldElement64<18446744073709551263>;

/// Batch traces and reduced bases on every family here, and the wide prime, stay bit-identical to
/// the engine before #971's run-wide monomial table.
#[test]
fn test_batch_traces_are_pinned_across_families() {
    let checked = SigF4Options {
        check_signatures: true,
        allow_graded_lex: true,
        ..SigF4Options::default()
    };
    let cascade = SigF4Options {
        workers: 3,
        parallel_cascade: true,
        ..checked.clone()
    };
    let lex = MonomialOrder::GradedLexicographic;
    let digests = [
        trace_digest(&eco::<7, Goldilocks>(), GREVLEX, &checked),
        trace_digest(&eco::<8, Wide>(), GREVLEX, &checked),
        trace_digest(&katsura::<6, Wide>(), GREVLEX, &checked),
        trace_digest(&katsura::<7, Goldilocks>(), GREVLEX, &checked),
        trace_digest(&katsura::<5, Zp32003>(), lex, &checked),
        trace_digest(&cyclic::<5, Zp32003>(), GREVLEX, &checked),
        trace_digest(&cyclic::<5, Wide>(), lex, &checked),
        trace_digest(&noon::<5, Wide>(), GREVLEX, &checked),
        trace_digest(&reimer::<4, Zp32003>(), GREVLEX, &checked),
        trace_digest(&katsura::<6, Goldilocks>(), GREVLEX, &cascade),
        trace_digest(&eco::<9, Wide>(), GREVLEX, &checked),
        trace_digest(&katsura::<8, Wide>(), GREVLEX, &checked),
    ];
    assert_eq!(digests, PINNED_TRACES, "{digests:#x?}");
}

/// Re-pinned for #961: promoted reducer rows change the batches of every row whose engine run
/// promotes one; the reduced bases are unchanged. Earlier, re-pinned for #1056. The digest includes the reduced basis's `Debug` text. Before #1022 that
/// text listed terms in `HashMap` iteration order, which follows hashbrown's SIMD group width, so
/// these pins held on x86_64 only. #1022 made `Debug` canonical, which moved every digest and made
/// them the same on aarch64 and x86_64. The batch traces print no polynomial, so only the basis
/// part moved.
const PINNED_TRACES: [u64; 12] = [
    0x7aa4379e59afc74e,
    0x75ee21999af59906,
    0xa6e80d160fce6ba0,
    0x2cdd6ca4dc84f8f8,
    0x8b8760c931cc325a,
    0x5c758ef80a2bfee5,
    0x8a8d2a386756505b,
    0xee08298a80bbe28e,
    0x508de2381fee4a34,
    0x8b44df1ac45806d4,
    0x1ac9454fb8972d6d,
    0xfdd3f1c32a46b688,
];

/// Dense planted quadratics in `N` variables, `2N` equations: #945's family, small.
fn dense_quadratics<const N: usize, F: FiniteField>(
    seed: u64,
) -> Vec<MultivariatePolynomial<N, F>> {
    use rand::{rngs::StdRng, Rng, SeedableRng};
    let mut rng = StdRng::seed_from_u64(seed);
    let point: Vec<F> = (0..N).map(|_| F::new(rng.gen_range(0..u64::MAX))).collect();
    let mut support = Vec::new();
    for i in 0..N {
        for j in i..N {
            let mut e = [0; N];
            e[i] += 1;
            e[j] += 1;
            support.push(Monomial::new(&e));
        }
        let mut e = [0; N];
        e[i] = 1;
        support.push(Monomial::new(&e));
    }
    (0..2 * N)
        .map(|_| {
            let mut terms: Vec<(Monomial<N>, F)> = support
                .iter()
                .map(|m| (*m, F::new(rng.gen_range(1..u64::MAX))))
                .collect();
            let value = terms.iter().fold(F::zero(), |acc, (m, c)| {
                let mut v = *c;
                for (x, e) in point.iter().zip(m.exponents()) {
                    for _ in 0..*e {
                        v *= *x;
                    }
                }
                acc + v
            });
            terms.push((Monomial::new(&[0; N]), -value));
            MultivariatePolynomial::new(&terms)
        })
        .collect()
}

fn lane_agrees<const N: usize, F: FiniteField>(seed: u64) {
    let system = dense_quadratics::<N, F>(seed);
    for (workers, parallel_cascade) in [(1, false), (3, false), (4, true)] {
        let options = |small_prime_lane| SigF4Options {
            workers,
            parallel_cascade,
            small_prime_lane,
            check_signatures: true,
            ..SigF4Options::default()
        };
        let (field, field_stats) = sig_f4_reported(&system, GREVLEX, &options(false));
        let (lane, lane_stats) = sig_f4_reported(&system, GREVLEX, &options(true));
        assert_eq!(lane.unwrap(), field.unwrap(), "{workers} workers");
        // #945's corrective iteration: lane mode holds each pivot once, in lane form only.
        assert!(
            lane_stats.claim_peak_live_bytes <= field_stats.claim_peak_live_bytes,
            "{workers} workers: lane {} > field {} live bytes",
            lane_stats.claim_peak_live_bytes,
            field_stats.claim_peak_live_bytes
        );
        assert_eq!(
            (lane_stats.targets, lane_stats.elements_added),
            (field_stats.targets, field_stats.elements_added)
        );
    }
}

/// #945: the lane route returns the field route's basis on dense quadratics over GF(31) and
/// GF(32003), on design 1, design 2 and the parallel cascade, within the field route's live bytes.
#[test]
fn test_small_prime_lane_keeps_the_basis() {
    for seed in 0..3 {
        lane_agrees::<6, crate::fields::Zp31>(seed);
        lane_agrees::<6, Zp32003>(seed);
    }
}

/// #945: a field without a lane ignores the option.
#[test]
fn test_small_prime_lane_is_ignored_on_a_wide_field() {
    lane_agrees::<5, Goldilocks>(1);
}

/// #945: the lane is opt-in; neither the default nor the checked options turn it on.
#[test]
fn test_small_prime_lane_is_off_by_default() {
    assert!(!SigF4Options::default().small_prime_lane);
    assert!(!checked_any_graded().small_prime_lane);
}

/// #961: a reducer multiple of the batch's degree whose lead an element of smaller signature has
/// just taken is reduced in that batch, so on these inputs, which have no degree falls, every
/// signature degree is one batch. Before, the pair naming it waited for another batch of the same
/// degree: 14 batches over Katsura-7's 7 degrees, and 94 over Cyclic-6's 16.
#[test]
fn test_each_signature_degree_is_one_batch_without_degree_falls() {
    fn check<const N: usize, F: FiniteField>(system: &[MultivariatePolynomial<N, F>], name: &str) {
        let claim = SigF4Options {
            workers: 3,
            parallel_cascade: true,
            ..SigF4Options::default()
        };
        for options in [SigF4Options::default(), claim] {
            let (result, s) = sig_f4_reported(system, GREVLEX, &options);
            assert_eq!(result.unwrap(), f4(system, GREVLEX).unwrap(), "{name}");
            let degrees = &s.batch_degrees;
            assert!(
                degrees.windows(2).all(|w| w[0] < w[1]),
                "{name} at {} workers: batch degrees {degrees:?}",
                options.workers
            );
            assert!(
                s.promoted_reducers > 0,
                "{name}: no reducer row was promoted"
            );
        }
    }
    check(&katsura::<7, Goldilocks>(), "katsura-7");
    check(&cyclic::<6, Goldilocks>(), "cyclic-6");
}
