//! #1194's counting study: the module orders and rewrite orders of Eder–Faugère's RB framework
//! (EF §2, §7, §11) that the engine can run without a new design, selected per run by
//! [`super::SigF4Options::variant`]. Research only; a timed build compiles none of it.
//!
//! The choice lives in a thread-local for the duration of one serial run, so that
//! [`Signature::cmp_in`] keeps its signature and the engine's call sites are unchanged. Runs with
//! more than one worker refuse any variant but the default, since their workers would not see it.
//!
//! Every variant is a compatible module order (EF Def 2.2) and a rewrite order (EF Def 7.2) under
//! which batches of increasing key are processed in increasing signature order, so Lairez
//! Theorem 62 (RFC T4) holds and the reduced basis is the shipping F4's.

use std::{cell::Cell, cmp::Ordering};

use super::signature::Signature;
use crate::poly::MonomialOrder;

/// The order on shifted signatures `t·lm(f_i) ⊗ e_i` (EF Def 2.2).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ModuleOrder {
    /// `<lt-pot`: shifted monomial, then index. The engine's design (RFC §9).
    #[default]
    Schreyer,
    /// `<d-pot`: degree of the shifted monomial, then index, then the monomial. F4/5's order (EF
    /// Property 13.1(a)); batches stay by degree.
    DegreePot,
    /// `<pot`: index, then monomial. Incremental, as F5 and G2V (EF §3.5): batches run by index
    /// first, so the basis of `f_0..f_i` is complete before `f_{i+1}` enters. No F5C
    /// interreduction between indices (EF §8.2), which the survey's `<pot` figures include.
    Pot,
}

/// Which element rewrites a signature (EF Def 7.1).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum RewriteOrder {
    /// `⊴_rat`: the greatest sig-lead ratio, newest on a tie (EF Def 7.13). SB and today's GVW.
    #[default]
    Ratio,
    /// `⊴_add`: the newest element (EF §7.3). F5, G2V and the first GVW (EF §11.5).
    Newest,
}

/// One cell of EF §14's grid.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Variant {
    pub module: ModuleOrder,
    pub rewrite: RewriteOrder,
}

impl Variant {
    /// The six combinations, the default first.
    pub const ALL: [Variant; 6] = {
        use {ModuleOrder::*, RewriteOrder::*};
        [
            Variant::new(Schreyer, Ratio),
            Variant::new(Schreyer, Newest),
            Variant::new(DegreePot, Ratio),
            Variant::new(DegreePot, Newest),
            Variant::new(Pot, Ratio),
            Variant::new(Pot, Newest),
        ]
    };

    pub const fn new(module: ModuleOrder, rewrite: RewriteOrder) -> Self {
        Self { module, rewrite }
    }
}

thread_local! {
    static ACTIVE: Cell<Variant> = const { Cell::new(Variant::new(ModuleOrder::Schreyer, RewriteOrder::Ratio)) };
}

/// The variant of the run on this thread.
pub(super) fn active() -> Variant {
    ACTIVE.with(Cell::get)
}

/// Makes `variant` this thread's until dropped, then restores the previous one.
pub(super) struct Scope(Variant);

impl Scope {
    pub(super) fn new(variant: Variant) -> Self {
        Self(ACTIVE.with(|a| a.replace(variant)))
    }
}

impl Drop for Scope {
    fn drop(&mut self) {
        ACTIVE.with(|a| a.set(self.0));
    }
}

/// The active module order's comparison, or `None` under Schreyer, which
/// [`Signature::cmp_in`] computes itself.
pub(super) fn cmp<const N: usize>(
    a: &Signature<N>,
    b: &Signature<N>,
    order: MonomialOrder,
) -> Option<Ordering> {
    match active().module {
        ModuleOrder::Schreyer => None,
        ModuleOrder::DegreePot => Some(
            a.degree()
                .cmp(&b.degree())
                .then(a.index.cmp(&b.index))
                .then_with(|| order.cmp(&a.mono, &b.mono)),
        ),
        ModuleOrder::Pot => Some(
            a.index
                .cmp(&b.index)
                .then_with(|| order.cmp(&a.mono, &b.mono)),
        ),
    }
}

/// The pending queue's key for `sig`: its degree, or under `<pot` its index then its degree, so
/// the queue's least key is always the least signatures' batch.
pub(super) fn queue_key<const N: usize>(sig: &Signature<N>) -> u64 {
    match active().module {
        ModuleOrder::Pot => (u64::from(sig.index) << 40) | sig.degree(),
        _ => sig.degree(),
    }
}

/// Whether the rewriter takes the newest dividing element rather than the greatest ratio.
pub(super) fn newest_rewrites() -> bool {
    active().rewrite == RewriteOrder::Newest
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        fields::{PrimeFieldElement64, Zp32003},
        grobner::{
            benchmark_systems::{cyclic, eco, katsura},
            f4::f4,
            sigf4::{sig_f4_reported, SigF4Error, SigF4Options, SigF4Statistics},
        },
        FiniteField, Monomial, MultivariatePolynomial,
    };

    type Goldilocks = PrimeFieldElement64<18446744069414584321>;
    const GREVLEX: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

    fn sig(exponents: [u32; 2], index: u32) -> Signature<2> {
        Signature::new(Monomial::new(&exponents), index)
    }

    fn run<const N: usize, F: FiniteField>(
        system: &[MultivariatePolynomial<N, F>],
        variant: Variant,
    ) -> SigF4Statistics {
        let options = SigF4Options {
            variant,
            ..SigF4Options::checked()
        };
        let (result, stats) = sig_f4_reported(system, GREVLEX, &options);
        let expected = f4(system, GREVLEX).expect("shipping F4 finishes");
        assert_eq!(
            result.expect("the engine finishes"),
            expected,
            "{variant:?} changed the reduced basis"
        );
        stats
    }

    /// Each module order compares as EF Def 2.2 defines it, on shifted monomials.
    #[test]
    fn test_module_orders_compare_as_defined() {
        // Degree 3 at index 0 against degree 2 at index 1.
        let (high, low) = (sig([2, 1], 0), sig([1, 1], 1));
        let compare = |variant| {
            let _scope = Scope::new(variant);
            high.cmp_in(&low, GREVLEX)
        };
        use {ModuleOrder::*, RewriteOrder::Ratio};
        assert_eq!(compare(Variant::new(Schreyer, Ratio)), Ordering::Greater);
        assert_eq!(compare(Variant::new(DegreePot, Ratio)), Ordering::Greater);
        assert_eq!(compare(Variant::new(Pot, Ratio)), Ordering::Less);
        // Equal degree: d-pot puts the index first, Schreyer the monomial.
        let (a, b) = (sig([2, 0], 1), sig([1, 1], 0));
        let _scope = Scope::new(Variant::new(DegreePot, Ratio));
        assert_eq!(a.cmp_in(&b, GREVLEX), Ordering::Greater);
        drop(_scope);
        assert_eq!(a.cmp_in(&b, GREVLEX), GREVLEX.cmp(&a.mono, &b.mono));
    }

    /// A scope restores the variant it replaced, so a run leaves its thread at the default.
    #[test]
    fn test_scope_restores_the_previous_variant() {
        let pot = Variant::new(ModuleOrder::Pot, RewriteOrder::Newest);
        {
            let _outer = Scope::new(pot);
            {
                let _inner = Scope::new(Variant::default());
                assert_eq!(active(), Variant::default());
            }
            assert_eq!(active(), pot);
        }
        assert_eq!(active(), Variant::default());
        run(&katsura::<4, Zp32003>(), pot);
        assert_eq!(active(), Variant::default());
    }

    /// Every variant returns the shipping F4's reduced basis, with the signature discipline
    /// asserted on every row operation.
    #[test]
    fn test_every_variant_matches_f4() {
        for variant in Variant::ALL {
            run(&katsura::<5, Zp32003>(), variant);
            run(&cyclic::<5, Zp32003>(), variant);
            run(&eco::<6, Goldilocks>(), variant);
        }
    }

    /// The variants change the trajectory: `<pot` and `<d-pot` reduce nothing to zero on Katsura,
    /// which is regular (EF Cor 7.16, 7.17, Table 7), while Schreyer does (EF Table 7); and the
    /// rewrite order changes which rows are reduced under every module order on Eco-6.
    #[test]
    fn test_variants_change_the_trajectory_as_the_survey_reports() {
        use {ModuleOrder::*, RewriteOrder::*};
        let system = katsura::<6, Zp32003>();
        assert!(run(&system, Variant::new(Schreyer, Ratio)).reductions_to_zero > 0);
        assert_eq!(
            run(&system, Variant::new(DegreePot, Ratio)).reductions_to_zero,
            0
        );
        assert_eq!(run(&system, Variant::new(Pot, Ratio)).reductions_to_zero, 0);
        let system = eco::<6, Goldilocks>();
        for module in [Schreyer, DegreePot, Pot] {
            let ratio = run(&system, Variant::new(module, Ratio));
            let newest = run(&system, Variant::new(module, Newest));
            assert_ne!(
                ratio.coefficient_products, newest.coefficient_products,
                "{module:?}: the rewrite order changed nothing"
            );
            assert_eq!(newest.singular_rows, 0, "⊴_add keeps singular elements");
        }
    }

    /// `⊴_add` must keep singular elements, as RB does (EF Algorithm 2, line 13): discarding them,
    /// as `⊴_rat` may, hands their signatures to an older rewriter, and on Cyclic-7 under `<d-pot`
    /// and `<pot` the basis came out incomplete.
    #[test]
    fn test_newest_rewriter_keeps_cyclic_7_complete() {
        use {ModuleOrder::*, RewriteOrder::*};
        let system = cyclic::<7, Zp32003>();
        let expected = f4(&system, GREVLEX).expect("shipping F4 finishes");
        for module in [DegreePot, Pot] {
            let options = SigF4Options {
                variant: Variant::new(module, Newest),
                ..SigF4Options::default()
            };
            let (result, _) = sig_f4_reported(&system, GREVLEX, &options);
            assert_eq!(result.expect("the engine finishes"), expected, "{module:?}");
        }
    }

    /// Parallel workers would not see a thread's variant, so they refuse anything but the default.
    #[test]
    fn test_variants_refuse_parallel_runs() {
        let system = katsura::<4, Zp32003>();
        let pot = Variant::new(ModuleOrder::Pot, RewriteOrder::Ratio);
        for (workers, parallel_cascade) in [(2, false), (1, true)] {
            let options = SigF4Options {
                variant: pot,
                workers,
                parallel_cascade,
                ..SigF4Options::default()
            };
            let (result, _) = sig_f4_reported(&system, GREVLEX, &options);
            assert!(matches!(result, Err(SigF4Error::Unsupported { .. })));
            let default = SigF4Options {
                workers,
                parallel_cascade,
                ..SigF4Options::default()
            };
            assert!(sig_f4_reported(&system, GREVLEX, &default).0.is_ok());
        }
    }
}
