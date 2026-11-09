//! Shape position on the registered Anemoi CICO rows — the question #224 (D5) calls its most
//! concrete, pinned where it is cheap.
//!
//! `fglm::shape` was validated on katsura, cyclic, planted and the differential corpus and never on
//! a cryptanalytic system (`MILESTONE-FGLM-SCALABILITY.md` §8.3). Whether it fires on Anemoi decides
//! whether a Krylov route has a target here at all, and the answer is an **algebraic** fact — a
//! minimal-polynomial degree against a quotient dimension — so it belongs in the suite rather than
//! in a timed sweep. The low rungs are pinned here; `examples/anemoi_ladder.rs shape` reaches the
//! rungs whose bases cost seconds.

use zeebra::{
    fields::Zp18446744073709551263,
    grobner::{
        f4,
        fglm::{
            fglm_to_lex_with_options, separating_variables, shape_lex_basis, shape_report,
            FglmOptions, QuotientAlgebra,
        },
        research::{
            anemoi_cico::{dispatch_anemoi_cico, AnemoiCicoVisitor},
            challenge,
        },
    },
    KnownOrder, MonomialOrder, MultivariatePolynomial,
};

type A64 = Zp18446744073709551263;

const SOURCE: MonomialOrder = MonomialOrder::GradedReverseLexicographic;

/// What one row's shape-position probe found.
struct Found {
    dimension: usize,
    minimal_polynomial_degree: usize,
    separating: Vec<usize>,
    /// The shape route's lex basis equalled the classical conversion's.
    agrees: bool,
}

struct Probe;

impl<F: KnownOrder> AnemoiCicoVisitor<F> for Probe {
    type Output = Found;

    fn visit<const N: usize>(self, system: &[MultivariatePolynomial<N, F>]) -> Found {
        let basis = f4(system, SOURCE).expect("the low Anemoi rungs are inside every F4 budget");
        let options = FglmOptions::unbounded();
        let algebra =
            QuotientAlgebra::new(&basis, SOURCE, &options).expect("zero-dimensional, per #214");
        let report = shape_report(&algebra, N - 1);
        let shape = shape_lex_basis(&algebra).expect("shape position, asserted by the caller");
        let (classical, _) =
            fglm_to_lex_with_options(&basis, SOURCE, &options).expect("the classical route");
        Found {
            dimension: report.dimension,
            minimal_polynomial_degree: report.minimal_polynomial_degree,
            separating: separating_variables(&algebra),
            // The reduced lex basis is unique, so a shape basis that differs is simply wrong.
            agrees: shape == classical,
        }
    }
}

/// Both Anemoi models are in shape position at `N = 1, 2`, and the shape route's lex basis is the
/// classical conversion's.
#[test]
fn test_the_low_anemoi_rungs_are_in_shape_position() {
    let mut checked = 0;
    for id in [
        "anemoi64-cico-n1-fcico",
        "anemoi64-cico-n1-pcico",
        "anemoi64-cico-n2-fcico",
        "anemoi64-cico-n2-pcico",
    ] {
        let manifest = challenge(id).unwrap_or_else(|| panic!("{id} is registered"));
        let rounds = manifest.anemoi_parameters().expect("an Anemoi row").rounds;
        let instance = manifest
            .anemoi_cico_instance::<A64>()
            .expect("the registered field");
        let found = dispatch_anemoi_cico::<A64, _>(&instance, Probe).expect("a compiled dimension");

        // `(alpha + 2)^N` with alpha = 3, the registry's own invariant.
        let rounds = u32::try_from(rounds).expect("a small round count");
        assert_eq!(found.dimension, 5usize.pow(rounds), "{id}");
        // Shape position is exactly this equality, and it is what `is_separating` tests.
        assert_eq!(
            found.minimal_polynomial_degree, found.dimension,
            "{id}: the last variable does not generate the quotient algebra"
        );
        assert!(
            found.separating.contains(&(instance.variables() - 1)),
            "{id}: the lex-last variable must be among the separating ones"
        );
        assert!(
            found.agrees,
            "{id}: the shape route's lex basis differs from the classical conversion's"
        );
        checked += 1;
    }
    assert_eq!(checked, 4, "every row in the list was probed");
}
