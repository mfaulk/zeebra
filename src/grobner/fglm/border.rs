//! The border of the standard monomial basis, and where each operator column points.
//!
//! The standard monomials `B` are closed downwards, so multiplying one by a variable either stays
//! inside `B` or lands on the *border*
//!
//! ```text
//! ∂B = (union over i of x_i B) \ B.
//! ```
//!
//! A border monomial can be reached from several columns — `x*y` from both `x * y` and `y * x` —
//! and its normal form does not depend on which. M17 computed it once per column. Separating the
//! question "where does this column point" from the question "what is that monomial's normal form"
//! is what lets the second be answered once per monomial instead.
//!
//! This module answers only the first. It performs no field arithmetic and reduces nothing, which
//! is why the same index serves the per-column reference path and every deduplicated one: an
//! ablation between them then differs in the reduction and in nothing else.

use std::collections::{HashMap, HashSet};

use crate::{grobner::fglm::QuotientBasis, Monomial};

/// Where multiplication by a variable sends a standard monomial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ColumnTarget {
    /// Still standard, at this index into the quotient basis. The column is a unit vector.
    Standard(usize),

    /// On the border, at this index into [`BorderIndex::monomials`]. Needs a normal form — and
    /// **the same index means the same monomial**, so two columns carrying the same index have the
    /// same answer.
    Border(usize),
}

/// Every operator column classified, and the distinct border monomials they point at.
///
/// Built once per quotient algebra and shared by every variable, since the classification does not
/// depend on which reduction strategy follows it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BorderIndex<const N: usize> {
    /// The distinct border monomials, descending under the quotient basis's order.
    ///
    /// Deterministically ordered rather than in encounter order: the order decides which monomial
    /// a border index names, and a hash-map iteration order would make that vary between runs.
    monomials: Vec<Monomial<N>>,

    /// `targets[i * dimension + j]` is where `x_i b_j` goes. Row-major by variable.
    targets: Vec<ColumnTarget>,

    /// `D`, so a `(variable, column)` pair can be indexed.
    dimension: usize,
}

impl<const N: usize> BorderIndex<N> {
    /// Classify every `x_i b_j` for the given standard monomials.
    ///
    /// `N * D` monomial multiplications and `N * D` basis lookups, and no arithmetic over the
    /// field at all.
    pub fn new(quotient: &QuotientBasis<N>) -> Self {
        let dimension = quotient.dimension();
        let order = quotient.order();

        // Classified first, indexed second. A border monomial's index is its position in the
        // *sorted* list, which is not known until every one has been seen — so the classification
        // keeps the monomial itself and the indices are filled in afterwards, rather than the
        // `N * D` products and lookups being done twice.
        let mut classified: Vec<Result<usize, Monomial<N>>> = Vec::with_capacity(N * dimension);
        let mut monomials: Vec<Monomial<N>> = Vec::new();
        let mut seen: HashSet<Monomial<N>> = HashSet::new();

        for i in 0..N {
            for monomial in quotient.monomials() {
                // No overflow is reachable: a standard monomial's exponents are below their
                // variables' pure powers, and this raises one of them by one.
                let product = *monomial * Monomial::univariate(i, 1);
                classified.push(match quotient.index_of(&product) {
                    Some(index) => Ok(index),
                    None => {
                        if seen.insert(product) {
                            monomials.push(product);
                        }
                        Err(product)
                    }
                });
            }
        }

        monomials.sort_by(|a, b| order.cmp(b, a));
        let position: HashMap<Monomial<N>, usize> = monomials
            .iter()
            .enumerate()
            .map(|(index, monomial)| (*monomial, index))
            .collect();

        let targets: Vec<ColumnTarget> = classified
            .into_iter()
            .map(|classification| match classification {
                Ok(index) => ColumnTarget::Standard(index),
                Err(product) => ColumnTarget::Border(position[&product]),
            })
            .collect();

        Self {
            monomials,
            targets,
            dimension,
        }
    }

    /// `D`, the number of columns each operator has.
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// `|∂B|`, the distinct border monomials, descending under the order.
    pub fn monomials(&self) -> &[Monomial<N>] {
        &self.monomials
    }

    /// Where `x_variable b_column` goes.
    ///
    /// # Panics
    /// If `variable` is not below `N` or `column` is not below [`Self::dimension`].
    pub fn target(&self, variable: usize, column: usize) -> ColumnTarget {
        assert!(variable < N, "variable {} of {}", variable, N);
        assert!(
            column < self.dimension,
            "column {} of {}",
            column,
            self.dimension
        );
        self.targets[variable * self.dimension + column]
    }

    /// Every column of one operator, in order.
    pub fn column_targets(&self, variable: usize) -> &[ColumnTarget] {
        assert!(variable < N, "variable {} of {}", variable, N);
        let start = variable * self.dimension;
        &self.targets[start..start + self.dimension]
    }

    /// `N * D`.
    pub fn columns(&self) -> usize {
        self.targets.len()
    }

    /// Columns whose product stayed standard.
    pub fn standard_columns(&self) -> usize {
        self.targets
            .iter()
            .filter(|target| matches!(target, ColumnTarget::Standard(_)))
            .count()
    }

    /// Columns whose product left the staircase.
    pub fn border_columns(&self) -> usize {
        self.columns() - self.standard_columns()
    }
}

#[cfg(test)]
mod tests {
    use super::{BorderIndex, ColumnTarget};
    use crate::{
        fields::Zp2147483647,
        grobner::{
            benchmark_systems::{cyclic, katsura},
            f4,
            fglm::QuotientBasis,
        },
        Monomial, MonomialOrder, MultivariatePolynomial,
    };

    type F = Zp2147483647;

    const ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    const SYSTEMS: [&[&str]; 6] = [
        &["x^2", "y^2"],
        &["x^2 - y", "y^3 - 1"],
        &["x + y", "x*y - 1"],
        &["x^3 - 1", "y - x^2"],
        &["x^2 - 2*x + 1", "y - x"],
        &["x^4 - x", "y^2 - x"],
    ];

    fn quotient_of<const N: usize>(
        system: &[&str],
        variables: [&str; N],
        order: MonomialOrder,
    ) -> QuotientBasis<N> {
        let generators: Vec<MultivariatePolynomial<N, F>> = system
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, variables).unwrap())
            .collect();
        let basis = f4(&generators, order).expect("within limits");
        QuotientBasis::new(&basis, order, usize::MAX).expect("finite")
    }

    /// Every column is classified the way `QuotientBasis::index_of` classifies its product.
    ///
    /// The index is a cache of that lookup, so this is the whole of its correctness: a standard
    /// target must name the product's own index, and a border target must name the product.
    #[test]
    fn test_every_column_is_classified_correctly() {
        for order in ORDERS {
            for system in SYSTEMS {
                let quotient = quotient_of(system, ["x", "y"], order);
                let index = BorderIndex::new(&quotient);

                for i in 0..2 {
                    for (j, monomial) in quotient.monomials().iter().enumerate() {
                        let product = *monomial * Monomial::univariate(i, 1);
                        match (index.target(i, j), quotient.index_of(&product)) {
                            (ColumnTarget::Standard(got), Some(expected)) => assert_eq!(
                                got, expected,
                                "column {} of T_{} in {:?} under {:?}",
                                j, i, system, order
                            ),
                            (ColumnTarget::Border(border), None) => assert_eq!(
                                index.monomials()[border],
                                product,
                                "border target of column {} of T_{} in {:?} under {:?}",
                                j,
                                i,
                                system,
                                order
                            ),
                            (target, standard) => panic!(
                                "{:?} disagrees with index_of = {:?} for column {} of T_{} in \
                                 {:?} under {:?}",
                                target, standard, j, i, system, order
                            ),
                        }
                    }
                }
            }
        }
    }

    /// The same border monomial always gets the same index, however many columns reach it.
    ///
    /// The property deduplication rests on: a border index identifies a monomial, so two columns
    /// carrying one have provably the same normal form.
    #[test]
    fn test_a_repeated_border_monomial_has_one_index() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = f4(&katsura::<6, F>(), order).expect("within limits");
        let quotient = QuotientBasis::new(&basis, order, usize::MAX).expect("finite");
        let index = BorderIndex::new(&quotient);

        let mut repeats = 0;
        for i in 0..6 {
            for (j, monomial) in quotient.monomials().iter().enumerate() {
                if let ColumnTarget::Border(border) = index.target(i, j) {
                    let product = *monomial * Monomial::univariate(i, 1);
                    assert_eq!(index.monomials()[border], product);
                    repeats += 1;
                }
            }
        }
        assert!(
            index.monomials().len() < repeats,
            "{} border columns over {} distinct monomials is no repetition",
            repeats,
            index.monomials().len()
        );
    }

    /// The border monomials are distinct and descending under the quotient basis's order.
    #[test]
    fn test_the_border_is_distinct_and_ordered() {
        for order in ORDERS {
            for system in SYSTEMS {
                let quotient = quotient_of(system, ["x", "y"], order);
                let index = BorderIndex::new(&quotient);

                let distinct: std::collections::HashSet<Monomial<2>> =
                    index.monomials().iter().copied().collect();
                assert_eq!(
                    distinct.len(),
                    index.monomials().len(),
                    "a border monomial is listed twice in {:?} under {:?}",
                    system,
                    order
                );

                for pair in index.monomials().windows(2) {
                    assert_eq!(
                        order.cmp(&pair[0], &pair[1]),
                        std::cmp::Ordering::Greater,
                        "{} does not precede {} under {:?}",
                        pair[0],
                        pair[1],
                        order
                    );
                }
            }
        }
    }

    /// No border monomial is standard, and every standard monomial's every multiple is accounted
    /// for.
    #[test]
    fn test_the_border_is_disjoint_from_the_basis() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = f4(&cyclic::<5, F>(), order).expect("within limits");
        let quotient = QuotientBasis::new(&basis, order, usize::MAX).expect("finite");
        let index = BorderIndex::new(&quotient);

        for monomial in index.monomials() {
            assert!(
                quotient.index_of(monomial).is_none(),
                "{} is both standard and on the border",
                monomial
            );
        }
        assert_eq!(index.columns(), 5 * quotient.dimension());
        assert_eq!(
            index.standard_columns() + index.border_columns(),
            index.columns()
        );
    }

    /// Building the index twice gives the same index, so border indices are reproducible.
    #[test]
    fn test_the_index_is_deterministic() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = f4(&katsura::<5, F>(), order).expect("within limits");
        let quotient = QuotientBasis::new(&basis, order, usize::MAX).expect("finite");
        assert_eq!(BorderIndex::new(&quotient), BorderIndex::new(&quotient));
    }

    /// One operator's slice of targets is the same as asking column by column.
    #[test]
    fn test_the_column_slice_agrees_with_the_targets() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = f4(&katsura::<5, F>(), order).expect("within limits");
        let quotient = QuotientBasis::new(&basis, order, usize::MAX).expect("finite");
        let index = BorderIndex::new(&quotient);

        for i in 0..5 {
            let slice = index.column_targets(i);
            assert_eq!(slice.len(), quotient.dimension());
            for (j, target) in slice.iter().enumerate() {
                assert_eq!(*target, index.target(i, j));
            }
        }
    }

    /// The zero algebra of the unit ideal has no columns and no border.
    #[test]
    fn test_the_unit_ideal_has_no_border() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let generators: Vec<MultivariatePolynomial<2, F>> = ["x", "x - 1"]
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, ["x", "y"]).unwrap())
            .collect();
        let basis = f4(&generators, order).expect("within limits");
        let quotient = QuotientBasis::new(&basis, order, usize::MAX).expect("finite");
        let index = BorderIndex::new(&quotient);

        assert_eq!(quotient.dimension(), 0);
        assert_eq!(index.columns(), 0);
        assert!(index.monomials().is_empty());
    }
}
