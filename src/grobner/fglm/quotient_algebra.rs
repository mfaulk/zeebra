//! `A = R/I` for a zero-dimensional ideal: coordinate vectors over the standard monomials, and
//! the operators that multiply by a variable.
//!
//! This is the whole of the algebra FGLM needs. Multiplication by an arbitrary element is not
//! provided, because the conversion never performs one: it starts from the class of 1 and reaches
//! every candidate monomial by applying one variable at a time.

use crate::{
    grobner::{
        f4::StageClock,
        fglm::{
            border::{BorderIndex, ColumnTarget},
            multiplication::{MultiplicationOperator, OperatorBuilder},
            options::OperatorConstruction,
            statistics::{BorderStatistics, FglmStageTimings},
            FglmError, FglmOptions, QuotientBasis,
        },
    },
    FiniteField, Monomial, MonomialOrder, MultivariatePolynomial,
};

/// What building the quotient algebra did: the shape of the border, and where the time went.
///
/// The durations are zero unless [`FglmOptions::measure_stages`] was set; the counters are
/// collected either way.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct QuotientStatistics {
    /// How many products stayed standard, how many did not, and how many of those repeated.
    pub border: BorderStatistics,

    /// The construction stages. [`FglmStageTimings::dependence`] is not one of them and stays
    /// zero: nothing here performs the lex walk.
    pub timings: FglmStageTimings,
}

/// `R/I` as a `D`-dimensional `F`-vector space, with the `N` multiplication operators.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QuotientAlgebra<const N: usize, F: FiniteField> {
    basis: QuotientBasis<N>,
    operators: Vec<MultiplicationOperator<F>>,

    /// The source Gröbner basis, kept so that `coordinates` can reduce a polynomial the caller
    /// supplies. The operators answer every question about *monomials*, but not about an
    /// arbitrary polynomial, and a Gröbner basis of a zero-dimensional ideal is a handful of
    /// elements against the operators' `N * D` columns.
    source: Vec<MultivariatePolynomial<N, F>>,
}

impl<const N: usize, F: FiniteField> QuotientAlgebra<N, F> {
    /// Build the quotient algebra of the ideal `basis` generates.
    ///
    /// `basis` must be a Gröbner basis under `order`.
    ///
    /// Column `j` of `T_i` is the coordinate vector of the normal form of `x_i * b_j`. Where that
    /// product is itself a standard monomial no reduction is performed at all, which is most of
    /// them.
    ///
    /// # Errors
    /// [`FglmError::PositiveDimensional`] if the quotient is infinite-dimensional,
    /// [`FglmError::QuotientDimensionExceeded`] if the standard monomials exceed
    /// `options.max_quotient_dimension`, and [`FglmError::OperatorStorageExceeded`] if the
    /// operators need more entries than `options.max_operator_entries`. The last is checked as
    /// each column is built, so the overshoot is bounded by one column.
    pub fn new(
        basis: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
        options: &FglmOptions,
    ) -> Result<Self, FglmError> {
        Self::new_with_statistics(basis, order, options).map(|(algebra, _)| algebra)
    }

    /// As [`Self::new`], additionally reporting the border's shape and the construction's stages.
    ///
    /// # The two strategies
    /// Both begin by classifying every `x_i b_j` with a [`BorderIndex`], which performs no field
    /// arithmetic. They differ only in whether a border monomial reached from several columns is
    /// reduced once or once per column, so an ablation between them is an ablation of the sharing
    /// and of nothing else. See [`OperatorConstruction`].
    pub fn new_with_statistics(
        basis: &[MultivariatePolynomial<N, F>],
        order: MonomialOrder,
        options: &FglmOptions,
    ) -> Result<(Self, QuotientStatistics), FglmError> {
        let mut clock = StageClock::new(options.measure_stages);
        let mut statistics = QuotientStatistics::default();

        let quotient = QuotientBasis::new(basis, order, options.max_quotient_dimension)?;
        let dimension = quotient.dimension();
        statistics.timings.quotient_basis = clock.lap();

        let index = BorderIndex::new(&quotient);
        statistics.border = BorderStatistics {
            operator_columns: index.columns(),
            standard_columns: index.standard_columns(),
            border_columns: index.border_columns(),
            distinct_border_monomials: index.monomials().len(),
            normal_form_calls: 0,
        };
        statistics.timings.border_classification = clock.lap();

        // The shared answers, when they are shared. Indexed by border index, so a column's answer
        // is a lookup — and `|∂B|` coordinate vectors are held at once, which the per-column path
        // does not do. That is the trade this strategy makes.
        //
        // **Budgeted as it fills**, not left until the columns are pushed. Every distinct border
        // monomial appears in at least one column, so the shared entries are bounded by the
        // operators' own — which means checking them against `max_operator_entries` can never
        // reject a system the reference path would have accepted, and the construction's peak
        // under this strategy is at most twice the limit rather than unbounded.
        let shared: Vec<Vec<(usize, F)>> = match options.operator_construction {
            OperatorConstruction::PerColumn => Vec::new(),
            OperatorConstruction::DeduplicatedBorder => {
                let mut shared = Vec::with_capacity(index.monomials().len());
                let mut shared_entries = 0usize;
                for monomial in index.monomials() {
                    let column = reduce_border_monomial(
                        *monomial,
                        basis,
                        order,
                        &quotient,
                        &mut statistics,
                        &mut clock,
                    );
                    shared_entries = shared_entries.checked_add(column.len()).ok_or(
                        FglmError::OperatorStorageExceeded {
                            entries: usize::MAX,
                            limit: options.max_operator_entries,
                        },
                    )?;
                    if shared_entries > options.max_operator_entries {
                        return Err(FglmError::OperatorStorageExceeded {
                            entries: shared_entries,
                            limit: options.max_operator_entries,
                        });
                    }
                    shared.push(column);
                }
                shared
            }
        };

        let mut operators = Vec::with_capacity(N);
        let mut entries = 0usize;

        for i in 0..N {
            let mut builder = OperatorBuilder::with_capacity(dimension);
            for target in index.column_targets(i) {
                let column = match *target {
                    ColumnTarget::Standard(standard) => {
                        builder.push_standard(standard);
                        continue;
                    }
                    ColumnTarget::Border(border) => match options.operator_construction {
                        // Cloned rather than shared behind a reference count: every column owning
                        // its own vector is what M17 stored, so this strategy changes the time and
                        // leaves the storage alone. Sharing the representation is M18-3's question.
                        OperatorConstruction::DeduplicatedBorder => shared[border].clone(),
                        OperatorConstruction::PerColumn => reduce_border_monomial(
                            index.monomials()[border],
                            basis,
                            order,
                            &quotient,
                            &mut statistics,
                            &mut clock,
                        ),
                    },
                };

                entries = entries.checked_add(column.len()).ok_or(
                    FglmError::OperatorStorageExceeded {
                        entries: usize::MAX,
                        limit: options.max_operator_entries,
                    },
                )?;
                if entries > options.max_operator_entries {
                    return Err(FglmError::OperatorStorageExceeded {
                        entries,
                        limit: options.max_operator_entries,
                    });
                }
                builder.push_reduced(column);
            }
            operators.push(builder.finish());
        }

        // So that the stages partition the construction rather than leaving a tail outside all of
        // them. What is in this lap is the column loop's own bookkeeping and the clones.
        statistics.timings.column_assembly += clock.lap();

        Ok((
            Self {
                basis: quotient,
                operators,
                source: basis.to_vec(),
            },
            statistics,
        ))
    }

    /// Entries the `N` operators hold between them.
    pub fn operator_entries(&self) -> usize {
        self.operators
            .iter()
            .map(MultiplicationOperator::stored_entries)
            .sum()
    }

    /// Bytes the `N` operators' representations occupy. See
    /// [`MultiplicationOperator::stored_bytes`] for what that does and does not include.
    pub fn operator_bytes(&self) -> usize {
        self.operators
            .iter()
            .map(MultiplicationOperator::stored_bytes)
            .sum()
    }

    /// `D = dim_F(R/I)`.
    pub fn dimension(&self) -> usize {
        self.basis.dimension()
    }

    /// The standard monomials the coordinates are taken over.
    pub fn quotient_basis(&self) -> &QuotientBasis<N> {
        &self.basis
    }

    /// `T_i`, multiplication by `x_i`.
    ///
    /// # Panics
    /// If `variable` is not below `N`.
    pub fn operator(&self, variable: usize) -> &MultiplicationOperator<F> {
        &self.operators[variable]
    }

    /// The coordinate vector of the residue class of 1.
    ///
    /// The first unit vector, since [`QuotientBasis`] is sorted ascending and 1 is below every
    /// other monomial in every monomial order. Empty for the unit ideal, whose quotient is the
    /// zero space — there, 1 and 0 are the same class.
    pub fn one(&self) -> Vec<F> {
        let mut v = vec![F::zero(); self.dimension()];
        if let Some(first) = v.first_mut() {
            *first = F::one();
        }
        v
    }

    /// `T_i` applied to a coordinate vector.
    ///
    /// # Panics
    /// If `variable` is not below `N`, or `v` is not of length [`Self::dimension`].
    pub fn multiply_by_variable(&self, variable: usize, v: &[F]) -> Vec<F> {
        self.operators[variable].apply(v)
    }

    /// The coordinate vector of a polynomial's residue class.
    ///
    /// Infallible, and not for lack of a failure to report. A normal form's every term is
    /// standard by construction: `normal_form` moves a term to the remainder exactly when no
    /// leading monomial of the divisors divides it, which is the definition of a standard
    /// monomial. The divisors here are the same basis whose leading monomials defined the
    /// quotient, with zeros dropped on both sides, so a term outside the basis cannot survive the
    /// reduction and there is nothing for a `Result` to carry.
    pub fn coordinates(&self, p: &MultivariatePolynomial<N, F>) -> Vec<F> {
        let mut v = vec![F::zero(); self.dimension()];
        for (index, value) in self.sparse_coordinates(p) {
            v[index] = value;
        }
        v
    }

    /// The normal form a coordinate vector represents. The inverse of [`Self::coordinates`].
    ///
    /// # Panics
    /// If `v` is not of length [`Self::dimension`].
    pub fn polynomial(&self, v: &[F]) -> MultivariatePolynomial<N, F> {
        assert_eq!(
            v.len(),
            self.dimension(),
            "a coordinate vector of {} entries in a quotient algebra of dimension {}",
            v.len(),
            self.dimension()
        );
        let terms: Vec<(Monomial<N>, F)> = self
            .basis
            .monomials()
            .iter()
            .zip(v)
            .filter(|(_, value)| !value.is_zero())
            .map(|(monomial, value)| (*monomial, *value))
            .collect();
        MultivariatePolynomial::new(&terms)
    }

    /// The source Gröbner basis the quotient was built from.
    pub fn source_basis(&self) -> &[MultivariatePolynomial<N, F>] {
        &self.source
    }

    /// The nonzero coordinates of a polynomial's residue class, ascending by index.
    fn sparse_coordinates(&self, p: &MultivariatePolynomial<N, F>) -> Vec<(usize, F)> {
        let normal_form = p.normal_form(&self.source, self.basis.order());
        coordinates_of_normal_form(&normal_form, &self.basis)
    }
}

/// One border monomial's normal form, as a sorted coordinate vector.
///
/// The one place a border reduction happens, so that both strategies reduce *identically* and an
/// ablation between them cannot accidentally be an ablation of two different reductions. Counts
/// the call and laps the clock, so the stage breakdown is the same either way.
fn reduce_border_monomial<const N: usize, F: FiniteField>(
    monomial: Monomial<N>,
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    quotient: &QuotientBasis<N>,
    statistics: &mut QuotientStatistics,
    clock: &mut StageClock,
) -> Vec<(usize, F)> {
    // A one-term polynomial per reduction. §5.3 of the milestone proposal asks whether this is
    // worth a specialized entry point that takes a monomial directly. Measured, it is 0.07% to
    // 0.38% of the reduction it precedes on the families where reduction dominates, so it is not —
    // see §5.3 of docs/MILESTONE-FGLM-SCALABILITY.md for the measurement and for the one family
    // where the share is larger and still does not matter.
    let term = MultivariatePolynomial::new(&[(monomial, F::one())]);
    let reduced = term.normal_form(basis, order);
    statistics.border.normal_form_calls += 1;
    statistics.timings.normal_forms += clock.lap();

    let column = coordinates_of_normal_form(&reduced, quotient);
    statistics.timings.column_assembly += clock.lap();
    column
}

/// The nonzero coordinates of an already-reduced polynomial, ascending by index.
///
/// # Panics
/// If a term's monomial is not standard. Unreachable for the output of `normal_form` against the
/// basis the quotient was built from — see [`QuotientAlgebra::coordinates`] — so reaching it means
/// the two have been given different divisor sets.
fn coordinates_of_normal_form<const N: usize, F: FiniteField>(
    normal_form: &MultivariatePolynomial<N, F>,
    quotient: &QuotientBasis<N>,
) -> Vec<(usize, F)> {
    let mut entries: Vec<(usize, F)> = normal_form
        .terms()
        .iter()
        .map(|(monomial, coefficient)| {
            let index = quotient.index_of(monomial).unwrap_or_else(|| {
                panic!(
                    "{} survived reduction but is not a standard monomial",
                    monomial
                )
            });
            (index, *coefficient)
        })
        .collect();
    entries.sort_unstable_by_key(|(index, _)| *index);
    entries
}

#[cfg(test)]
mod tests {
    use super::QuotientAlgebra;
    use crate::{
        fields::Zp2147483647,
        grobner::{
            benchmark_systems::{cyclic, katsura, planted},
            f4,
            fglm::{FglmError, FglmOptions, OperatorConstruction},
        },
        FiniteField, Monomial, MonomialOrder, MultivariatePolynomial, One, Zero,
    };

    type F = Zp2147483647;

    const ORDERS: [MonomialOrder; 3] = [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ];

    /// The zero-dimensional two-variable systems the identities are checked on.
    const SYSTEMS: [&[&str]; 6] = [
        &["x^2", "y^2"],
        &["x^2 - y", "y^3 - 1"],
        &["x + y", "x*y - 1"],
        &["x^3 - 1", "y - x^2"],
        &["x^2 - 2*x + 1", "y - x"],
        &["x^4 - x", "y^2 - x"],
    ];

    fn parse<const N: usize>(
        system: &[&str],
        variables: [&str; N],
    ) -> Vec<MultivariatePolynomial<N, F>> {
        system
            .iter()
            .map(|s| MultivariatePolynomial::parse(s, variables).unwrap())
            .collect()
    }

    /// The quotient algebra of a parsed system, with no limit that could fire.
    fn algebra_of<const N: usize>(
        system: &[&str],
        variables: [&str; N],
        order: MonomialOrder,
    ) -> (Vec<MultivariatePolynomial<N, F>>, QuotientAlgebra<N, F>) {
        let generators = parse(system, variables);
        let basis = f4(&generators, order).expect("within limits");
        let algebra =
            QuotientAlgebra::new(&basis, order, &FglmOptions::unbounded()).expect("finite");
        (generators, algebra)
    }

    /// `f(T_0, ..., T_{N-1})` applied to a coordinate vector.
    ///
    /// Each term's monomial is realized by applying one variable operator at a time, which is the
    /// only multiplication the algebra offers and the one FGLM uses.
    fn apply_polynomial<const N: usize>(
        algebra: &QuotientAlgebra<N, F>,
        f: &MultivariatePolynomial<N, F>,
        v: &[F],
    ) -> Vec<F> {
        let mut total = vec![F::zero(); algebra.dimension()];
        for (monomial, coefficient) in f.terms() {
            let mut image = v.to_vec();
            for (i, exponent) in monomial.exponents().iter().enumerate() {
                for _ in 0..*exponent {
                    image = algebra.multiply_by_variable(i, &image);
                }
            }
            for (slot, value) in total.iter_mut().zip(&image) {
                *slot += *coefficient * *value;
            }
        }
        total
    }

    /// The `j`-th unit coordinate vector, i.e. the class of the `j`-th standard monomial.
    fn unit<const N: usize>(algebra: &QuotientAlgebra<N, F>, j: usize) -> Vec<F> {
        let mut v = vec![F::zero(); algebra.dimension()];
        v[j] = F::one();
        v
    }

    /// The operators commute, on every basis vector, for every pair of variables.
    ///
    /// `T_i T_j = T_j T_i` holds because the quotient is a commutative ring, so a disagreement
    /// means the columns were built wrong rather than that the mathematics is subtle.
    #[test]
    fn test_the_operators_commute() {
        for order in ORDERS {
            for system in SYSTEMS {
                let (_, algebra) = algebra_of(system, ["x", "y"], order);
                for j in 0..algebra.dimension() {
                    let e = unit(&algebra, j);
                    let xy = algebra.multiply_by_variable(1, &algebra.multiply_by_variable(0, &e));
                    let yx = algebra.multiply_by_variable(0, &algebra.multiply_by_variable(1, &e));
                    assert_eq!(
                        xy, yx,
                        "T_x T_y and T_y T_x disagree on basis vector {} of {:?} under {:?}",
                        j, system, order
                    );
                }
            }
        }
    }

    /// Every input generator acts as the zero operator on the quotient.
    ///
    /// The defining property of `R/I`: a generator is in `I`, so it annihilates every class.
    /// Checked on every basis vector rather than only on the class of 1, which is the stronger
    /// statement and costs `D` applications instead of one.
    #[test]
    fn test_every_generator_acts_as_zero() {
        for order in ORDERS {
            for system in SYSTEMS {
                let (generators, algebra) = algebra_of(system, ["x", "y"], order);
                for f in &generators {
                    for j in 0..algebra.dimension() {
                        let image = apply_polynomial(&algebra, f, &unit(&algebra, j));
                        assert!(
                            image.iter().all(|value| value.is_zero()),
                            "{} does not annihilate basis vector {} of {:?} under {:?}: {:?}",
                            f,
                            j,
                            system,
                            order,
                            image
                        );
                    }
                }
            }
        }
    }

    /// Each operator column is the normal form of the product it stands for.
    ///
    /// Compared against a fresh `normal_form` call rather than against `coordinates`, which would
    /// use the same reduction and prove nothing.
    #[test]
    fn test_columns_agree_with_normal_forms() {
        for order in ORDERS {
            for system in SYSTEMS {
                let generators = parse(system, ["x", "y"]);
                let basis = f4(&generators, order).expect("within limits");
                let algebra =
                    QuotientAlgebra::new(&basis, order, &FglmOptions::unbounded()).expect("finite");

                for i in 0..2 {
                    for (j, monomial) in algebra.quotient_basis().monomials().iter().enumerate() {
                        let product = *monomial * Monomial::univariate(i, 1);
                        let expected = MultivariatePolynomial::new(&[(product, F::one())])
                            .normal_form(&basis, order);
                        let from_column = algebra.polynomial(&algebra.operator(i).column(j));
                        assert_eq!(
                            from_column, expected,
                            "column {} of T_{} in {:?} under {:?}",
                            j, i, system, order
                        );
                    }
                }
            }
        }
    }

    /// `coordinates` and `polynomial` are inverse, up to the reduction `coordinates` performs.
    #[test]
    fn test_coordinates_and_polynomial_are_inverse() {
        for order in ORDERS {
            for system in SYSTEMS {
                let generators = parse(system, ["x", "y"]);
                let basis = f4(&generators, order).expect("within limits");
                let algebra =
                    QuotientAlgebra::new(&basis, order, &FglmOptions::unbounded()).expect("finite");

                // Polynomials deliberately above the staircase, so the reduction does work.
                let probes = parse(
                    &["x^5 + y^5 + 1", "3*x^3*y^2 - 2*x + 7", "x*y + y", "1", "0"],
                    ["x", "y"],
                );
                for p in &probes {
                    let round_tripped = algebra.polynomial(&algebra.coordinates(p));
                    assert_eq!(
                        round_tripped,
                        p.normal_form(&basis, order),
                        "{} in {:?} under {:?}",
                        p,
                        system,
                        order
                    );
                }
            }
        }
    }

    /// The class of 1 is the first unit vector, and `one` agrees with `coordinates`.
    #[test]
    fn test_one_is_the_first_coordinate() {
        for order in ORDERS {
            for system in SYSTEMS {
                let (_, algebra) = algebra_of(system, ["x", "y"], order);
                let one: MultivariatePolynomial<2, F> = MultivariatePolynomial::one();
                assert_eq!(algebra.one(), algebra.coordinates(&one));
                assert_eq!(algebra.one(), unit(&algebra, 0));
            }
        }
    }

    /// The class of 1 generates the algebra: every standard monomial is reached from it.
    ///
    /// The property FGLM's frontier depends on — it computes a candidate monomial's vector by
    /// applying one operator to an already-known vector, never by reducing a polynomial.
    #[test]
    fn test_the_class_of_one_generates_the_algebra() {
        for order in ORDERS {
            for system in SYSTEMS {
                let (_, algebra) = algebra_of(system, ["x", "y"], order);
                for (j, monomial) in algebra.quotient_basis().monomials().iter().enumerate() {
                    let mut image = algebra.one();
                    for (i, exponent) in monomial.exponents().iter().enumerate() {
                        for _ in 0..*exponent {
                            image = algebra.multiply_by_variable(i, &image);
                        }
                    }
                    assert_eq!(
                        image,
                        unit(&algebra, j),
                        "{} is not reached from 1 in {:?} under {:?}",
                        monomial,
                        system,
                        order
                    );
                }
            }
        }
    }

    /// An operator applied to a dense vector is the weighted sum of its columns.
    ///
    /// Linearity stated concretely, on vectors with every coordinate nonzero. The larger systems
    /// are included because the two-variable ones have at most two columns contributing to any
    /// single coordinate, where katsura-6 has as many as 29.
    #[test]
    fn test_an_operator_is_the_weighted_sum_of_its_columns() {
        /// Distinct weights, so a dropped or duplicated column cannot cancel out.
        fn check<const N: usize>(
            name: &str,
            system: &[MultivariatePolynomial<N, F>],
            order: MonomialOrder,
        ) {
            let basis = f4(system, order).expect("within limits");
            let algebra =
                QuotientAlgebra::new(&basis, order, &FglmOptions::unbounded()).expect("finite");
            let d = algebra.dimension();

            for i in 0..N {
                let operator = algebra.operator(i);
                let weights: Vec<F> = (0..d).map(|j| F::new(j as u64 + 1)).collect();

                let mut expected = vec![F::zero(); d];
                for (j, weight) in weights.iter().enumerate() {
                    for (slot, value) in expected.iter_mut().zip(operator.column(j)) {
                        *slot += *weight * value;
                    }
                }

                assert_eq!(
                    operator.apply(&weights),
                    expected,
                    "T_{} is not the weighted column sum of {} under {:?}",
                    i,
                    name,
                    order
                );
            }
        }

        for order in ORDERS {
            for system in SYSTEMS {
                check(system[0], &parse(system, ["x", "y"]), order);
            }
        }

        let grevlex = MonomialOrder::GradedReverseLexicographic;
        check("katsura-5", &katsura::<5, F>(), grevlex);
        check("katsura-6", &katsura::<6, F>(), grevlex);
        check("cyclic-5", &cyclic::<5, F>(), grevlex);
    }

    /// The operators are linear maps.
    ///
    /// `T(a u + b v) = a T(u) + b T(v)`, on vectors dense enough that the two sides are not the
    /// same computation. A representation that accumulated wrongly would satisfy it on unit
    /// vectors and fail here.
    #[test]
    fn test_the_operators_are_linear() {
        for order in ORDERS {
            for system in SYSTEMS {
                let (_, algebra) = algebra_of(system, ["x", "y"], order);
                let d = algebra.dimension();
                if d == 0 {
                    continue;
                }

                let u: Vec<F> = (0..d).map(|j| F::new(2 * j as u64 + 1)).collect();
                let v: Vec<F> = (0..d).map(|j| F::new(7 * j as u64 + 3)).collect();
                let (a, b) = (F::new(5), F::new(11));

                for i in 0..2 {
                    let combination: Vec<F> =
                        u.iter().zip(&v).map(|(x, y)| a * *x + b * *y).collect();
                    let left = algebra.multiply_by_variable(i, &combination);

                    let image_u = algebra.multiply_by_variable(i, &u);
                    let image_v = algebra.multiply_by_variable(i, &v);
                    let right: Vec<F> = image_u
                        .iter()
                        .zip(&image_v)
                        .map(|(x, y)| a * *x + b * *y)
                        .collect();

                    assert_eq!(
                        left, right,
                        "T_{} is not linear in {:?} under {:?}",
                        i, system, order
                    );
                }
            }
        }
    }

    /// `<x^2, y^2>` has a nilpotent, non-diagonalizable `T_x`.
    ///
    /// The nonradical structure the milestone must preserve. `T_x` is nonzero and `T_x^2` is zero,
    /// so the operator has a nontrivial nilpotent part and no eigenbasis. Any later step that
    /// assumed diagonalizability, or that the quotient dimension counted distinct points, would be
    /// wrong here: there is one distinct zero and the dimension is four.
    #[test]
    fn test_a_nonradical_ideal_has_a_nilpotent_operator() {
        for order in ORDERS {
            let (_, algebra) = algebra_of(&["x^2", "y^2"], ["x", "y"], order);
            assert_eq!(algebra.dimension(), 4);

            let one = algebra.one();
            let x = algebra.multiply_by_variable(0, &one);
            assert!(
                x.iter().any(|value| !value.is_zero()),
                "T_x annihilates 1 under {:?}",
                order
            );
            let x_squared = algebra.multiply_by_variable(0, &x);
            assert!(
                x_squared.iter().all(|value| value.is_zero()),
                "T_x^2 is not zero under {:?}: {:?}",
                order,
                x_squared
            );
        }
    }

    /// The unit ideal has the zero algebra: dimension 0, and no coordinates to speak of.
    #[test]
    fn test_the_unit_ideal_has_the_zero_algebra() {
        for order in ORDERS {
            let (_, algebra) = algebra_of(&["x", "x - 1"], ["x", "y"], order);
            assert_eq!(algebra.dimension(), 0);
            assert!(algebra.one().is_empty());

            let probe: MultivariatePolynomial<2, F> =
                MultivariatePolynomial::parse("x^3 + y + 2", ["x", "y"]).unwrap();
            assert!(algebra.coordinates(&probe).is_empty());
            for i in 0..2 {
                assert_eq!(algebra.operator(i).dimension(), 0);
                assert_eq!(algebra.operator(i).stored_entries(), 0);
            }
        }
    }

    /// A positive-dimensional ideal is rejected before any operator is built.
    #[test]
    fn test_a_positive_dimensional_ideal_is_rejected() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = f4(&cyclic::<4, F>(), order).expect("within limits");
        assert_eq!(
            QuotientAlgebra::new(&basis, order, &FglmOptions::unbounded()).unwrap_err(),
            FglmError::PositiveDimensional
        );
    }

    /// Both column kinds occur, and the stored entries are fewer than a dense matrix's cells.
    ///
    /// The representation's premise, asserted where it is weakest and where it is strongest.
    /// `cargo run --release --example fglm_operators` measures it across the corpus, and the
    /// answer is not uniform: 25% to 42% of columns stay inside the staircase, and the stored
    /// entries run from **58% of dense on the katsura family down to 0.34% on planted-8**. So the
    /// sparse columns are worth 1.7x on one family and 290x on another, and at 16 bytes an entry
    /// against 8 bytes a dense cell they do not pay at all on katsura. That is a storage question
    /// for M18-3, not a correctness one; what is asserted here is only what holds everywhere.
    #[test]
    fn test_both_column_kinds_occur_and_beat_a_dense_matrix() {
        let order = MonomialOrder::GradedReverseLexicographic;

        // katsura-5 is the densest shape measured, at 59% of dense.
        let basis = f4(&katsura::<5, F>(), order).expect("within limits");
        let algebra =
            QuotientAlgebra::new(&basis, order, &FglmOptions::unbounded()).expect("finite");
        let d = algebra.dimension();
        assert_eq!(d, 16);

        let standard: usize = (0..5).map(|i| algebra.operator(i).standard_columns()).sum();
        let stored: usize = (0..5).map(|i| algebra.operator(i).stored_entries()).sum();
        assert!(standard > 0, "no column stayed inside the staircase");
        assert!(standard < 5 * d, "every column stayed inside the staircase");
        assert!(
            stored < 5 * d * d,
            "{} stored entries against {} dense cells is no saving",
            stored,
            5 * d * d
        );

        // planted-6 is the sparsest, where the saving is structural rather than marginal.
        let point: Vec<F> = [3u64, 5, 7, 11, 13, 17]
            .iter()
            .map(|v| F::new(*v))
            .collect();
        let basis = f4(&planted::<6, F>(&point), order).expect("within limits");
        let algebra =
            QuotientAlgebra::new(&basis, order, &FglmOptions::unbounded()).expect("finite");
        let d = algebra.dimension();
        let stored: usize = (0..6).map(|i| algebra.operator(i).stored_entries()).sum();
        assert_eq!(d, 64);
        assert!(
            stored * 20 < 6 * d * d,
            "{} stored entries against {} dense cells is under a twentieth",
            stored,
            6 * d * d
        );
    }

    /// An operator-entry limit below what the system needs is a structured error.
    #[test]
    fn test_the_operator_storage_limit_is_enforced() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = f4(&katsura::<5, F>(), order).expect("within limits");

        let mut options = FglmOptions::unbounded();
        options.max_operator_entries = 4;
        match QuotientAlgebra::new(&basis, order, &options) {
            Err(FglmError::OperatorStorageExceeded { entries, limit }) => {
                assert_eq!(limit, 4);
                assert!(entries > 4, "{} should be over the limit", entries);
            }
            other => panic!(
                "expected an operator storage error, got {:?}",
                other.is_ok()
            ),
        }
    }

    /// The quotient-dimension limit still applies when going through the algebra.
    #[test]
    fn test_the_quotient_dimension_limit_is_enforced() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = f4(&katsura::<5, F>(), order).expect("within limits");

        let mut options = FglmOptions::unbounded();
        options.max_quotient_dimension = 8;
        assert_eq!(
            QuotientAlgebra::new(&basis, order, &options).unwrap_err(),
            FglmError::QuotientDimensionExceeded { limit: 8 }
        );
    }

    /// Both construction strategies build the same algebra, value for value.
    ///
    /// The whole correctness argument for M18-1, and it is an equality of `QuotientAlgebra`s rather
    /// than of the lex bases they lead to: a wrong column that happens not to change the final
    /// basis would pass the weaker check and fail this one.
    #[test]
    fn test_the_construction_strategies_agree() {
        fn check<const N: usize>(
            name: &str,
            system: &[MultivariatePolynomial<N, F>],
            order: MonomialOrder,
        ) {
            let basis = f4(system, order).expect("within limits");
            let per_column = FglmOptions::unbounded()
                .with_operator_construction(OperatorConstruction::PerColumn);
            let deduplicated = FglmOptions::unbounded()
                .with_operator_construction(OperatorConstruction::DeduplicatedBorder);

            let (reference, reference_statistics) =
                QuotientAlgebra::new_with_statistics(&basis, order, &per_column).expect("finite");
            let (optimized, optimized_statistics) =
                QuotientAlgebra::new_with_statistics(&basis, order, &deduplicated).expect("finite");

            assert_eq!(
                reference, optimized,
                "{} under {:?}: the strategies disagree",
                name, order
            );
            // The classification is shared, so every border counter must match. Only the number
            // of reductions may differ, and it is checked separately.
            assert_eq!(
                reference_statistics.border.operator_columns,
                optimized_statistics.border.operator_columns
            );
            assert_eq!(
                reference_statistics.border.distinct_border_monomials,
                optimized_statistics.border.distinct_border_monomials
            );
            assert_eq!(
                reference.operator_entries(),
                optimized.operator_entries(),
                "{} under {:?}: the strategies store different amounts",
                name,
                order
            );
        }

        for order in ORDERS {
            for system in SYSTEMS {
                check(system[0], &parse(system, ["x", "y"]), order);
            }
            // Three variables, where a border monomial can be reached from three directions
            // rather than two.
            check("katsura-3", &katsura::<3, F>(), order);
            check(
                "x^2-y, y^2-z, z^2-1",
                &parse(&["x^2 - y", "y^2 - z", "z^2 - 1"], ["x", "y", "z"]),
                order,
            );
        }

        let grevlex = MonomialOrder::GradedReverseLexicographic;
        check("katsura-5", &katsura::<5, F>(), grevlex);
        check("katsura-6", &katsura::<6, F>(), grevlex);
        check("cyclic-5", &cyclic::<5, F>(), grevlex);
        let point: Vec<F> = [3u64, 5, 7, 11, 13, 17]
            .iter()
            .map(|v| F::new(*v))
            .collect();
        check("planted-6", &planted::<6, F>(&point), grevlex);
    }

    /// Deduplication reduces once per distinct border monomial, not once per column.
    ///
    /// The counters are what distinguish the two paths at runtime, so they are asserted rather than
    /// assumed — and the gap is asserted to be real on a system where the border repeats.
    #[test]
    fn test_deduplication_reduces_once_per_border_monomial() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = f4(&katsura::<6, F>(), order).expect("within limits");

        let (_, reference) = QuotientAlgebra::new_with_statistics(
            &basis,
            order,
            &FglmOptions::unbounded().with_operator_construction(OperatorConstruction::PerColumn),
        )
        .expect("finite");
        let (_, optimized) = QuotientAlgebra::new_with_statistics(
            &basis,
            order,
            &FglmOptions::unbounded()
                .with_operator_construction(OperatorConstruction::DeduplicatedBorder),
        )
        .expect("finite");

        assert_eq!(
            reference.border.normal_form_calls, reference.border.border_columns,
            "the reference path should reduce once per border column"
        );
        assert_eq!(
            optimized.border.normal_form_calls, optimized.border.distinct_border_monomials,
            "the deduplicated path should reduce once per distinct border monomial"
        );
        assert!(
            optimized.border.normal_form_calls < reference.border.normal_form_calls,
            "{} reductions is no saving against {}",
            optimized.border.normal_form_calls,
            reference.border.normal_form_calls
        );
    }

    /// Deduplication does not change what the operator-entry budget sees.
    ///
    /// Each column still owns its own vector, so a limit that fires under one strategy fires under
    /// the other at the same count. A strategy that quietly raised the storage would be a different
    /// trade than the one M18-1 claims to make.
    #[test]
    fn test_the_operator_budget_is_unchanged_by_deduplication() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let basis = f4(&katsura::<5, F>(), order).expect("within limits");

        for construction in [
            OperatorConstruction::PerColumn,
            OperatorConstruction::DeduplicatedBorder,
        ] {
            let mut options = FglmOptions::unbounded().with_operator_construction(construction);
            options.max_operator_entries = 4;
            match QuotientAlgebra::new(&basis, order, &options) {
                Err(FglmError::OperatorStorageExceeded { entries, limit }) => {
                    assert_eq!(limit, 4);
                    assert!(
                        entries > 4,
                        "{:?}: {} is not over the limit",
                        construction,
                        entries
                    );
                }
                other => panic!(
                    "{:?}: expected an operator storage error, got ok = {}",
                    construction,
                    other.is_ok()
                ),
            }
        }
    }

    /// A budget set to exactly what a system needs is enough for every strategy.
    ///
    /// The deduplicated path checks its shared vectors against the same budget before the columns
    /// exist, so the claim that this cannot reject a system the reference path accepts is checked
    /// at the tight boundary rather than argued. It holds because every distinct border monomial
    /// appears in at least one column, so the shared entries never exceed the operators'.
    #[test]
    fn test_a_budget_that_exactly_suffices_is_enough_for_every_strategy() {
        fn check<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
            let order = MonomialOrder::GradedReverseLexicographic;
            let basis = f4(system, order).expect("within limits");
            let needed = QuotientAlgebra::new(&basis, order, &FglmOptions::unbounded())
                .expect("finite")
                .operator_entries();

            for construction in [
                OperatorConstruction::PerColumn,
                OperatorConstruction::DeduplicatedBorder,
            ] {
                let mut options = FglmOptions::unbounded().with_operator_construction(construction);
                options.max_operator_entries = needed;
                assert!(
                    QuotientAlgebra::new(&basis, order, &options).is_ok(),
                    "{}: {:?} rejected a system at a budget of exactly its {} entries",
                    name,
                    construction,
                    needed
                );

                options.max_operator_entries = needed - 1;
                assert!(
                    QuotientAlgebra::new(&basis, order, &options).is_err(),
                    "{}: {:?} accepted a system one entry over its budget",
                    name,
                    construction
                );
            }
        }

        check("katsura-5", &katsura::<5, F>());
        check("katsura-6", &katsura::<6, F>());
        check("cyclic-5", &cyclic::<5, F>());
    }

    /// The named baseline is the M17 configuration, so a comparison against it stays meaningful.
    #[test]
    fn test_the_baseline_names_the_m17_strategies() {
        let baseline = FglmOptions::baseline();
        assert_eq!(
            baseline.operator_construction,
            OperatorConstruction::PerColumn
        );
        assert!(!baseline.measure_stages);
        assert_eq!(baseline.max_quotient_dimension, 4_096);
        assert_eq!(baseline.max_operator_entries, 20_000_000);
        assert_eq!(baseline.max_span_entries, 20_000_000);
    }

    /// The identities hold on a larger system, in more variables, with a planted solution.
    ///
    /// The two-variable cases above are exhaustive but small. This is the same commutation and
    /// vanishing check where `D` is 64 and `N` is 6, so the operators have real structure.
    #[test]
    fn test_the_identities_hold_on_a_planted_system() {
        let order = MonomialOrder::GradedReverseLexicographic;
        let point: Vec<F> = [3u64, 5, 7, 11, 13, 17]
            .iter()
            .map(|v| F::new(*v))
            .collect();
        let generators = planted::<6, F>(&point);
        let basis = f4(&generators, order).expect("within limits");
        let algebra =
            QuotientAlgebra::new(&basis, order, &FglmOptions::unbounded()).expect("finite");
        assert_eq!(algebra.dimension(), 64);

        for j in 0..algebra.dimension() {
            let e = unit(&algebra, j);
            for i in 0..6 {
                for k in 0..6 {
                    let ik = algebra.multiply_by_variable(k, &algebra.multiply_by_variable(i, &e));
                    let ki = algebra.multiply_by_variable(i, &algebra.multiply_by_variable(k, &e));
                    assert_eq!(ik, ki, "T_{} and T_{} disagree on vector {}", i, k, j);
                }
            }
            for f in &generators {
                assert!(
                    apply_polynomial(&algebra, f, &e)
                        .iter()
                        .all(|value| value.is_zero()),
                    "{} does not annihilate basis vector {}",
                    f,
                    j
                );
            }
        }
    }
}
