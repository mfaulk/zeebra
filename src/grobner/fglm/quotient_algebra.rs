//! `A = R/I` for a zero-dimensional ideal: coordinate vectors over the standard monomials, and
//! the operators that multiply by a variable.
//!
//! This is the whole of the algebra FGLM needs. Multiplication by an arbitrary element is not
//! provided, because the conversion never performs one: it starts from the class of 1 and reaches
//! every candidate monomial by applying one variable at a time.

use crate::{
    grobner::{
        f4::{MonicBasis, StageClock},
        fglm::{
            batch::{self, BatchOverflow, BorderBatchStatistics},
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

    /// What the batched border reduction did, or zeros under the scalar strategies.
    pub batches: BorderBatchStatistics,
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
                for monomial in index.monomials() {
                    shared.push(reduce_border_monomial(
                        *monomial,
                        basis,
                        order,
                        &quotient,
                        &mut statistics,
                        &mut clock,
                    ));
                }
                shared
            }
            OperatorConstruction::BatchedBorder => batched_border(
                index.monomials(),
                basis,
                order,
                &quotient,
                options,
                &mut statistics,
                &mut clock,
            )?,
        };

        // The shared vectors exist before any column does, so the entry budget is checked **as
        // they fill**. That is sound in the direction that matters: every distinct border monomial
        // appears in at least one column, so the shared entries never exceed the operators' own,
        // and the early check can never reject a system the per-column path would have accepted.
        // What it does change is the peak — up to twice the budget where the per-column path's is
        // exactly the budget, which is the honest cost of sharing.
        let mut shared_entries = 0usize;
        for column in &shared {
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
        }

        let mut operators = Vec::with_capacity(N);
        let mut entries = 0usize;
        let mut bytes = 0usize;

        for i in 0..N {
            let mut builder = OperatorBuilder::new(dimension, options.operator_storage);
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
                        OperatorConstruction::DeduplicatedBorder
                        | OperatorConstruction::BatchedBorder => shared[border].clone(),
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

                // Nonzeros, which is the older budget's unit. Counted from the column before it is
                // stored, so it does not depend on the representation chosen for it.
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

                // Bytes, which does depend on it: `push_reduced` reports what it stored, so the
                // budget is enforced on the allocation that happened rather than on a model of it.
                let stored = builder.push_reduced(column);
                bytes = bytes
                    .checked_add(stored)
                    .ok_or(FglmError::OperatorBytesExceeded {
                        bytes: usize::MAX,
                        limit: options.max_operator_bytes,
                    })?;
                if bytes > options.max_operator_bytes {
                    return Err(FglmError::OperatorBytesExceeded {
                        bytes,
                        limit: options.max_operator_bytes,
                    });
                }
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

    /// Field-element cells the `N` operators' columns allocate, zero or not.
    pub fn operator_cells(&self) -> usize {
        self.operators
            .iter()
            .map(MultiplicationOperator::stored_cells)
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

    /// Of the `N * D` columns, how many are held densely.
    pub fn dense_columns(&self) -> usize {
        self.operators
            .iter()
            .map(MultiplicationOperator::dense_columns)
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

/// Every distinct border monomial's normal form, computed in batches.
///
/// The targets are the border monomials in the index's own descending order, chunked by
/// [`BorderBatchSize`]. Each chunk builds its own symbolic closure and reduces its targets against
/// that closure's fixed reducer pivots — so the sharing is within a chunk, which is what the knob
/// trades.
///
/// A chunk that crosses a limit either fails or is reduced scalar-wise, per
/// [`BatchOverflow`]. **No target is ever dropped**, which is why the fallback reduces the chunk's
/// targets individually rather than returning fewer answers.
#[allow(clippy::too_many_arguments)]
fn batched_border<const N: usize, F: FiniteField>(
    targets: &[Monomial<N>],
    basis: &[MultivariatePolynomial<N, F>],
    order: MonomialOrder,
    quotient: &QuotientBasis<N>,
    options: &FglmOptions,
    statistics: &mut QuotientStatistics,
    clock: &mut StageClock,
) -> Result<Vec<Vec<(usize, F)>>, FglmError> {
    // Monic, with leading monomials precomputed, once for every batch. Zero elements are not valid
    // divisors and `MonicBasis::new` rejects them, so they are filtered rather than passed on.
    let nonzero: Vec<MultivariatePolynomial<N, F>> =
        basis.iter().filter(|p| !p.is_zero()).cloned().collect();
    let monic = MonicBasis::new(&nonzero, order);

    let chunk = options.border_batch.size.chunk(targets.len());
    let mut shared: Vec<Vec<(usize, F)>> = Vec::with_capacity(targets.len());

    for group in targets.chunks(chunk) {
        let outcome = batch::reduce_batch(
            group,
            &monic,
            order,
            &options.border_batch,
            options.measure_stages,
        );
        statistics.timings.border_symbolic += clock.lap();

        let remainders = match outcome {
            Ok((remainders, batch_statistics)) => {
                batch::accumulate(&mut statistics.batches, &batch_statistics);
                statistics.border.normal_form_calls += group.len();
                remainders
            }
            Err(e) => match options.border_batch.on_overflow {
                BatchOverflow::Fail => return Err(e),
                // The scalar path builds no closure, so it cannot cross these limits. Counted, so
                // a run that took it is not mistaken for one that did not need to.
                BatchOverflow::Scalar => {
                    statistics.batches.batches += 1;
                    statistics.batches.fallbacks += 1;
                    for monomial in group {
                        shared.push(reduce_border_monomial(
                            *monomial, basis, order, quotient, statistics, clock,
                        ));
                    }
                    continue;
                }
            },
        };

        for remainder in remainders {
            shared.push(coordinates_of_monomials(&remainder, quotient));
        }
        statistics.timings.column_assembly += clock.lap();
    }

    Ok(shared)
}

/// `(monomial, coefficient)` pairs as a coordinate vector, ascending by index.
///
/// # Panics
/// If a monomial is not standard. Unreachable for a batch's remainder — the reduction runs until no
/// reducible monomial is left — so reaching it means the closure was incomplete.
fn coordinates_of_monomials<const N: usize, F: FiniteField>(
    remainder: &[(Monomial<N>, F)],
    quotient: &QuotientBasis<N>,
) -> Vec<(usize, F)> {
    let mut entries: Vec<(usize, F)> = Vec::with_capacity(remainder.len());
    entries.extend(remainder.iter().map(|(monomial, coefficient)| {
        let index = quotient.index_of(monomial).unwrap_or_else(|| {
            panic!(
                "{} survived a batched reduction but is not a standard monomial",
                monomial
            )
        });
        (index, *coefficient)
    }));
    entries.sort_unstable_by_key(|(index, _)| *index);
    entries
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
    // `with_capacity` and not `collect`. A `HashMap`'s iterator is not `TrustedLen`, so `collect`
    // goes through the growth path, whose minimum non-zero allocation is **four** elements for this
    // element size — and a planted system's typical reduced column holds one. Measured, that slack
    // was 41% of planted-10's whole operator storage. `with_capacity` allocates exactly.
    let terms = normal_form.terms();
    let mut entries: Vec<(usize, F)> = Vec::with_capacity(terms.len());
    entries.extend(terms.iter().map(|(monomial, coefficient)| {
        let index = quotient.index_of(monomial).unwrap_or_else(|| {
            panic!(
                "{} survived reduction but is not a standard monomial",
                monomial
            )
        });
        (index, *coefficient)
    }));
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
            fglm::{FglmError, FglmOptions, OperatorConstruction, OperatorStorage},
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
            let (reference, reference_statistics) =
                QuotientAlgebra::new_with_statistics(&basis, order, &per_column).expect("finite");

            for construction in [
                OperatorConstruction::DeduplicatedBorder,
                OperatorConstruction::BatchedBorder,
            ] {
                let options = FglmOptions::unbounded().with_operator_construction(construction);
                let (optimized, optimized_statistics) =
                    QuotientAlgebra::new_with_statistics(&basis, order, &options).expect("finite");

                assert_eq!(
                    reference, optimized,
                    "{} under {:?}: {:?} disagrees with the reference",
                    name, order, construction
                );
                // The classification is shared, so every border counter must match. Only the
                // number of reductions may differ, and it is checked separately.
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
                    "{} under {:?}: {:?} stores a different amount",
                    name,
                    order,
                    construction
                );
            }
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
        assert_eq!(
            reference.border.normal_form_calls, reference.border.border_columns,
            "the reference path should reduce once per border column"
        );

        for construction in [
            OperatorConstruction::DeduplicatedBorder,
            OperatorConstruction::BatchedBorder,
        ] {
            let (_, optimized) = QuotientAlgebra::new_with_statistics(
                &basis,
                order,
                &FglmOptions::unbounded().with_operator_construction(construction),
            )
            .expect("finite");

            assert_eq!(
                optimized.border.normal_form_calls, optimized.border.distinct_border_monomials,
                "{:?} should reduce once per distinct border monomial",
                construction
            );
            assert!(
                optimized.border.normal_form_calls < reference.border.normal_form_calls,
                "{:?}: {} reductions is no saving against {}",
                construction,
                optimized.border.normal_form_calls,
                reference.border.normal_form_calls
            );
        }

        // The batched path does its reductions inside a closure, so it reports a batch and the
        // scalar paths do not.
        let (_, batched) = QuotientAlgebra::new_with_statistics(
            &basis,
            order,
            &FglmOptions::unbounded()
                .with_operator_construction(OperatorConstruction::BatchedBorder),
        )
        .expect("finite");
        assert_eq!(batched.batches.batches, 1, "one unbounded batch");
        assert_eq!(
            batched.batches.fallbacks, 0,
            "no batch should have fallen back"
        );
        assert!(
            batched.batches.reducer_rows > 0,
            "an empty closure reduces nothing"
        );
        assert!(batched.batches.columns > batched.batches.reducer_rows);
        assert_eq!(
            reference.batches.batches, 0,
            "the scalar path builds no batch"
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
            OperatorConstruction::BatchedBorder,
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

    /// Every storage strategy gives the same operators, observably.
    ///
    /// Not a `QuotientAlgebra` equality, and deliberately so: the representations differ, so the
    /// values differ, which is why they are compared through what a caller can see — every column,
    /// every application, and the nonzero count — rather than through the bytes they happen to
    /// occupy.
    #[test]
    fn test_the_storage_strategies_agree() {
        const STORAGES: [OperatorStorage; 3] = [
            OperatorStorage::Sparse,
            OperatorStorage::Adaptive,
            OperatorStorage::Dense,
        ];

        fn check<const N: usize>(
            name: &str,
            system: &[MultivariatePolynomial<N, F>],
            order: MonomialOrder,
        ) {
            let basis = f4(system, order).expect("within limits");
            let reference = QuotientAlgebra::new(
                &basis,
                order,
                &FglmOptions::unbounded().with_operator_storage(OperatorStorage::Sparse),
            )
            .expect("finite");
            let d = reference.dimension();

            // Weights with every coordinate nonzero and all distinct, so a dropped or duplicated
            // column cannot cancel out, plus the unit vectors the conversion actually uses.
            let dense: Vec<F> = (0..d).map(|j| F::new(j as u64 + 1)).collect();

            for storage in STORAGES {
                let algebra = QuotientAlgebra::new(
                    &basis,
                    order,
                    &FglmOptions::unbounded().with_operator_storage(storage),
                )
                .expect("finite");

                assert_eq!(
                    algebra.operator_entries(),
                    reference.operator_entries(),
                    "{} under {:?}: {:?} found a different number of nonzeros",
                    name,
                    order,
                    storage
                );

                for i in 0..N {
                    for j in 0..d {
                        assert_eq!(
                            algebra.operator(i).column(j),
                            reference.operator(i).column(j),
                            "{} under {:?}: {:?} disagrees on column {} of T_{}",
                            name,
                            order,
                            storage,
                            j,
                            i
                        );
                        assert_eq!(
                            algebra.multiply_by_variable(i, &unit(&algebra, j)),
                            reference.multiply_by_variable(i, &unit(&reference, j)),
                            "{} under {:?}: {:?} disagrees applying T_{} to e_{}",
                            name,
                            order,
                            storage,
                            i,
                            j
                        );
                    }
                    assert_eq!(
                        algebra.multiply_by_variable(i, &dense),
                        reference.multiply_by_variable(i, &dense),
                        "{} under {:?}: {:?} disagrees applying T_{} to a dense vector",
                        name,
                        order,
                        storage,
                        i
                    );
                }
            }
        }

        for order in ORDERS {
            for system in SYSTEMS {
                check(system[0], &parse(system, ["x", "y"]), order);
            }
            check("katsura-3", &katsura::<3, F>(), order);
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

    /// Adaptive storage is never larger than either extreme, and is strictly smaller than one of
    /// them on each family.
    ///
    /// The claim the strategy exists for. It is a per-column minimum, so being no worse than both
    /// is structural; being *better* than both on some instance is what makes it worth having, and
    /// that depends on the corpus containing columns on each side of the crossover.
    #[test]
    fn test_adaptive_storage_is_never_the_larger_choice() {
        fn bytes<const N: usize>(
            system: &[MultivariatePolynomial<N, F>],
            storage: OperatorStorage,
        ) -> usize {
            let order = MonomialOrder::GradedReverseLexicographic;
            let basis = f4(system, order).expect("within limits");
            QuotientAlgebra::new(
                &basis,
                order,
                &FglmOptions::unbounded().with_operator_storage(storage),
            )
            .expect("finite")
            .operator_bytes()
        }

        fn check<const N: usize>(name: &str, system: &[MultivariatePolynomial<N, F>]) {
            let sparse = bytes(system, OperatorStorage::Sparse);
            let adaptive = bytes(system, OperatorStorage::Adaptive);
            let dense = bytes(system, OperatorStorage::Dense);

            assert!(
                adaptive <= sparse,
                "{}: adaptive is {} bytes against sparse's {}",
                name,
                adaptive,
                sparse
            );
            assert!(
                adaptive <= dense,
                "{}: adaptive is {} bytes against dense's {}",
                name,
                adaptive,
                dense
            );
        }

        // katsura's reduced columns are dense enough that the dense form is smaller, so adaptive
        // must beat sparse there.
        let katsura_7 = katsura::<7, F>();
        check("katsura-7", &katsura_7);
        assert!(
            bytes(&katsura_7, OperatorStorage::Adaptive)
                < bytes(&katsura_7, OperatorStorage::Sparse),
            "katsura-7's columns are dense enough that adaptive should beat sparse"
        );

        // The planted family's columns hold about one entry each, so adaptive must beat dense and
        // must match sparse exactly — it should pick sparse for every column.
        let point: Vec<F> = (0..8).map(|i| F::new(2 * i as u64 + 3)).collect();
        let planted_8 = planted::<8, F>(&point);
        check("planted-8", &planted_8);
        assert_eq!(
            bytes(&planted_8, OperatorStorage::Adaptive),
            bytes(&planted_8, OperatorStorage::Sparse),
            "planted-8 has no column dense enough to be worth holding densely"
        );
        assert!(
            bytes(&planted_8, OperatorStorage::Adaptive)
                < bytes(&planted_8, OperatorStorage::Dense),
            "a dense planted-8 should be much larger"
        );

        check("cyclic-6", &cyclic::<6, F>());
    }

    /// The byte budget fires on bytes, where the entry budget would not have.
    ///
    /// The reason it is a second limit and not a redefinition of the first: under dense storage the
    /// same nonzeros occupy `D` cells, so a budget written in entries cannot see the difference.
    #[test]
    fn test_the_operator_byte_budget_is_enforced() {
        let order = MonomialOrder::GradedReverseLexicographic;
        // planted-6, not katsura: katsura's columns are 81% full, so holding them densely is
        // *smaller* and there would be no overshoot for a budget to catch. A planted column holds
        // about one entry of 64, which is where the dense form is ruinous.
        let point: Vec<F> = [3u64, 5, 7, 11, 13, 17]
            .iter()
            .map(|v| F::new(*v))
            .collect();
        let basis = f4(&planted::<6, F>(&point), order).expect("within limits");

        let sparse = FglmOptions::unbounded().with_operator_storage(OperatorStorage::Sparse);
        let dense = FglmOptions::unbounded().with_operator_storage(OperatorStorage::Dense);
        let sparse_bytes = QuotientAlgebra::new(&basis, order, &sparse)
            .expect("finite")
            .operator_bytes();
        let dense_bytes = QuotientAlgebra::new(&basis, order, &dense)
            .expect("finite")
            .operator_bytes();
        assert!(
            dense_bytes > sparse_bytes,
            "planted-6 held densely should be larger: {} against {}",
            dense_bytes,
            sparse_bytes
        );

        // A budget that the sparse form fits inside and the dense form does not, with the *entry*
        // budget unbounded throughout — so what fires can only be the byte budget.
        let mut limited = dense;
        limited.max_operator_bytes = sparse_bytes;
        match QuotientAlgebra::new(&basis, order, &limited) {
            Err(FglmError::OperatorBytesExceeded { bytes, limit }) => {
                assert_eq!(limit, sparse_bytes);
                assert!(bytes > limit, "{} should be over {}", bytes, limit);
            }
            other => panic!("expected a byte-budget error, got ok = {}", other.is_ok()),
        }

        let mut generous = limited;
        generous.operator_storage = OperatorStorage::Sparse;
        assert!(
            QuotientAlgebra::new(&basis, order, &generous).is_ok(),
            "the sparse form should fit inside a budget set from its own size"
        );
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
                OperatorConstruction::BatchedBorder,
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
