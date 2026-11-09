//! Crossbred's admissible parameters, and its total work counted across every guess.
//!
//! Crossbred (Joux and Vitse, eprint 2017/372) solves `m` quadratics in `n` variables over `F_q`
//! in two steps. **Preprocessing** reduces submatrices of the degree-`D` Macaulay matrix to obtain
//! `r` polynomials of degree at most `d` in a chosen `k` variables; **enumeration** then runs over
//! all `q^(n-k)` assignments of the other `n - k` variables, each one leaving a system that
//! linearizes at degree `d`. The parameters are the triple `(D, d, k)`.
//!
//! Two things make this module worth having rather than a formula in a document.
//!
//! **Not every `(D, d, k)` works, and which ones do is a series coefficient.** Preprocessing has
//! to produce at least as many useful polynomials as the specialized system is short of
//! determining, or the consistency test in the inner loop cannot be done by linearization at all.
//! That is condition i) below, and it is what [`CrossbredSeries`] computes.
//!
//! **The cost is the sum over all guesses.** A reduced system that looks small is irrelevant if
//! the guess count is `q^(n-k)` with `n - k = 51`, which is what the `n = 74` Fukuoka record
//! actually ran. [`WorkAccounting`] therefore reports the guess count as its own term and never
//! folds it into a per-guess figure. Outer hybridation — fixing `h` further variables and running
//! the whole algorithm `q^h` times — moves work between the two terms and **leaves the total guess
//! count at `q^(n-k)` exactly**, which is the arithmetic that makes the point.
//!
//! # One series family, three papers
//!
//! `T` and `S` here are the same objects as, respectively, `T_{k,q}` in the proof of Theorem 2 of
//! eprint 2024/758 and the series `S_{k,q}` that 2024/758 Definition 5 i) tests — which is in turn
//! Joux and Vitse's bivariate series generalized to `q > 2` by Bellini et al. (eprint 2022/708
//! eq. 6), and `G^k_{m,n}` and `J^k_{m,n}` of eprint 2026/360 Propositions 3 and 4. They differ by
//! exactly the corank of the specialized Macaulay matrix, `S = T - corank(Mac_d(F|b))`, which is
//! what makes condition i) readable: **`T` is what preprocessing produces and `S` is the surplus
//! over what linearization needs.** The identity is asserted in
//! `tests::test_the_surplus_is_the_polynomials_minus_what_linearization_needs` rather than
//! assumed, because it is the one statement tying the three papers' notations together.
//!
//! # These are predictions
//!
//! Every coefficient here is exact arithmetic over a *model*: the input sequence is assumed
//! `q`-semi-regular and its specializations semi-regular for almost every `b` (2024/758 §3,
//! 2026/360 Definition 4). 2024/758 §5 measured the model holding for 99.99% of sampled sequences
//! at the sizes they could sample. Nothing here may gate a correctness decision, and
//! `docs/research/crossbred.md` records which published figures it reproduces.

use crate::grobner::hilbert::HilbertError;

/// Strassen's exponent, which is what the crossbred literature's `omega` is in practice.
///
/// 2026/360 §1 uses `omega ~= 2.8074`; 2022/708 §5.2 computes its tables at `omega = 2.81`. The
/// difference is below the resolution of anything this module is used for, but the figure is a
/// parameter rather than a constant so that a table can say which one it used.
pub const DEFAULT_LINEAR_ALGEBRA_EXPONENT: f64 = 2.8074;

/// Machine word in bits, the block size of the block Lanczos step in 2026/360 Proposition 7.
pub const DEFAULT_WORD_BITS: u32 = 64;

/// Why a crossbred count could not be produced.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CrossbredError {
    /// A coefficient left `i128`. The series are exponential in the degree and the counts are
    /// exact, so the only honest response to overflow is to refuse.
    Overflow,

    /// `kept` is not strictly between zero and `variables`, or `kept_degree` is not below
    /// `degree`, or the field order is below two.
    BadParameters,
}

impl std::fmt::Display for CrossbredError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CrossbredError::Overflow => write!(formatter, "a crossbred count exceeded i128"),
            CrossbredError::BadParameters => {
                write!(
                    formatter,
                    "parameters outside 0 < k < n, 1 <= d < D, q >= 2"
                )
            }
        }
    }
}

impl std::error::Error for CrossbredError {}

impl From<HilbertError> for CrossbredError {
    fn from(_: HilbertError) -> Self {
        CrossbredError::Overflow
    }
}

/// `left * right`, truncated above degree `up_to`.
fn multiply(left: &[i128], right: &[i128], up_to: usize) -> Result<Vec<i128>, CrossbredError> {
    let mut out = vec![0i128; up_to + 1];
    for (i, a) in left.iter().enumerate() {
        if *a == 0 || i > up_to {
            continue;
        }
        for (j, b) in right.iter().enumerate() {
            if i + j > up_to {
                break;
            }
            let term = a.checked_mul(*b).ok_or(CrossbredError::Overflow)?;
            out[i + j] = out[i + j]
                .checked_add(term)
                .ok_or(CrossbredError::Overflow)?;
        }
    }
    Ok(out)
}

/// `1 / series`, truncated above degree `up_to`. Requires a unit constant term.
fn invert(series: &[i128], up_to: usize) -> Result<Vec<i128>, CrossbredError> {
    debug_assert_eq!(series.first().copied(), Some(1), "a unit constant term");
    let mut out = vec![0i128; up_to + 1];
    out[0] = 1;
    for index in 1..=up_to {
        let mut total = 0i128;
        for j in 1..=index {
            let coefficient = series.get(j).copied().unwrap_or(0);
            if coefficient == 0 {
                continue;
            }
            let term = coefficient
                .checked_mul(out[index - j])
                .ok_or(CrossbredError::Overflow)?;
            total = total.checked_add(term).ok_or(CrossbredError::Overflow)?;
        }
        out[index] = -total;
    }
    Ok(out)
}

/// `series^exponent`, truncated above degree `up_to`.
fn power(series: &[i128], exponent: usize, up_to: usize) -> Result<Vec<i128>, CrossbredError> {
    let mut result = vec![0i128; up_to + 1];
    result[0] = 1;
    let mut base = series.to_vec();
    let mut remaining = exponent;
    while remaining > 0 {
        if remaining & 1 == 1 {
            result = multiply(&result, &base, up_to)?;
        }
        remaining >>= 1;
        if remaining > 0 {
            base = multiply(&base, &base, up_to)?;
        }
    }
    Ok(result)
}

/// `1 - z^power`, as a series.
fn one_minus_power(exponent: u64, up_to: usize) -> Vec<i128> {
    let mut series = vec![0i128; up_to + 1];
    series[0] = 1;
    if (exponent as usize) <= up_to {
        series[exponent as usize] = -1;
    }
    series
}

/// `1 / (1 - z)`, as a series.
fn geometric(up_to: usize) -> Vec<i128> {
    vec![1i128; up_to + 1]
}

/// `M_{n,q}(z) = ((1 - z^q) / (1 - z))^n` — monomials in `n` variables with every exponent below
/// `q`, by total degree.
///
/// This is the monomial count the field equations leave: over `F_2` it is `(1 + z)^n`, so
/// `[z^t] = binomial(n, t)` and not `binomial(n + t - 1, t)`. Every column count below is taken
/// from this series rather than from a binomial coefficient, which is what makes the `q = 2` and
/// `q > 2` paths one path.
///
/// # Errors
/// [`CrossbredError::Overflow`].
pub fn monomial_series(
    variables: usize,
    order: u64,
    up_to: u64,
) -> Result<Vec<i128>, CrossbredError> {
    if order < 2 {
        return Err(CrossbredError::BadParameters);
    }
    let up_to = up_to as usize;
    let quotient = multiply(&one_minus_power(order, up_to), &geometric(up_to), up_to)?;
    power(&quotient, variables, up_to)
}

/// `H_{n,m,q}(z) = M_{n,q}(z) ((1 - z^2) / (1 - z^{2q}))^m` — the Hilbert series of a
/// `q`-semi-regular sequence of `m` quadratics in `n` variables.
///
/// 2024/758 Theorem 1 statement 4, which is the definition of `q`-semi-regularity there; over
/// `F_2` it is Bardet's `(1 + z)^n / (1 + z^2)^m`. The expansion is returned **untruncated**, so
/// its first non-positive coefficient is visible — that index is the model's degree of regularity
/// and [`first_non_positive`] is how to get it.
///
/// # Errors
/// [`CrossbredError::Overflow`].
pub fn semiregular_series(
    variables: usize,
    equations: usize,
    order: u64,
    up_to: u64,
) -> Result<Vec<i128>, CrossbredError> {
    let limit = up_to as usize;
    let frobenius = multiply(
        &one_minus_power(2, limit),
        &invert(&one_minus_power(2 * order, limit), limit)?,
        limit,
    )?;
    let monomials = monomial_series(variables, order, up_to)?;
    multiply(&monomials, &power(&frobenius, equations, limit)?, limit)
}

/// The first degree at which `series` is non-positive, if the expansion reached one.
///
/// For [`semiregular_series`] this is the model's **degree of regularity**: the first degree at
/// which a `q`-semi-regular sequence is predicted to leave no residue classes. `None` says the
/// expansion was too short, not that the degree does not exist — an underdetermined system
/// (`m < n`) genuinely has none, and reads as `None` at every length.
pub fn first_non_positive(series: &[i128]) -> Option<u64> {
    series
        .iter()
        .position(|coefficient| *coefficient <= 0)
        .map(|index| index as u64)
}

/// Monomials of degree at most `degree` in `variables` variables over `F_q`.
///
/// What linearization at degree `d` has to determine, and the `N` of 2026/360 eq. (9) — which over
/// `F_2` is `sum_{i<=d} binomial(k, i)` and not `binomial(k + d, d)`.
///
/// # Errors
/// [`CrossbredError::Overflow`].
pub fn monomials_up_to(variables: usize, order: u64, degree: u64) -> Result<i128, CrossbredError> {
    let series = monomial_series(variables, order, degree)?;
    let mut total = 0i128;
    for coefficient in series.iter() {
        total = total
            .checked_add(*coefficient)
            .ok_or(CrossbredError::Overflow)?;
    }
    Ok(total)
}

/// What a triple `(D, d, k)` would give, and whether it can work at all.
///
/// Both conditions are necessary and neither implies the other (2024/758 §4, Example 2). Condition
/// i) is the one Joux and Vitse stated; condition ii) is 2024/758's addition, and is what makes
/// the admissible set a *proper* subset of what the earlier literature predicted.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Admissibility {
    /// `[w^D z^d] T` — the polynomials preprocessing is predicted to produce, i.e. the corank of
    /// the column submatrix whose kernel preprocessing computes.
    pub polynomials: i128,

    /// `corank(Mac_d(F|b))` — how far the specialized system is from being determined by
    /// linearization at degree `d`, and so how many of those polynomials have to be useful.
    pub needed: i128,

    /// `[w^D z^d] S = polynomials - needed`. Condition i) is this being non-negative.
    pub surplus: i128,

    /// Condition i) of 2024/758 Definition 5: `[w^D z^d] S_{k,q}(w, z) >= 0`.
    pub condition_i: bool,

    /// Condition ii) of 2024/758 Definition 5: `[z^D] (H_{k,m,q}(z) / (1 - z))_+ = 0`, i.e. `D` is
    /// large enough that the *specialized* system's own degree-`D` Macaulay matrix would contain
    /// the constant 1 — without which an inconsistent `F|b` cannot be detected as inconsistent.
    pub condition_ii: bool,

    /// `D < D_reg(F)`, required by 2024/758 Theorem 2 and 2026/360 Definition 7. `None` for the
    /// degree of regularity reads as satisfied: an underdetermined system has no such degree.
    pub degree_below_regularity: bool,

    /// `d < d_reg(F|b)`, the same requirement for the specialized system.
    pub kept_degree_below_regularity: bool,
}

impl Admissibility {
    /// Both conditions of 2024/758 Definition 5, with the two degree bounds its Theorem 2 assumes.
    ///
    /// 2026/360 Definition 7 calls the weaker notion — condition i) and the degree bounds, without
    /// condition ii) — *potentially admissible*, and conjectures the two coincide. They do not in
    /// general: 2024/758 Example 2 exhibits `q = 16, n = m = 8, k = 7, D = 7, d = 4` satisfying
    /// i) and failing ii).
    pub fn admissible(&self) -> bool {
        self.potentially_admissible() && self.condition_ii
    }

    /// Condition i) and the two degree bounds — 2026/360 Definition 7.
    pub fn potentially_admissible(&self) -> bool {
        self.condition_i && self.degree_below_regularity && self.kept_degree_below_regularity
    }
}

/// The bivariate series that decide admissibility, expanded once for one `(q, n, m, k)`.
///
/// Expanding is the expensive part — the series are products of `m`-th powers — so a sweep over
/// `(D, d)` builds this once and reads coefficients off it.
#[derive(Clone, Debug)]
pub struct CrossbredSeries {
    /// Field order.
    order: u64,

    /// Equation count.
    equations: usize,

    /// Variables kept linear-ish: the `k` of `(D, d, k)`.
    kept: usize,

    /// `[w^i z^j] T`, indexed `[i][j]`.
    polynomials: Vec<Vec<i128>>,

    /// `[w^i z^j] S`, indexed `[i][j]`.
    surplus: Vec<Vec<i128>>,

    /// `(H_{k,m,q}(z) / (1 - z))_+`, whose vanishing at `z^D` is condition ii).
    specialized_cumulative: Vec<i128>,

    /// `D_reg` of the full system under the model.
    degree_of_regularity: Option<u64>,

    /// `d_reg` of the specialized system under the model.
    kept_degree_of_regularity: Option<u64>,
}

impl CrossbredSeries {
    /// Expand to total degree `max_degree` in each variable.
    ///
    /// # Errors
    /// [`CrossbredError::BadParameters`] unless `0 < kept < variables` and `order >= 2`;
    /// [`CrossbredError::Overflow`].
    pub fn new(
        order: u64,
        variables: usize,
        equations: usize,
        kept: usize,
        max_degree: u64,
    ) -> Result<Self, CrossbredError> {
        if order < 2 || kept == 0 || kept >= variables {
            return Err(CrossbredError::BadParameters);
        }
        let limit = max_degree as usize;

        // The three univariate pieces. `H(wz)` is `H` on the diagonal, so it is built from the
        // univariate expansion rather than multiplied out bivariately.
        let kept_h = semiregular_series(kept, equations, order, max_degree)?;
        let whole_h = semiregular_series(variables, equations, order, max_degree)?;
        let free_m = monomial_series(variables - kept, order, max_degree)?;

        // numerator(T) = H_{k,m,q}(wz) M_{n-k,q}(w) - H_{n,m,q}(w)
        // numerator(S) = numerator(T) - H_{k,m,q}(z)
        let mut t_numerator = vec![vec![0i128; limit + 1]; limit + 1];
        for (diagonal, kept_coefficient) in kept_h.iter().enumerate() {
            if *kept_coefficient == 0 {
                continue;
            }
            for (shift, free_coefficient) in free_m.iter().enumerate() {
                if diagonal + shift > limit || *free_coefficient == 0 {
                    continue;
                }
                let term = kept_coefficient
                    .checked_mul(*free_coefficient)
                    .ok_or(CrossbredError::Overflow)?;
                let cell = &mut t_numerator[diagonal + shift][diagonal];
                *cell = cell.checked_add(term).ok_or(CrossbredError::Overflow)?;
            }
        }
        for (degree, coefficient) in whole_h.iter().enumerate() {
            let cell = &mut t_numerator[degree][0];
            *cell = cell
                .checked_sub(*coefficient)
                .ok_or(CrossbredError::Overflow)?;
        }
        let mut s_numerator = t_numerator.clone();
        for (degree, coefficient) in kept_h.iter().enumerate() {
            let cell = &mut s_numerator[0][degree];
            *cell = cell
                .checked_sub(*coefficient)
                .ok_or(CrossbredError::Overflow)?;
        }

        Ok(Self {
            order,
            equations,
            kept,
            polynomials: divide_by_one_minus_both(&t_numerator)?,
            surplus: divide_by_one_minus_both(&s_numerator)?,
            specialized_cumulative: positive_truncation(&multiply(
                &kept_h,
                &geometric(limit),
                limit,
            )?),
            degree_of_regularity: first_non_positive(&whole_h),
            kept_degree_of_regularity: first_non_positive(&kept_h),
        })
    }

    /// `[w^D z^d] T` — the polynomials preprocessing is predicted to produce.
    pub fn polynomials(&self, degree: u64, kept_degree: u64) -> i128 {
        self.coefficient(&self.polynomials, degree, kept_degree)
    }

    /// `[w^D z^d] S` — the surplus of those over what linearization needs.
    pub fn surplus(&self, degree: u64, kept_degree: u64) -> i128 {
        self.coefficient(&self.surplus, degree, kept_degree)
    }

    /// `corank(Mac_d(F|b))` — what linearization is short by, under the model.
    pub fn specialized_corank(&self, degree: u64, kept_degree: u64) -> i128 {
        self.polynomials(degree, kept_degree) - self.surplus(degree, kept_degree)
    }

    /// The model's `D_reg` for the whole system, or `None` if the expansion stayed positive.
    pub fn degree_of_regularity(&self) -> Option<u64> {
        self.degree_of_regularity
    }

    /// The model's `d_reg` for the specialized system.
    pub fn kept_degree_of_regularity(&self) -> Option<u64> {
        self.kept_degree_of_regularity
    }

    /// Both admissibility conditions at one `(D, d)`.
    pub fn admissibility(&self, degree: u64, kept_degree: u64) -> Admissibility {
        let polynomials = self.polynomials(degree, kept_degree);
        let surplus = self.surplus(degree, kept_degree);
        Admissibility {
            polynomials,
            needed: polynomials - surplus,
            surplus,
            condition_i: surplus >= 0,
            condition_ii: self
                .specialized_cumulative
                .get(degree as usize)
                .copied()
                .unwrap_or(0)
                == 0,
            degree_below_regularity: self
                .degree_of_regularity
                .is_none_or(|regular| degree < regular),
            kept_degree_below_regularity: self
                .kept_degree_of_regularity
                .is_none_or(|regular| kept_degree < regular),
        }
    }

    /// The field order these series were built for.
    pub fn order(&self) -> u64 {
        self.order
    }

    /// The equation count these series were built for.
    pub fn equations(&self) -> usize {
        self.equations
    }

    /// The `k` these series were built for.
    pub fn kept(&self) -> usize {
        self.kept
    }

    /// Zero outside the expansion, which is the honest reading: the coefficient was not computed
    /// and the caller asked beyond `max_degree`.
    fn coefficient(&self, table: &[Vec<i128>], degree: u64, kept_degree: u64) -> i128 {
        table
            .get(degree as usize)
            .and_then(|row| row.get(kept_degree as usize))
            .copied()
            .unwrap_or(0)
    }
}

/// Divide a bivariate series by `(1 - w)(1 - z)` — a prefix sum in each variable.
fn divide_by_one_minus_both(table: &[Vec<i128>]) -> Result<Vec<Vec<i128>>, CrossbredError> {
    let mut out = table.to_vec();
    for row in out.iter_mut() {
        let mut running = 0i128;
        for cell in row.iter_mut() {
            running = running.checked_add(*cell).ok_or(CrossbredError::Overflow)?;
            *cell = running;
        }
    }
    for index in 1..out.len() {
        let (above, below) = out.split_at_mut(index);
        let previous = above.last().expect("index >= 1");
        for (cell, earlier) in below[0].iter_mut().zip(previous.iter()) {
            *cell = cell.checked_add(*earlier).ok_or(CrossbredError::Overflow)?;
        }
    }
    Ok(out)
}

/// The series with everything from its first non-positive coefficient onward set to zero.
///
/// The `[.]_+` of the literature. 2024/758 applies it to `H_{k,m,q}(z) / (1 - z)` — to the
/// quotient, not to `H` before dividing: cumulating a truncated `H` is non-decreasing from `1`, so
/// it can never satisfy a condition that asks for zero.
fn positive_truncation(series: &[i128]) -> Vec<i128> {
    let cut = first_non_positive(series);
    series
        .iter()
        .enumerate()
        .map(|(index, coefficient)| match cut {
            Some(first) if index as u64 >= first => 0,
            _ => *coefficient,
        })
        .collect()
}

/// The shape of the matrix preprocessing works on.
///
/// `rows` is the identity 2026/360 states just before its Corollary 2:
/// `#Rows(Mac^k) = g^k_{D,d} + #Cols(M^k)`, with `g^k_{D,d}` the polynomial count. It matters
/// because the cokernel cost is driven by **rows**, which is the correction 2026/360 §2.3 makes to
/// the published estimators — they all use the column count.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PreprocessingShape {
    /// Columns of `M^k_{<=D,>=d,m}`: monomials of total degree at most `D` whose degree in the
    /// kept variables exceeds `d`.
    pub columns: i128,

    /// Columns of `Mac^k_{<=D,>=d,m}`: every monomial of total degree at most `D`. The quantity
    /// 2026/360 Table 6 tabulates, which is **not** [`PreprocessingShape::columns`].
    pub macaulay_columns: i128,

    /// Rows of `Mac^k_{<=D,>=d,m}` counted **without** the General and Frobenius criteria:
    /// `m` times the multipliers `u` with `deg(u) <= D - 2` and `deg_k(u) >= d - 1`.
    ///
    /// An upper bound on the row count, and the one 2026/360 §6 states its MQOM figures in — it
    /// says so: "number of rows (without applying the General and the Frobenius criteria)".
    /// Keeping it separate from [`PreprocessingShape::rows`] is what lets both be checked against
    /// that table.
    pub naive_rows: i128,

    /// Rows of `Mac^k_{<=D,>=d,m}`, as `polynomials + columns`.
    pub rows: i128,

    /// Polynomials the original algorithm generates — the corank, `[w^D z^d] T`.
    pub polynomials: i128,

    /// Polynomials the *improved* preprocessing of 2026/360 Corollary 1 needs instead:
    /// `N + n - k - 1`, with `N` the monomials of degree at most `d` in the kept variables. For
    /// MQOM level I this is `2^7.3` against the original's `2^60.34`, which is the largest single
    /// reduction in the whole accounting.
    pub minimal_polynomials: i128,
}

/// The shape of the preprocessing matrices at `(D, d, k)`.
///
/// # Errors
/// [`CrossbredError::BadParameters`], [`CrossbredError::Overflow`].
pub fn preprocessing_shape(
    series: &CrossbredSeries,
    variables: usize,
    degree: u64,
    kept_degree: u64,
) -> Result<PreprocessingShape, CrossbredError> {
    let kept = series.kept();
    if kept_degree >= degree || kept >= variables || kept == 0 {
        return Err(CrossbredError::BadParameters);
    }
    let order = series.order();
    let kept_monomials = monomial_series(kept, order, degree)?;
    let free_monomials = monomial_series(variables - kept, order, degree)?;

    let mut columns = 0i128;
    let mut macaulay_columns = 0i128;
    let mut multipliers = 0i128;
    for total in 0..=degree as usize {
        for in_kept in 0..=total {
            let product = kept_monomials[in_kept]
                .checked_mul(free_monomials[total - in_kept])
                .ok_or(CrossbredError::Overflow)?;
            macaulay_columns = macaulay_columns
                .checked_add(product)
                .ok_or(CrossbredError::Overflow)?;
            if in_kept > kept_degree as usize {
                columns = columns
                    .checked_add(product)
                    .ok_or(CrossbredError::Overflow)?;
            }
            // A row is `u * f_i` with `deg(u) <= D - 2` and `deg_k(u) >= d - 1`.
            if total + 2 <= degree as usize && in_kept + 1 >= kept_degree as usize {
                multipliers = multipliers
                    .checked_add(product)
                    .ok_or(CrossbredError::Overflow)?;
            }
        }
    }

    let polynomials = series.polynomials(degree, kept_degree);
    let needed = monomials_up_to(kept, order, kept_degree)?;
    Ok(PreprocessingShape {
        columns,
        macaulay_columns,
        naive_rows: multipliers
            .checked_mul(series.equations() as i128)
            .ok_or(CrossbredError::Overflow)?,
        rows: polynomials
            .checked_add(columns)
            .ok_or(CrossbredError::Overflow)?,
        polynomials,
        minimal_polynomials: needed + (variables - kept) as i128 - 1,
    })
}

/// How a work accounting prices linear algebra.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct WorkOptions {
    /// Linear-algebra exponent.
    pub exponent: f64,

    /// Machine word in bits, the block Lanczos block size.
    pub word_bits: u32,

    /// Outer hybridation: fix `h` further variables and run everything `q^h` times.
    pub hybridation: usize,

    /// Whether preprocessing generates only the `N + n - k - 1` polynomials of 2026/360
    /// Corollary 1 rather than the full corank.
    pub improved_preprocessing: bool,
}

impl Default for WorkOptions {
    fn default() -> Self {
        Self {
            exponent: DEFAULT_LINEAR_ALGEBRA_EXPONENT,
            word_bits: DEFAULT_WORD_BITS,
            hybridation: 0,
            improved_preprocessing: false,
        }
    }
}

/// Total work at `(D, d, k)`, as base-two logarithms of operation counts.
///
/// Logarithms because the interesting instances are past `2^128` operations and the point of the
/// accounting is the exponent. Every term is separate, and in particular
/// [`WorkAccounting::log2_guesses`] is never folded into the enumeration figure — the warning this
/// module exists to honour is that a cheap specialized solve times `2^51` guesses is not cheap.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct WorkAccounting {
    /// `T_1`: generating `Mac^k`, including the General and Frobenius criteria — the term every
    /// published estimator omits (2026/360 §2.3, Proposition 6).
    pub log2_matrix_generation: f64,

    /// `T_2`: the cokernel by block Lanczos, `(r / W) c^2 max(n^2 / W, 1)` (2026/360
    /// Proposition 7). Driven by the **row** count `c`.
    pub log2_cokernel: f64,

    /// `T_3`: multiplying the cokernel basis back through `Mac^k`, `r n^2 c` (Proposition 8).
    pub log2_new_polynomials: f64,

    /// The three preprocessing terms, times `q^h` because hybridation repeats preprocessing.
    pub log2_preprocessing: f64,

    /// `(n - k) log2 q` — the guess count, independent of `h`.
    pub log2_guesses: f64,

    /// One specialized consistency test: `m N^omega`, with `N` the degree-`d` monomials in the
    /// kept variables.
    pub log2_per_guess: f64,

    /// `log2_guesses + log2_per_guess`.
    pub log2_enumeration: f64,

    /// Preprocessing plus enumeration.
    pub log2_total: f64,
}

/// `log2(2^a + 2^b)`, computed without leaving the exponent domain.
fn log2_sum(a: f64, b: f64) -> f64 {
    let (high, low) = if a >= b { (a, b) } else { (b, a) };
    if !high.is_finite() {
        return high;
    }
    high + (1.0 + (low - high).exp2()).log2()
}

/// The total work accounting at `(D, d, k)`.
///
/// Reads the terms off 2026/360 §4 — `T_1` from Proposition 6, `T_2` from Proposition 7, `T_3`
/// from Proposition 8 — and prices enumeration as 2022/708's `m q^(n-k) N^omega`, with `N` taken
/// from [`monomials_up_to`] so the field equations are counted. With `hybridation = h` the
/// preprocessing terms are computed on `variables - h` variables and multiplied by `q^h`, which
/// leaves `log2_guesses` at `(n - k) log2 q` regardless of `h`.
///
/// # Errors
/// [`CrossbredError::BadParameters`], [`CrossbredError::Overflow`].
pub fn work(
    order: u64,
    variables: usize,
    equations: usize,
    kept: usize,
    degree: u64,
    kept_degree: u64,
    options: WorkOptions,
) -> Result<WorkAccounting, CrossbredError> {
    if kept_degree >= degree || kept_degree == 0 || kept == 0 || options.hybridation >= variables {
        return Err(CrossbredError::BadParameters);
    }
    let inner = variables - options.hybridation;
    if kept >= inner {
        return Err(CrossbredError::BadParameters);
    }
    let order_bits = (order as f64).log2();
    let inner_bits = (inner as f64).log2();
    let series = CrossbredSeries::new(order, inner, equations, kept, degree)?;
    let shape = preprocessing_shape(&series, inner, degree, kept_degree)?;

    let monomials = monomial_series(inner, order, degree)?;
    let mut generation = f64::NEG_INFINITY;
    let mut criteria = f64::NEG_INFINITY;
    for total in 2..=degree as usize {
        let count = monomials[total];
        if count <= 0 {
            continue;
        }
        let bits = (count as f64).log2();
        if total < degree as usize {
            generation = log2_sum(generation, bits);
        }
        if total + 2 <= degree as usize {
            criteria = log2_sum(criteria, options.exponent * bits);
        }
    }
    let log2_matrix_generation = log2_sum(3.0 * inner_bits + generation, criteria);

    let retained = if options.improved_preprocessing {
        shape.minimal_polynomials
    } else {
        shape.polynomials
    };
    if retained <= 0 {
        return Err(CrossbredError::BadParameters);
    }
    let retained_bits = (retained as f64).log2();
    let rows_bits = (shape.rows.max(1) as f64).log2();
    let word_bits = (options.word_bits as f64).log2();
    let blocked = (2.0 * inner_bits - word_bits).max(0.0);
    let log2_cokernel = retained_bits - word_bits + 2.0 * rows_bits + blocked;
    let log2_new_polynomials = retained_bits + 2.0 * inner_bits + rows_bits;

    let log2_preprocessing = options.hybridation as f64 * order_bits
        + log2_sum(
            log2_sum(log2_matrix_generation, log2_cokernel),
            log2_new_polynomials,
        );

    let log2_guesses = (variables - kept) as f64 * order_bits;
    let linearized = monomials_up_to(kept, order, kept_degree)?;
    let log2_per_guess =
        (equations as f64).log2() + options.exponent * (linearized.max(1) as f64).log2();
    let log2_enumeration = log2_guesses + log2_per_guess;

    Ok(WorkAccounting {
        log2_matrix_generation,
        log2_cokernel,
        log2_new_polynomials,
        log2_preprocessing,
        log2_guesses,
        log2_per_guess,
        log2_enumeration,
        log2_total: log2_sum(log2_preprocessing, log2_enumeration),
    })
}

/// The cheapest admissible `(D, d)` for a given `k`, by total work.
///
/// Returns `None` when no `(D, d)` within `max_degree` is admissible at this `k`, which is the
/// common case for small `k` and is the reason a parameter search is a search.
///
/// # Errors
/// [`CrossbredError::Overflow`].
pub fn best_parameters(
    order: u64,
    variables: usize,
    equations: usize,
    kept: usize,
    max_degree: u64,
    options: WorkOptions,
) -> Result<Option<(u64, u64, WorkAccounting)>, CrossbredError> {
    let inner = variables
        .checked_sub(options.hybridation)
        .ok_or(CrossbredError::BadParameters)?;
    if kept == 0 || kept >= inner {
        return Ok(None);
    }
    let series = CrossbredSeries::new(order, inner, equations, kept, max_degree)?;
    let mut best: Option<(u64, u64, WorkAccounting)> = None;
    for degree in 2..=max_degree {
        for kept_degree in 1..degree {
            if !series.admissibility(degree, kept_degree).admissible() {
                continue;
            }
            let accounting = work(
                order,
                variables,
                equations,
                kept,
                degree,
                kept_degree,
                options,
            )?;
            if best
                .as_ref()
                .is_none_or(|(_, _, found)| accounting.log2_total < found.log2_total)
            {
                best = Some((degree, kept_degree, accounting));
            }
        }
    }
    Ok(best)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// That the monomial count is the one the field equations leave, not the polynomial ring's.
    #[test]
    fn test_monomials_respect_the_field_equations() {
        // Over F_2 a monomial is a subset of the variables.
        let series = monomial_series(10, 2, 4).expect("expands");
        assert_eq!(series[0], 1);
        assert_eq!(series[1], 10);
        assert_eq!(series[2], 45);
        assert_eq!(series[3], 120);
        // Over F_31 and below degree 31 nothing is cut, so it is the ordinary count.
        let large = monomial_series(5, 31, 3).expect("expands");
        assert_eq!(large[2], 15, "monomials of degree 2 in 5 variables");
        assert_eq!(large[3], 35, "monomials of degree 3 in 5 variables");
    }

    /// That the semiregular series over F_2 is Bardet's `(1 + z)^n / (1 + z^2)^m`.
    #[test]
    fn test_the_boolean_semiregular_series_is_bardets() {
        let series = semiregular_series(20, 40, 2, 6).expect("expands");
        // (1+z)^20/(1+z^2)^40 expanded by hand in low degrees: 1, 20, 190 - 40, ...
        assert_eq!(series[0], 1);
        assert_eq!(series[1], 20);
        assert_eq!(series[2], 190 - 40);
        assert_eq!(
            first_non_positive(&series),
            Some(4),
            "m = 2n at n = 20 is predicted to finish at degree 4"
        );
    }

    /// That the five parameter sets of Joux-Vitse's own Table 1 reproduce, column for column.
    ///
    /// `N` and `R` are their closed forms for the column count and the independent-row count, and
    /// their "Exp. num of polys" is `R - N`. The series must land on the same integer, which is
    /// the check that this module's `T` is the quantity their table reports.
    #[test]
    fn test_the_joux_vitse_table_one_reproduces() {
        // n, m, k, D, published columns, published rank, published polynomial count
        let published = [
            (35usize, 35usize, 9usize, 3u64, 1056i128, 1260i128, 204i128),
            (35, 70, 14, 3, 2366, 2520, 154),
            (41, 41, 11, 4, 31075, 34481, 3406),
            (41, 82, 15, 3, 3290, 3444, 154),
            // n = 74, m = 148 with outer hybridation h = 12, so 62 variables remain.
            (62, 148, 23, 4, 277288, 278166, 878),
        ];
        for (n, m, k, d, columns, rank, polynomials) in published {
            let series = CrossbredSeries::new(2, n, m, k, d).expect("expands");
            let shape = preprocessing_shape(&series, n, d, 1).expect("a shape");
            assert_eq!(
                shape.columns, columns,
                "columns of M^k at n = {}, m = {}, k = {}, D = {}",
                n, m, k, d
            );
            assert_eq!(
                shape.polynomials, polynomials,
                "polynomial count at n = {}, m = {}, k = {}, D = {}",
                n, m, k, d
            );
            // Their R - N is the same integer, which is why the rank column is checked here too.
            assert_eq!(
                rank - columns,
                polynomials,
                "Joux-Vitse's own R - N at n = {}",
                n
            );
        }
    }

    /// That the polynomial counts of 2026/360 Tables 1 and 2 reproduce.
    ///
    /// Nine parameter sets at `d` from 1 to 3, measured by its authors with a Magma implementation
    /// of the preprocessing step. Covers `d > 1`, which Joux-Vitse's Table 1 does not.
    #[test]
    fn test_the_vidal_delaplace_ionica_polynomial_counts_reproduce() {
        // m, n, k, D, d, published r
        let published = [
            (63usize, 30usize, 17usize, 4u64, 1u64, 2930i128),
            (59, 28, 17, 4, 1, 2591),
            (49, 23, 18, 4, 1, 1944),
            (69, 33, 22, 4, 2, 5945),
            (63, 30, 20, 4, 2, 6429),
            (43, 20, 14, 3, 2, 238),
            (47, 22, 14, 3, 2, 294),
            (79, 38, 27, 4, 3, 7019),
            (83, 40, 27, 4, 3, 8097),
            // Table 2, which varies k at fixed (m, n) and so checks the k dependence.
            (49, 23, 16, 4, 1, 2568),
            (49, 23, 15, 4, 1, 3003),
        ];
        for (m, n, k, degree, kept_degree, expected) in published {
            let series = CrossbredSeries::new(2, n, m, k, degree).expect("expands");
            assert_eq!(
                series.polynomials(degree, kept_degree),
                expected,
                "r at m = {}, n = {}, k = {}, D = {}, d = {}",
                m,
                n,
                k,
                degree,
                kept_degree
            );
        }
    }

    /// That 2026/360's worked Example 2 reproduces, including the degree that is not yet enough.
    ///
    /// The example's point is that `D = 3` generates polynomials and still fails — two, where
    /// linearization at `d = 1` needs `k + 1 = 14` — while `D = 4` gives 3230. A module that only
    /// got the admissible case right would miss exactly the failure the parameter search exists
    /// to detect.
    #[test]
    fn test_the_vidal_example_two_reproduces_including_the_inadmissible_degree() {
        let series = CrossbredSeries::new(2, 21, 45, 13, 4).expect("expands");
        assert_eq!(series.polynomials(3, 1), 2, "g^k_(3,1) of Example 2");
        assert_eq!(series.polynomials(4, 1), 3230, "g^k_(4,1) of Example 2");
        let short = series.admissibility(3, 1);
        assert_eq!(short.needed, 14, "d = 1 needs k + 1 = 14 polynomials");
        assert!(!short.condition_i, "two polynomials is not fourteen");
        assert!(series.admissibility(4, 1).condition_i, "3230 is");
    }

    /// That the surplus is the polynomial count minus what linearization needs.
    ///
    /// The one statement tying the three papers' series together: 2024/758's `S` is its `T` minus
    /// `corank(Mac_d(F|b))`, so condition i) reads as a surplus being non-negative. Checked over a
    /// range of `(D, d)` and over both a binary and a non-binary field, since the identity is the
    /// reason `T` is computed at all.
    #[test]
    fn test_the_surplus_is_the_polynomials_minus_what_linearization_needs() {
        for (order, n, m, k) in [(2u64, 30usize, 63usize, 17usize), (31, 20, 40, 12)] {
            let series = CrossbredSeries::new(order, n, m, k, 8).expect("expands");
            let kept_h = semiregular_series(k, m, order, 8).expect("expands");
            let cumulative: Vec<i128> = kept_h
                .iter()
                .scan(0i128, |running, coefficient| {
                    *running += *coefficient;
                    Some(*running)
                })
                .collect();
            for degree in 2..=8u64 {
                for kept_degree in 1..degree {
                    assert_eq!(
                        series.specialized_corank(degree, kept_degree),
                        cumulative[kept_degree as usize],
                        "T - S must be corank(Mac_d(F|b)) at q = {}, D = {}, d = {}",
                        order,
                        degree,
                        kept_degree
                    );
                }
            }
        }
    }

    /// That the two admissibility conditions are independent, on 2024/758's own example.
    ///
    /// `q = 16, n = m = 8, k = 7, D = 7, d = 4` satisfies condition i) and fails condition ii) —
    /// which is the whole reason condition ii) exists, and the case that makes the admissible set
    /// a proper subset of what the earlier literature predicted. At `d = 2` condition i) fails.
    #[test]
    fn test_condition_two_is_not_implied_by_condition_one() {
        let series = CrossbredSeries::new(16, 8, 8, 7, 9).expect("expands");
        let wide = series.admissibility(7, 4);
        assert!(wide.condition_i, "2024/758 Example 2: i) holds at d = 4");
        assert!(!wide.condition_ii, "2024/758 Example 2: ii) fails at D = 7");
        assert!(!wide.admissible(), "so the triple is not admissible");
        let narrow = series.admissibility(7, 2);
        assert!(!narrow.condition_i, "2024/758 Example 2: i) fails at d = 2");
    }

    /// That condition ii) is satisfied by every published binary parameter choice, so condition i)
    /// is the binding one over F_2.
    ///
    /// 2024/758's narrowing bites at large `q`; its own counterexamples are `q = 16` and its
    /// Table 1 is `q = 16` and `q = 256`. Over F_2 with `m >= 2k` the specialized system is so
    /// overdetermined that its cumulative series goes non-positive at degree 3, so any `D >= 3`
    /// passes. Pinned because it is the reason the Fukuoka records remain admissible under the
    /// stricter definition.
    #[test]
    fn test_the_binary_records_remain_admissible_under_the_stricter_definition() {
        // q, n, m, k, D, d — Joux-Vitse's record row and Bellini et al.'s Table 1 type I rows.
        let published = [
            (62usize, 148usize, 23usize, 4u64, 1u64),
            (64, 148, 22, 4, 1),
            (74, 148, 28, 6, 1),
        ];
        for (n, m, k, degree, kept_degree) in published {
            let series = CrossbredSeries::new(2, n, m, k, degree).expect("expands");
            let verdict = series.admissibility(degree, kept_degree);
            assert!(
                verdict.condition_ii,
                "condition ii) at n = {}, m = {}, k = {}, D = {}",
                n, m, k, degree
            );
            assert!(
                verdict.admissible(),
                "admissible at n = {}, m = {}, k = {}, D = {}: {:?}",
                n,
                m,
                k,
                degree,
                verdict
            );
        }
    }

    /// That the row count is the polynomial count plus the column count.
    #[test]
    fn test_rows_are_polynomials_plus_columns() {
        let series = CrossbredSeries::new(2, 30, 63, 17, 4).expect("expands");
        let shape = preprocessing_shape(&series, 30, 4, 1).expect("a shape");
        assert_eq!(shape.rows, shape.polynomials + shape.columns);
        assert!(
            shape.naive_rows > shape.rows,
            "the criteria-free row count is an upper bound: {} against {}",
            shape.naive_rows,
            shape.rows
        );
        assert_eq!(
            shape.minimal_polynomials,
            18 + 30 - 17 - 1,
            "N + n - k - 1 with N = 1 + k"
        );
    }

    /// That the guess count is `q^(n-k)` whatever the hybridation, which is the accounting point.
    ///
    /// `(D, d, k) = (6, 1, 28)` is Bellini et al.'s optimal triple for Fukuoka type I at `n = 74`,
    /// and is admissible with and without hybridation — so the two accountings are comparable and
    /// the guess term can be checked to be the same `2^46` in both.
    #[test]
    fn test_hybridation_moves_work_without_changing_the_guess_count() {
        let bare = work(
            2,
            74,
            148,
            28,
            6,
            1,
            WorkOptions {
                hybridation: 0,
                ..WorkOptions::default()
            },
        )
        .expect("an accounting");
        let hybrid = work(
            2,
            74,
            148,
            28,
            6,
            1,
            WorkOptions {
                hybridation: 10,
                ..WorkOptions::default()
            },
        )
        .expect("an accounting");
        assert_eq!(bare.log2_guesses, 46.0, "n - k = 46 bits of guesses");
        assert_eq!(
            bare.log2_guesses, hybrid.log2_guesses,
            "hybridation partitions the guess space, it does not shrink it"
        );
        // And it does not pay for itself in work. The cokernel term is `(r / W) c^2`, and
        // dropping ten variables raises `r` by as much as it lowers `c^2` here — 75.67 against
        // 75.64 bits — so the whole `2^h` repetition is paid and nothing is recovered. Outer
        // hybridation buys parallelism across machines and, as
        // `test_an_inadmissible_triple_has_no_work_figure` shows, admissibility at a smaller `D`;
        // it does not buy total work. Joux and Vitse say as much — "the main interest of this
        // outer hybridation is to allow an easy parallelization" — and this is that sentence as
        // arithmetic.
        assert!(
            hybrid.log2_preprocessing > bare.log2_preprocessing,
            "the q^h repetition factor should dominate: {} against {}",
            hybrid.log2_preprocessing,
            bare.log2_preprocessing
        );
        assert!(
            (hybrid.log2_preprocessing - bare.log2_preprocessing - 10.0).abs() < 0.1,
            "the whole q^h factor is paid, so the gap should be h bits; computed {}",
            hybrid.log2_preprocessing - bare.log2_preprocessing
        );
    }

    /// That a triple whose series coefficient is negative is refused rather than priced.
    ///
    /// `k = 23, D = 4` on the full 74 variables generates **no** polynomials — the coefficient is
    /// negative — which is exactly why Joux and Vitse ran that `k` with `h = 12` outer
    /// hybridation, on 62 variables, where it generates 878. A work figure for the unhybridized
    /// triple would be a number for a run that cannot happen.
    #[test]
    fn test_an_inadmissible_triple_has_no_work_figure() {
        let series = CrossbredSeries::new(2, 74, 148, 23, 4).expect("expands");
        assert!(
            series.polynomials(4, 1) < 0,
            "no polynomials at k = 23, D = 4 on all 74 variables"
        );
        assert_eq!(
            work(2, 74, 148, 23, 4, 1, WorkOptions::default()).unwrap_err(),
            CrossbredError::BadParameters
        );
    }

    /// That 2026/360's MQOM level I figures reproduce, and that they are criteria-free counts.
    ///
    /// Table 6 publishes four numbers at `(D, d, k) = (13, 1, 31)` for 160 quadratics in 160
    /// variables with `h = 3`, so on 157. Three are plain counting — `log2(#Row) = 61.91`,
    /// `log2(#Col) = 61.69`, and `log2(r) = 60.34` as rows minus the columns of `M^k` — and the
    /// fourth, `log2(t) = 7.3`, is the Corollary 1 reduction. All four land.
    ///
    /// **The published `r` is the criteria-free count, not the corank.** The series of their own
    /// Proposition 3 — which reproduces their Table 1 exactly, see the test above — gives `2^52.4`
    /// at these parameters, nearly `2^8` fewer polynomials, because it accounts for the
    /// dependencies the General and Frobenius criteria remove. Their §6 says it is counting
    /// without the criteria, so the two figures are consistent as stated; what matters here is
    /// that a harness must not mix them.
    #[test]
    fn test_the_mqom_level_one_figures_reproduce_as_criteria_free_counts() {
        let series = CrossbredSeries::new(2, 157, 160, 31, 13).expect("expands");
        let shape = preprocessing_shape(&series, 157, 13, 1).expect("a shape");
        let published = [
            ("log2(#Row)", (shape.naive_rows as f64).log2(), 61.91),
            ("log2(#Col)", (shape.macaulay_columns as f64).log2(), 61.69),
            (
                "log2(r)",
                ((shape.naive_rows - shape.columns) as f64).log2(),
                60.34,
            ),
            ("log2(t)", (shape.minimal_polynomials as f64).log2(), 7.3),
        ];
        for (label, computed, expected) in published {
            assert!(
                (computed - expected).abs() < 0.05,
                "2026/360 Table 6 reports {} = {}, computed {}",
                label,
                expected,
                computed
            );
        }
        let corank = (shape.polynomials as f64).log2();
        assert!(
            (corank - 52.42).abs() < 0.05,
            "the Proposition 3 corank at the same parameters is 2^52.42, computed 2^{}",
            corank
        );
    }

    /// That a parameter search finds the Fukuoka type I record's own degree admissible.
    #[test]
    fn test_the_parameter_search_finds_an_admissible_triple_for_the_record() {
        let found = best_parameters(
            2,
            74,
            148,
            23,
            6,
            WorkOptions {
                hybridation: 12,
                ..WorkOptions::default()
            },
        )
        .expect("a search")
        .expect("an admissible triple at k = 23");
        assert_eq!(
            (found.0, found.1),
            (4, 1),
            "D = 4, d = 1 is what Joux-Vitse ran at k = 23"
        );
    }

    /// That bad parameters are refused rather than silently producing a figure.
    #[test]
    fn test_parameters_outside_the_domain_are_refused() {
        assert_eq!(
            CrossbredSeries::new(2, 10, 20, 10, 4).unwrap_err(),
            CrossbredError::BadParameters,
            "k = n leaves nothing to enumerate"
        );
        assert_eq!(
            CrossbredSeries::new(1, 10, 20, 5, 4).unwrap_err(),
            CrossbredError::BadParameters,
            "there is no field of order one"
        );
        assert_eq!(
            work(2, 10, 20, 5, 2, 2, WorkOptions::default()).unwrap_err(),
            CrossbredError::BadParameters,
            "d must be below D"
        );
    }
}
