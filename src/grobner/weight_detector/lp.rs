//! Exact feasibility for homogeneous weight constraints: two-phase simplex over `i128` rationals,
//! Bland's rule, every operation checked.
//!
//! The constraints are homogeneous (`a·w > 0` or `a·w = 0`), so scaling normalises them to
//! `a·w ≥ 1`, `a·w = 0` and `w ≥ 1`, and an optimum of `Σ w` scales to the smallest integer vector
//! on its ray. An overflow or the pivot cap is an [`WeightSearchError`], never a wrong answer: the caller
//! verifies any weight vector it uses against the polynomials themselves.

use std::cmp::Ordering;

/// One homogeneous constraint on the weight vector.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Constraint {
    /// `a·w > 0`.
    Positive(Vec<i64>),
    /// `a·w = 0`.
    Zero(Vec<i64>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WeightSearchError {
    /// An intermediate rational left `i128`, or the integer weights left `u32`.
    Overflow,
    /// More pivots than the cap: Bland's rule terminates, but not necessarily soon.
    PivotLimit,
}

/// What one solve cost.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct LpWork {
    pub pivots: usize,
}

const MAX_PIVOTS: usize = 20_000;

/// The positive integer weight vector of least `Σ w` (up to scaling) satisfying `constraints`, or
/// `Ok(None)` if none exists.
pub(crate) fn smallest_weights(
    constraints: &[Constraint],
    variables: usize,
    work: &mut LpWork,
) -> Result<Option<Vec<u32>>, WeightSearchError> {
    let y = match solve(constraints, variables, work)? {
        Some(y) => y,
        None => return Ok(None),
    };
    // x = 1 + y, then clear denominators and divide out the common factor.
    let x: Vec<Q> = y
        .iter()
        .map(|v| v.add(Q::ONE).ok_or(WeightSearchError::Overflow))
        .collect::<Result<_, _>>()?;
    let mut scale: i128 = 1;
    for v in &x {
        scale = lcm(scale, v.d).ok_or(WeightSearchError::Overflow)?;
    }
    let mut ints: Vec<i128> = x
        .iter()
        .map(|v| {
            (scale / v.d)
                .checked_mul(v.n)
                .ok_or(WeightSearchError::Overflow)
        })
        .collect::<Result<_, _>>()?;
    let g = ints.iter().fold(0, |g, &v| gcd(g, v));
    for v in &mut ints {
        *v /= g;
    }
    ints.iter()
        .map(|&v| u32::try_from(v).map_err(|_| WeightSearchError::Overflow))
        .collect::<Result<Vec<_>, _>>()
        .map(Some)
}

/// `y ≥ 0` minimising `Σ y`, where `w = 1 + y`.
fn solve(
    constraints: &[Constraint],
    n: usize,
    work: &mut LpWork,
) -> Result<Option<Vec<Q>>, WeightSearchError> {
    let slacks = constraints
        .iter()
        .filter(|c| matches!(c, Constraint::Positive(_)))
        .count();
    let rows = constraints.len();
    // Columns: y (n), slacks, artificials (rows), then the right-hand side.
    let artificial = n + slacks;
    let rhs = artificial + rows;
    let mut t = vec![vec![Q::ZERO; rhs + 1]; rows];
    let mut slack = n;
    for (r, c) in constraints.iter().enumerate() {
        let (a, positive) = match c {
            Constraint::Positive(a) => (a, true),
            Constraint::Zero(a) => (a, false),
        };
        assert_eq!(a.len(), n, "constraint arity");
        let row_sum: i128 = a.iter().map(|&v| v as i128).sum();
        let mut b = -row_sum;
        for (j, &v) in a.iter().enumerate() {
            t[r][j] = Q::int(v as i128);
        }
        if positive {
            b += 1;
            t[r][slack] = Q::int(-1);
            slack += 1;
        }
        t[r][rhs] = Q::int(b);
        if b < 0 {
            for v in &mut t[r][..rhs + 1] {
                *v = v.neg();
            }
        }
        t[r][artificial + r] = Q::ONE;
    }
    let mut basis: Vec<usize> = (artificial..artificial + rows).collect();

    // Phase 1: minimise the artificials.
    let phase1: Vec<Q> = (0..rhs)
        .map(|j| if j >= artificial { Q::ONE } else { Q::ZERO })
        .collect();
    simplex(&mut t, &mut basis, &phase1, rhs, rhs, work)?;
    for (r, &b) in basis.iter().enumerate() {
        if b >= artificial && t[r][rhs].n != 0 {
            return Ok(None);
        }
    }

    // Drive the zero-level artificials out of the basis, dropping rows that are redundant.
    let mut r = 0;
    while r < basis.len() {
        if basis[r] < artificial {
            r += 1;
            continue;
        }
        match (0..artificial).find(|&j| t[r][j].n != 0) {
            Some(j) => {
                pivot(&mut t, &mut basis, r, j, rhs)?;
                work.pivots += 1;
                r += 1;
            }
            None => {
                t.remove(r);
                basis.remove(r);
            }
        }
    }

    // Phase 2: minimise Σ y with the artificials barred from entering.
    let phase2: Vec<Q> = (0..rhs)
        .map(|j| if j < n { Q::ONE } else { Q::ZERO })
        .collect();
    simplex(&mut t, &mut basis, &phase2, artificial, rhs, work)?;

    let mut y = vec![Q::ZERO; n];
    for (r, &b) in basis.iter().enumerate() {
        if b < n {
            y[b] = t[r][rhs];
        }
    }
    Ok(Some(y))
}

/// Minimise `cost` from a feasible basis; columns `>= allowed` may not enter.
fn simplex(
    t: &mut [Vec<Q>],
    basis: &mut [usize],
    cost: &[Q],
    allowed: usize,
    rhs: usize,
    work: &mut LpWork,
) -> Result<(), WeightSearchError> {
    loop {
        if work.pivots >= MAX_PIVOTS {
            return Err(WeightSearchError::PivotLimit);
        }
        // Bland: the lowest-index column with a negative reduced cost enters.
        let mut entering = None;
        for j in 0..allowed {
            if basis.contains(&j) {
                continue;
            }
            let mut reduced = cost[j];
            for (r, &b) in basis.iter().enumerate() {
                if cost[b].n != 0 && t[r][j].n != 0 {
                    reduced = reduced
                        .sub(cost[b].mul(t[r][j]).ok_or(WeightSearchError::Overflow)?)
                        .ok_or(WeightSearchError::Overflow)?;
                }
            }
            if reduced.n < 0 {
                entering = Some(j);
                break;
            }
        }
        let Some(j) = entering else {
            return Ok(());
        };
        // Ratio test, ties to the lowest basic index.
        let mut leaving: Option<(usize, Q)> = None;
        for r in 0..t.len() {
            if t[r][j].n <= 0 {
                continue;
            }
            let ratio = t[r][rhs].div(t[r][j]).ok_or(WeightSearchError::Overflow)?;
            let better = match &leaving {
                None => true,
                Some((best, q)) => match ratio.cmp(q) {
                    Ordering::Less => true,
                    Ordering::Equal => basis[r] < basis[*best],
                    Ordering::Greater => false,
                },
            };
            if better {
                leaving = Some((r, ratio));
            }
        }
        // Both objectives are bounded below by zero, so an unbounded column cannot exist.
        let (r, _) = leaving.expect("bounded objective");
        pivot(t, basis, r, j, rhs)?;
        work.pivots += 1;
    }
}

fn pivot(
    t: &mut [Vec<Q>],
    basis: &mut [usize],
    r: usize,
    j: usize,
    rhs: usize,
) -> Result<(), WeightSearchError> {
    let p = t[r][j];
    for v in &mut t[r][..rhs + 1] {
        *v = v.div(p).ok_or(WeightSearchError::Overflow)?;
    }
    let pivot_row = t[r].clone();
    for (i, row) in t.iter_mut().enumerate() {
        if i == r || row[j].n == 0 {
            continue;
        }
        let f = row[j];
        for (v, &pv) in row.iter_mut().zip(&pivot_row) {
            if pv.n != 0 {
                *v = v
                    .sub(f.mul(pv).ok_or(WeightSearchError::Overflow)?)
                    .ok_or(WeightSearchError::Overflow)?;
            }
        }
    }
    basis[r] = j;
    Ok(())
}

/// A rational with positive denominator, in lowest terms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Q {
    n: i128,
    d: i128,
}

impl Q {
    const ZERO: Q = Q { n: 0, d: 1 };
    const ONE: Q = Q { n: 1, d: 1 };

    fn int(n: i128) -> Q {
        Q { n, d: 1 }
    }

    fn new(n: i128, d: i128) -> Option<Q> {
        if d == 0 {
            return None;
        }
        let g = gcd(n, d);
        let (mut n, mut d) = (n / g, d / g);
        if d < 0 {
            n = n.checked_neg()?;
            d = d.checked_neg()?;
        }
        Some(Q { n, d })
    }

    fn neg(self) -> Q {
        Q {
            n: -self.n,
            d: self.d,
        }
    }

    fn add(self, o: Q) -> Option<Q> {
        let g = gcd(self.d, o.d);
        let (a, b) = (self.d / g, o.d / g);
        Q::new(
            self.n.checked_mul(b)?.checked_add(o.n.checked_mul(a)?)?,
            self.d.checked_mul(b)?,
        )
    }

    fn sub(self, o: Q) -> Option<Q> {
        self.add(o.neg())
    }

    fn mul(self, o: Q) -> Option<Q> {
        let g1 = gcd(self.n, o.d);
        let g2 = gcd(o.n, self.d);
        Q::new(
            (self.n / g1).checked_mul(o.n / g2)?,
            (self.d / g2).checked_mul(o.d / g1)?,
        )
    }

    fn div(self, o: Q) -> Option<Q> {
        if o.n == 0 {
            return None;
        }
        self.mul(Q::new(o.d, o.n)?)
    }
}

impl PartialOrd for Q {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Q {
    fn cmp(&self, other: &Self) -> Ordering {
        // Denominators are positive, so cross-multiplication preserves order; on overflow compare
        // as floats, which only perturbs the ratio-test tie-break, never feasibility.
        match (self.n.checked_mul(other.d), other.n.checked_mul(self.d)) {
            (Some(a), Some(b)) => a.cmp(&b),
            _ => (self.n as f64 / self.d as f64)
                .partial_cmp(&(other.n as f64 / other.d as f64))
                .unwrap_or(Ordering::Equal),
        }
    }
}

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    if a == 0 {
        1
    } else {
        a as i128
    }
}

fn lcm(a: i128, b: i128) -> Option<i128> {
    (a / gcd(a, b)).checked_mul(b)
}

#[cfg(test)]
mod tests {
    use super::{smallest_weights, Constraint, LpWork};

    fn weights(constraints: &[Constraint], n: usize) -> Option<Vec<u32>> {
        smallest_weights(constraints, n, &mut LpWork::default()).unwrap()
    }

    fn satisfies(w: &[u32], constraints: &[Constraint]) -> bool {
        let dot = |a: &[i64]| a.iter().zip(w).map(|(&a, &w)| a * w as i64).sum::<i64>();
        w.iter().all(|&v| v >= 1)
            && constraints.iter().all(|c| match c {
                Constraint::Positive(a) => dot(a) > 0,
                Constraint::Zero(a) => dot(a) == 0,
            })
    }

    #[test]
    fn unconstrained_weights_are_all_one() {
        assert_eq!(weights(&[], 3), Some(vec![1, 1, 1]));
    }

    #[test]
    fn strict_constraints_have_the_smallest_solution() {
        // 2a > 3b, 2b > a: the least-sum rational point scales to an integer one that satisfies both.
        let c = [
            Constraint::Positive(vec![2, -3]),
            Constraint::Positive(vec![-1, 2]),
        ];
        let w = weights(&c, 2).unwrap();
        assert!(satisfies(&w, &c), "{w:?}");
    }

    #[test]
    fn contradictory_constraints_are_infeasible() {
        let c = [
            Constraint::Positive(vec![1, -2]),
            Constraint::Positive(vec![-1, 2]),
        ];
        assert_eq!(weights(&c, 2), None);
        assert_eq!(weights(&[Constraint::Zero(vec![1, 1])], 2), None);
    }

    #[test]
    fn equalities_fix_the_ray() {
        // 3a = b and 2b = c: the ray (1, 3, 6).
        let c = [
            Constraint::Zero(vec![3, -1, 0]),
            Constraint::Zero(vec![0, 2, -1]),
            Constraint::Zero(vec![6, 0, -1]),
        ];
        assert_eq!(weights(&c, 3), Some(vec![1, 3, 6]));
    }

    #[test]
    fn random_systems_agree_with_brute_force() {
        use rand::{rngs::StdRng, Rng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(1192);
        let (mut feasible, mut infeasible) = (0, 0);
        for _ in 0..300 {
            let n = rng.gen_range(2..=3);
            let rows = rng.gen_range(1..=4);
            let c: Vec<Constraint> = (0..rows)
                .map(|_| Constraint::Positive((0..n).map(|_| rng.gen_range(-3..=3)).collect()))
                .collect();
            let brute = (1..=12u32)
                .flat_map(|a| (1..=12u32).flat_map(move |b| (1..=12u32).map(move |c| [a, b, c])))
                .any(|w| satisfies(&w[..n], &c));
            match weights(&c, n) {
                Some(w) => {
                    assert!(satisfies(&w, &c), "{c:?} -> {w:?}");
                    feasible += 1;
                }
                // Brute force over a box can miss a feasible cone, never invent one.
                None => {
                    assert!(!brute, "{c:?} has a solution the LP missed");
                    infeasible += 1;
                }
            }
        }
        assert!(
            feasible > 50 && infeasible > 50,
            "{feasible} / {infeasible}"
        );
    }
}
