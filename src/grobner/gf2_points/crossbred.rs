//! Crossbred at `(D, d = 1)` over `GF(2)` (Joux–Vitse, 2017/372; #1156).
//!
//! Variables `0..k` are *kept* and `k..n` are *enumerated*. Preprocessing eliminates, in the
//! degree-`D` Boolean Macaulay matrix, every column whose monomial has degree two or more in the
//! kept variables. The rows left with none of those columns are combinations of the equations of
//! the form `Σ_{p<k} x_p·g_p(y) + g_k(y)`. At every assignment `y` of the enumerated variables
//! they are a linear system in the kept ones. Every point of the system satisfies every
//! combination, so solving that linear system loses nothing: the method is complete.

use std::{collections::HashMap, sync::atomic::AtomicU64, sync::atomic::Ordering};

use super::{
    drive, kernel::mobius_in_place, BooleanQuadraticSystem, Gf2PointError, Gf2PointOptions,
    Gf2PointReport,
};
use crate::linalg::gf2::{reduced_row_echelon_four_russians, BitMatrix};

/// The low enumerated variables evaluated per chunk by one Möbius transform.
const CHUNK_BITS: usize = 14;

/// Four Russians table width for the Macaulay elimination.
const TABLE_BITS: usize = 8;

/// `k` kept variables and Macaulay degree `D`; `d = 1` is fixed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CrossbredParameters {
    pub kept: usize,
    pub degree: usize,
}

/// The shape of crossbred's preprocessing.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CrossbredStatistics {
    /// Macaulay rows: one per (multiplier of degree ≤ `D − 2`, equation).
    pub rows: usize,
    /// Boolean monomials of degree ≤ `D`.
    pub columns: usize,
    /// Columns of degree ≥ 2 in the kept variables: the ones eliminated.
    pub high_columns: usize,
    /// The Macaulay matrix's rank.
    pub rank: usize,
    /// Combinations retained: linear in the kept variables.
    pub polynomials: usize,
}

/// Every mask over `n` variables with at most `degree` bits, by increasing popcount.
fn masks_up_to(n: usize, degree: usize) -> Vec<u64> {
    let mut out = vec![0u64];
    let mut layer = vec![0u64];
    for _ in 0..degree.min(n) {
        let mut next = Vec::new();
        for &mask in &layer {
            let start = if mask == 0 {
                0
            } else {
                64 - mask.leading_zeros() as usize
            };
            next.extend((start..n).map(|i| mask | 1 << i));
        }
        out.extend_from_slice(&next);
        layer = next;
    }
    out
}

/// The retained combinations, bitsliced: `entries[g * (k + 1) + p]` lists `(y, lanes)`, the lane
/// mask of group `g` (64 combinations) on `x_p · y^…` — `p = k` is the term free of kept variables
/// — with `y` a mask over the enumerated variables, shifted down by `k`.
struct Combinations {
    groups: usize,
    entries: Vec<Vec<(u64, u64)>>,
    count: usize,
}

fn preprocess(
    system: &BooleanQuadraticSystem,
    CrossbredParameters { kept: k, degree }: CrossbredParameters,
    budget: usize,
) -> Result<(Combinations, CrossbredStatistics), Gf2PointError> {
    let n = system.vars;
    let kept_mask = if k == 64 { !0 } else { (1u64 << k) - 1 };
    let mut columns = masks_up_to(n, degree);
    // High columns first, so that rows reduced to zero there lead in a low column.
    columns.sort_by_key(|&mask| (mask & kept_mask).count_ones() < 2);
    let high = columns
        .iter()
        .take_while(|&&mask| (mask & kept_mask).count_ones() >= 2)
        .count();
    let index: HashMap<u64, usize> = columns.iter().enumerate().map(|(i, &m)| (m, i)).collect();
    let multipliers = masks_up_to(n, degree - 2);
    let rows = multipliers.len() * system.equations.len();
    let bytes = rows * columns.len().div_ceil(64) * 8;
    if bytes > budget {
        return Err(Gf2PointError::MatrixTooLarge {
            rows,
            columns: columns.len(),
            bytes,
            budget,
        });
    }
    let mut matrix = BitMatrix::zero(rows, columns.len());
    let mut row = 0;
    for &u in &multipliers {
        for equation in &system.equations {
            for monomial in equation.monomials() {
                let column = index[&(u | monomial)];
                let set = matrix.get(row, column);
                matrix.set(row, column, !set);
            }
            row += 1;
        }
    }
    let rank = reduced_row_echelon_four_russians(&mut matrix, TABLE_BITS).rank;
    let retained: Vec<usize> = (0..rank)
        .filter(|&r| matrix.leading_column(r).is_some_and(|c| c >= high))
        .collect();
    let groups = retained.len().div_ceil(64);
    let mut merged: Vec<HashMap<u64, u64>> = vec![HashMap::new(); groups * (k + 1)];
    for (index, &r) in retained.iter().enumerate() {
        let (group, bit) = (index / 64, 1u64 << (index % 64));
        for (w, &word) in matrix.row(r).iter().enumerate() {
            let mut rest = word;
            while rest != 0 {
                let mask = columns[w * 64 + rest.trailing_zeros() as usize];
                rest &= rest - 1;
                let x = mask & kept_mask;
                let p = if x == 0 {
                    k
                } else {
                    x.trailing_zeros() as usize
                };
                let y = if k == 64 { 0 } else { mask >> k };
                *merged[group * (k + 1) + p].entry(y).or_insert(0) ^= bit;
            }
        }
    }
    let statistics = CrossbredStatistics {
        rows,
        columns: columns.len(),
        high_columns: high,
        rank,
        polynomials: retained.len(),
    };
    let entries = merged
        .into_iter()
        .map(|m| m.into_iter().filter(|&(_, lanes)| lanes != 0).collect())
        .collect();
    Ok((
        Combinations {
            groups,
            entries,
            count: retained.len(),
        },
        statistics,
    ))
}

/// The solutions of one guess's linear system, passed to `emit` as masks over the kept variables;
/// `false` from `emit` stops. `row(i)` is combination `i`: bit `p < k` the coefficient of `x_p`,
/// bit `k` the constant. Rows are reduced one at a time, so an inconsistent guess — almost all of
/// them — is usually rejected after about `k + 1` rows.
fn solve_linear(
    k: usize,
    count: usize,
    row: impl Fn(usize) -> u64,
    pivots: &mut Vec<(usize, u64)>,
    mut emit: impl FnMut(u64) -> bool,
) -> bool {
    pivots.clear();
    let constant = 1u64 << k;
    for i in 0..count {
        let mut r = row(i);
        for &(column, pivot) in pivots.iter() {
            if r >> column & 1 == 1 {
                r ^= pivot;
            }
        }
        if r == 0 {
            continue;
        }
        if r == constant {
            return true;
        }
        let column = r.trailing_zeros() as usize;
        for (_, pivot) in pivots.iter_mut() {
            if *pivot >> column & 1 == 1 {
                *pivot ^= r;
            }
        }
        pivots.push((column, r));
    }
    let pivot_mask = pivots.iter().fold(0u64, |m, &(c, _)| m | 1 << c);
    let free = ((constant - 1) & !pivot_mask).count_ones();
    let free_mask = (constant - 1) & !pivot_mask;
    for assignment in 0..1u64 << free {
        let x_free = deposit(assignment, free_mask);
        let mut x = x_free;
        for &(column, pivot) in pivots.iter() {
            let value = ((pivot & x_free).count_ones() & 1) as u64 ^ (pivot >> k & 1);
            x |= value << column;
        }
        if !emit(x) {
            return false;
        }
    }
    true
}

/// The low bits of `bits` spread over the set bits of `mask`.
fn deposit(mut bits: u64, mut mask: u64) -> u64 {
    let mut out = 0;
    while mask != 0 {
        let low = mask & mask.wrapping_neg();
        if bits & 1 == 1 {
            out |= low;
        }
        bits >>= 1;
        mask ^= low;
    }
    out
}

pub(super) fn solve(
    system: &BooleanQuadraticSystem,
    parameters: CrossbredParameters,
    options: &Gf2PointOptions,
    first: bool,
) -> Result<(Vec<u64>, Gf2PointReport), Gf2PointError> {
    let n = system.vars;
    let CrossbredParameters { kept: k, degree } = parameters;
    if k == 0 || k > n.min(63) || degree < 2 || degree > n.max(2) {
        return Err(Gf2PointError::InvalidParameters {
            variables: n,
            kept: k,
            degree,
        });
    }
    let (combinations, statistics) = preprocess(system, parameters, options.matrix_budget_bytes)?;
    let enumerated = n - k;
    let c = enumerated.min(CHUNK_BITS);
    let chunks = 1u64 << (enumerated - c);
    let width = combinations.groups * (k + 1);
    let candidates = AtomicU64::new(0);
    let walk = |chunk: u64, emit: &mut dyn FnMut(u64) -> bool| {
        let low_mask = (1u64 << c) - 1;
        let mut table = vec![0u64; width << c];
        for (slot, entries) in combinations.entries.iter().enumerate() {
            for &(y, lanes) in entries {
                // A monomial with an enumerated variable fixed to zero in this chunk vanishes.
                if (y >> c) & !chunk != 0 {
                    continue;
                }
                table[(y & low_mask) as usize * width + slot] ^= lanes;
            }
        }
        mobius_in_place(&mut table, c, width);
        let mut pivots = Vec::with_capacity(k);
        let mut seen = 0;
        for low in 0..1u64 << c {
            let block = &table[low as usize * width..(low as usize + 1) * width];
            let y = (chunk << c | low) << k;
            let row = |i: usize| {
                let (group, lane) = (i / 64, i % 64);
                block[group * (k + 1)..(group + 1) * (k + 1)]
                    .iter()
                    .enumerate()
                    .fold(0u64, |r, (p, &w)| r | (w >> lane & 1) << p)
            };
            let go_on = solve_linear(k, combinations.count, row, &mut pivots, |x| {
                seen += 1;
                let point = x | y;
                !system.vanishes_at(point) || emit(point)
            });
            if !go_on {
                break;
            }
        }
        candidates.fetch_add(seen, Ordering::Relaxed);
    };
    let (points, walked) = drive(chunks, options.workers, first, &walk);
    let report = Gf2PointReport {
        chunks,
        chunks_walked: walked,
        points_per_chunk: 1 << c,
        candidates: candidates.into_inner(),
        preprocessing: Some(statistics),
    };
    Ok((points, report))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn masks_up_to_counts_binomial_prefixes() {
        assert_eq!(masks_up_to(5, 0), vec![0]);
        assert_eq!(masks_up_to(5, 2).len(), 1 + 5 + 10);
        assert_eq!(masks_up_to(6, 3).len(), 1 + 6 + 15 + 20);
        assert_eq!(masks_up_to(3, 9).len(), 8);
        let masks = masks_up_to(7, 3);
        let mut unique = masks.clone();
        unique.sort_unstable();
        unique.dedup();
        assert_eq!(unique.len(), masks.len());
    }

    #[test]
    fn deposit_spreads_bits_over_the_mask() {
        assert_eq!(deposit(0b11, 0b1010), 0b1010);
        assert_eq!(deposit(0b01, 0b1010), 0b0010);
        assert_eq!(deposit(0b10, 0b1010), 0b1000);
        assert_eq!(deposit(0b101, 0b1_0110), 0b1_0010);
    }

    /// Every solution of a small linear system, against brute force over all `2^k` assignments.
    #[test]
    fn linear_solve_returns_exactly_the_affine_solution_set() {
        use rand::{rngs::StdRng, Rng, SeedableRng};
        let mut rng = StdRng::seed_from_u64(11);
        for k in 1..=7 {
            for _ in 0..200 {
                let count = rng.gen_range(0..2 * k + 2);
                let rows: Vec<u64> = (0..count)
                    .map(|_| rng.gen::<u64>() & ((2 << k) - 1))
                    .collect();
                let satisfies = |x: u64| {
                    rows.iter()
                        .all(|&r| ((r & x).count_ones() & 1) as u64 == r >> k & 1)
                };
                let expected: Vec<u64> = (0..1u64 << k).filter(|&x| satisfies(x)).collect();
                let mut got = Vec::new();
                let mut pivots = Vec::new();
                solve_linear(
                    k,
                    count,
                    |i| rows[i],
                    &mut pivots,
                    |x| {
                        got.push(x);
                        true
                    },
                );
                got.sort_unstable();
                assert_eq!(got, expected, "k = {k}, rows = {rows:?}");
            }
        }
    }
}
