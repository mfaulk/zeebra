//! What the field's *storage* width is worth, measured at both widths on the same work.
//!
//! M19-D (#49) found that the apparent advantage of hand-written AVX2 over autovectorization was
//! an artifact: the two paths ran over `u64` and `u32` arrays, so the AVX2 one moved half the
//! bytes. At equal width the advantage vanished. That made storage width the lever rather than
//! instruction width, which is what `PrimeFieldElement32` exists to pull — and it left one
//! question open, since a 4-byte cell doubles the AVX2 lane count from four to eight.
//!
//! Three arms, each stating the bound it hit:
//!
//! - `axpy` — the dense elimination kernel's inner loop in isolation, at three working-set sizes,
//!   at both widths, against a hand-written 8-lane AVX2 kernel. Bytes moved per entry is exact
//!   here: two cells read and one written, so 24 bytes at 8 bytes a cell and 12 at 4.
//! - `echelon` — a whole dense row echelon over the same matrices at both widths.
//! - `f4` — F4's elimination stage at both widths on benchmark instances, which is the figure
//!   M16 attributed 65-88% of the computation to.
//!
//! ```text
//! cargo run --release --example field_width             # every arm
//! cargo run --release --example field_width -- axpy
//! cargo run --release --example field_width -- echelon
//! cargo run --release --example field_width -- f4
//! ```
//!
//! The AVX2 kernel and the scalar kernel it is compared against both operate on raw `u32`
//! Montgomery residues, because `PrimeFieldElement32`'s representation is private — the same
//! arrangement #49 used. `montgomery_replica_agrees_with_the_field` checks the replica against the
//! shipped type before any timing is taken, so a kernel that is fast and wrong cannot be reported.

use std::{
    hint::black_box,
    time::{Duration, Instant},
};

use rand::{prelude::StdRng, Rng, SeedableRng};
use zeebra::{
    fields::{Mersenne31, Zp2147483647},
    grobner::{
        benchmark_systems::{cyclic, katsura},
        f4_with_options, F4Options, F4Statistics,
    },
    linalg::{
        row_echelon_with,
        sparse::{SparseMatrix, SparseRow},
        Backend,
    },
    FiniteField, MonomialOrder, MultivariatePolynomial,
};

/// The modulus every arm runs over: 2^31 - 1, which both field types can hold.
const P: u32 = 2147483647;

// === The kernel, replicated at both widths ===

/// The dense kernel's inner loop: `target -= factor * source`, maintaining the nonzero counts.
///
/// This is `DenseRows::subtract_scaled`'s body over a whole row, and the counters are the reason
/// it is not simply an axpy: the dense backend reports the same `peak_nonzeros` the sparse one
/// does, which costs two zero tests an entry. A SIMD kernel that drops them is not measuring the
/// same thing, so neither of the ones below does.
///
/// `#[inline(never)]` so that each kernel is its own symbol in the artifact and the instruction
/// census that decides whether LLVM vectorized it is unambiguous. It is called once per row, not
/// once per entry, so this costs nothing measurable.
#[inline(never)]
fn axpy<F: FiniteField>(target: &mut [F], source: &[F], factor: F) -> (usize, usize) {
    let mut gained = 0usize;
    let mut lost = 0usize;
    for (cell, &scaled) in target.iter_mut().zip(source.iter()) {
        let before = *cell;
        let after = before - factor * scaled;
        *cell = after;

        let was_zero = before.is_zero();
        let is_zero = after.is_zero();
        gained += usize::from(was_zero & !is_zero);
        lost += usize::from(!was_zero & is_zero);
    }
    (gained, lost)
}

/// Montgomery arithmetic over raw `u32` residues, replicating `fields::prime_field_32`.
///
/// Needed because the shipped representation is private and the AVX2 kernel has to see it. Checked
/// against the shipped type by [`montgomery_replica_agrees_with_the_field`].
mod replica {
    pub const fn n_prime(p: u32) -> u32 {
        let mut inverse: u32 = 1;
        let mut step = 0;
        while step < 5 {
            inverse = inverse.wrapping_mul(2u32.wrapping_sub(p.wrapping_mul(inverse)));
            step += 1;
        }
        inverse.wrapping_neg()
    }

    pub const fn r2_mod_p(p: u32) -> u32 {
        let r = ((1u64 << 32) % p as u64) as u32;
        ((r as u64 * r as u64) % p as u64) as u32
    }

    /// `t * R^-1 mod P`, for P at or below 2^31 so that `t + m*P` stays inside 64 bits.
    #[inline(always)]
    pub fn redc(t: u64, p: u32) -> u32 {
        let m = (t as u32).wrapping_mul(n_prime(p));
        let high = ((t + m as u64 * p as u64) >> 32) as u32;
        if high >= p {
            high - p
        } else {
            high
        }
    }

    #[inline(always)]
    pub fn mul(a: u32, b: u32, p: u32) -> u32 {
        redc(a as u64 * b as u64, p)
    }

    /// A canonical residue to Montgomery form.
    pub fn to_internal(canonical: u32, p: u32) -> u32 {
        mul(canonical, r2_mod_p(p), p)
    }

    /// Montgomery form back to a canonical residue.
    pub fn to_canonical(internal: u32, p: u32) -> u32 {
        redc(internal as u64, p)
    }

    /// The scalar kernel the AVX2 one is compared against, over the same raw residues.
    #[inline(never)]
    pub fn axpy(target: &mut [u32], source: &[u32], factor: u32, p: u32) -> (usize, usize) {
        let mut gained = 0usize;
        let mut lost = 0usize;
        for (cell, &scaled) in target.iter_mut().zip(source.iter()) {
            let before = *cell;
            let product = mul(factor, scaled, p);
            let (difference, borrow) = before.overflowing_sub(product);
            let after = if borrow {
                difference.wrapping_add(p)
            } else {
                difference
            };
            *cell = after;

            gained += usize::from((before == 0) & (after != 0));
            lost += usize::from((before != 0) & (after == 0));
        }
        (gained, lost)
    }
}

/// The replica computes the field's multiplication, so a measurement over it is a measurement of
/// the field.
fn montgomery_replica_agrees_with_the_field() {
    let mut rng = StdRng::seed_from_u64(11);
    for _ in 0..4096 {
        let (a, b) = (rng.gen_range(0..P), rng.gen_range(0..P));
        let expected = (Mersenne31::new(a as u64) * Mersenne31::new(b as u64)).value();
        let product = replica::mul(replica::to_internal(a, P), replica::to_internal(b, P), P);
        assert_eq!(
            replica::to_canonical(product, P),
            expected,
            "the replica disagrees with the field on {a} * {b}"
        );
    }
}

// === The 8-lane AVX2 kernel ===

/// The same kernel at eight lanes, which is the question #49 left open at four.
///
/// Three `vpmuludq` per half of the vector: the product, `m = low32(t) * n'`, and `m * P`. The two
/// conditional subtractions are `vpminud` over the wrapped difference, which is correct for any P
/// at or below 2^31 and is what lets the whole thing stay branchless.
#[cfg(target_arch = "x86_64")]
#[inline(never)]
#[target_feature(enable = "avx2")]
unsafe fn axpy_avx2(target: &mut [u32], source: &[u32], factor: u32, p: u32) -> (usize, usize) {
    use std::arch::x86_64::*;

    const LANES: usize = 8;

    /// `a * b * R^-1 mod P` over eight `u32` lanes.
    #[inline(always)]
    unsafe fn mont_mul(a: __m256i, b: __m256i, p: __m256i, np: __m256i) -> __m256i {
        // `_mm256_mul_epu32` reads the low half of each 64-bit lane, so the odd 32-bit lanes are
        // shifted down and handled as a second pass.
        let a_odd = _mm256_srli_epi64(a, 32);
        let b_odd = _mm256_srli_epi64(b, 32);

        let t_even = _mm256_mul_epu32(a, b);
        let t_odd = _mm256_mul_epu32(a_odd, b_odd);

        // m = low32(t) * n' mod 2^32, which is the low half of this product, and is exactly what
        // the next multiply reads.
        let m_even = _mm256_mul_epu32(t_even, np);
        let m_odd = _mm256_mul_epu32(t_odd, np);

        let sum_even = _mm256_add_epi64(t_even, _mm256_mul_epu32(m_even, p));
        let sum_odd = _mm256_add_epi64(t_odd, _mm256_mul_epu32(m_odd, p));

        // The low 32 bits of each sum are zero by construction, so the shift is the division by R.
        let high_even = _mm256_srli_epi64(sum_even, 32);
        let high_odd = _mm256_srli_epi64(sum_odd, 32);
        let high = _mm256_blend_epi32(high_even, _mm256_slli_epi64(high_odd, 32), 0b1010_1010);

        // The quotient is below 2P, so one conditional subtraction reduces it.
        _mm256_min_epu32(high, _mm256_sub_epi32(high, p))
    }

    let p_vec = _mm256_set1_epi32(p as i32);
    let np_vec = _mm256_set1_epi32(replica::n_prime(p) as i32);
    let factor_vec = _mm256_set1_epi32(factor as i32);
    let zero = _mm256_setzero_si256();

    let mut gained = 0usize;
    let mut lost = 0usize;

    let chunks = target.len() / LANES;
    for chunk in 0..chunks {
        let offset = chunk * LANES;
        let cells = target.as_mut_ptr().add(offset) as *mut __m256i;
        let before = _mm256_loadu_si256(cells as *const __m256i);
        let scaled = _mm256_loadu_si256(source.as_ptr().add(offset) as *const __m256i);

        let product = mont_mul(scaled, factor_vec, p_vec, np_vec);
        let difference = _mm256_sub_epi32(before, product);
        let after = _mm256_min_epu32(difference, _mm256_add_epi32(difference, p_vec));
        _mm256_storeu_si256(cells, after);

        // The counters, which the shipped kernel maintains and so this one must too: a lane mask
        // per comparison, and a population count over the eight bits.
        let before_zero =
            _mm256_movemask_ps(_mm256_castsi256_ps(_mm256_cmpeq_epi32(before, zero))) as u32;
        let after_zero =
            _mm256_movemask_ps(_mm256_castsi256_ps(_mm256_cmpeq_epi32(after, zero))) as u32;
        gained += (before_zero & !after_zero & 0xFF).count_ones() as usize;
        lost += (!before_zero & after_zero & 0xFF).count_ones() as usize;
    }

    // The tail, scalar. Row lengths in F4 are not multiples of eight.
    let tail = chunks * LANES;
    let (gained_tail, lost_tail) = replica::axpy(&mut target[tail..], &source[tail..], factor, p);
    (gained + gained_tail, lost + lost_tail)
}

/// The AVX2 kernel writes the same cells and reports the same counters as the scalar one.
#[cfg(target_arch = "x86_64")]
fn avx2_agrees_with_scalar() {
    let mut rng = StdRng::seed_from_u64(29);
    // Lengths either side of a vector, and one that is not a multiple of eight, for the tail.
    for length in [0usize, 1, 7, 8, 9, 64, 251] {
        // A third of the cells zero, so both counters are exercised rather than only one.
        let draw = |rng: &mut StdRng| -> u32 {
            if rng.gen_bool(0.33) {
                0
            } else {
                replica::to_internal(rng.gen_range(0..P), P)
            }
        };
        let source: Vec<u32> = (0..length).map(|_| draw(&mut rng)).collect();
        let original: Vec<u32> = (0..length).map(|_| draw(&mut rng)).collect();
        let factor = replica::to_internal(rng.gen_range(0..P), P);

        let mut expected = original.clone();
        let scalar = replica::axpy(&mut expected, &source, factor, P);

        let mut actual = original.clone();
        let vector = unsafe { axpy_avx2(&mut actual, &source, factor, P) };

        assert_eq!(actual, expected, "cells disagree at length {length}");
        assert_eq!(vector, scalar, "counters disagree at length {length}");
    }
}

// === Arm 1: the kernel in isolation ===

/// Row lengths, chosen so that both widths land in the same level of cache at each one.
///
/// A pair of rows is `2 * entries * width` bytes, so the footprints run 8/16 KB, 256 KB/512 KB,
/// 16/32 MB and 128/256 MB. Naming the entry count rather than the byte count is what makes the
/// two widths comparable: the same number of cell updates, and half the bytes to do them in.
///
/// The last row is there because this machine has 256 MB of L3: a 32 MB working set, which #49
/// called out of cache, is out of L2 but still in L3, so a bandwidth claim needs a size above it.
const LENGTHS: [(&str, usize); 4] = [
    ("L1", 512),
    ("L2", 32 * 1024),
    ("L3", 2 * 1024 * 1024),
    ("DRAM", 16 * 1024 * 1024),
];

fn axpy_arm() {
    montgomery_replica_agrees_with_the_field();
    #[cfg(target_arch = "x86_64")]
    avx2_agrees_with_scalar();

    println!("\n=== axpy: `target -= factor * source` with the nonzero counters ===\n");
    println!(
        "{:<6} {:>9} {:>9} {:<22} {:>10} {:>9} {:>8}",
        "level", "entries", "pair/KB", "kernel", "ns/entry", "bytes/e", "GB/s"
    );

    for (level, entries) in LENGTHS {
        let passes = passes_for(entries);

        let wide = time_field_axpy::<Zp2147483647>(entries, passes);
        report(level, entries, 8, "scalar u64 (library)", wide);

        let narrow = time_field_axpy::<Mersenne31>(entries, passes);
        report(level, entries, 4, "scalar u32 (library)", narrow);

        let replica = time_replica_axpy(entries, passes, Kernel::Scalar);
        report(level, entries, 4, "scalar u32 (replica)", replica);

        #[cfg(target_arch = "x86_64")]
        {
            let vector = time_replica_axpy(entries, passes, Kernel::Avx2);
            report(level, entries, 4, "AVX2 u32, 8 lanes", vector);
        }
        #[cfg(not(target_arch = "x86_64"))]
        println!("  AVX2 arm skipped: not x86_64");
        println!();
    }
}

/// Enough passes that the shortest row is still timed over tens of milliseconds.
fn passes_for(entries: usize) -> usize {
    ((1 << 26) / entries).max(4)
}

/// Nanoseconds per entry, over `passes` passes of a `entries`-long row pair.
fn time_field_axpy<F: FiniteField>(entries: usize, passes: usize) -> f64 {
    let mut rng = StdRng::seed_from_u64(7);
    let source: Vec<F> = (0..entries).map(|_| F::random(&mut rng)).collect();
    let mut target: Vec<F> = (0..entries).map(|_| F::random(&mut rng)).collect();
    let factor = F::new(3);

    // One untimed pass, so the first timed one is not paying for the first touch of the pages.
    axpy(&mut target, &source, factor);

    let start = Instant::now();
    for _ in 0..passes {
        let counts = axpy(black_box(&mut target), black_box(&source), factor);
        black_box(counts);
    }
    nanos_per_entry(start.elapsed(), entries, passes)
}

enum Kernel {
    Scalar,
    #[cfg(target_arch = "x86_64")]
    Avx2,
}

fn time_replica_axpy(entries: usize, passes: usize, kernel: Kernel) -> f64 {
    let mut rng = StdRng::seed_from_u64(7);
    let source: Vec<u32> = (0..entries)
        .map(|_| replica::to_internal(rng.gen_range(0..P), P))
        .collect();
    let mut target: Vec<u32> = (0..entries)
        .map(|_| replica::to_internal(rng.gen_range(0..P), P))
        .collect();
    let factor = replica::to_internal(3, P);

    match kernel {
        Kernel::Scalar => {
            replica::axpy(&mut target, &source, factor, P);
            let start = Instant::now();
            for _ in 0..passes {
                let counts = replica::axpy(black_box(&mut target), black_box(&source), factor, P);
                black_box(counts);
            }
            nanos_per_entry(start.elapsed(), entries, passes)
        }
        #[cfg(target_arch = "x86_64")]
        Kernel::Avx2 => {
            assert!(
                std::arch::is_x86_feature_detected!("avx2"),
                "this machine has no AVX2"
            );
            unsafe {
                axpy_avx2(&mut target, &source, factor, P);
                let start = Instant::now();
                for _ in 0..passes {
                    let counts = axpy_avx2(black_box(&mut target), black_box(&source), factor, P);
                    black_box(counts);
                }
                nanos_per_entry(start.elapsed(), entries, passes)
            }
        }
    }
}

fn nanos_per_entry(elapsed: Duration, entries: usize, passes: usize) -> f64 {
    elapsed.as_secs_f64() * 1e9 / (entries as f64 * passes as f64)
}

/// One row of the axpy table. `bytes` is the cell width; two cells are read and one written.
fn report(level: &str, entries: usize, bytes: usize, kernel: &str, nanos: f64) {
    let per_entry = 3 * bytes;
    let footprint = 2 * entries * bytes / 1024;
    println!(
        "{:<6} {:>9} {:>9} {:<22} {:>10.3} {:>9} {:>8.1}",
        level,
        entries,
        footprint,
        kernel,
        nanos,
        per_entry,
        per_entry as f64 / nanos
    );
}

// === Arm 2: a whole dense row echelon ===

/// Shapes and densities in the range F4's matrices occupy, large enough to leave L2.
const SHAPES: [(usize, usize, f64); 3] = [(512, 512, 0.10), (1500, 1500, 0.05), (3000, 3000, 0.02)];

fn echelon_arm() {
    println!("\n=== dense row echelon over the same matrices at both widths ===\n");
    println!(
        "{:<14} {:>7} {:>9} {:>9} {:>8} {:>9} {:>8}",
        "shape", "density", "cells", "u64/ms", "u64/MB", "u32/ms", "u32/MB"
    );

    for (rows, columns, density) in SHAPES {
        // One draw of residues, used to build both matrices, so the two eliminations are over the
        // same matrix and not merely over the same distribution.
        let entries = draw_entries(rows, columns, density, 4242);

        let mut wide = matrix_of::<Zp2147483647>(&entries, columns);
        let start = Instant::now();
        let wide_statistics = row_echelon_with(Backend::Dense, &mut wide, usize::MAX)
            .expect("the budget is unbounded");
        let wide_elapsed = start.elapsed();

        let mut narrow = matrix_of::<Mersenne31>(&entries, columns);
        let start = Instant::now();
        let narrow_statistics = row_echelon_with(Backend::Dense, &mut narrow, usize::MAX)
            .expect("the budget is unbounded");
        let narrow_elapsed = start.elapsed();

        // The two have to have done the same elimination, or the times are not comparable.
        assert_eq!(wide_statistics.rank, narrow_statistics.rank);
        assert_eq!(
            wide_statistics.row_operations,
            narrow_statistics.row_operations
        );
        assert_eq!(
            wide_statistics.final_nonzeros,
            narrow_statistics.final_nonzeros
        );

        let cells = rows * columns;
        println!(
            "{:<14} {:>6.0}% {:>9} {:>9.1} {:>8.1} {:>9.1} {:>8.1}",
            format!("{rows}x{columns}"),
            density * 100.0,
            cells,
            millis(wide_elapsed),
            megabytes(cells * 8),
            millis(narrow_elapsed),
            megabytes(cells * 4),
        );
    }
}

/// Entries as plain integers, so one draw can be interpreted at either width.
fn draw_entries(rows: usize, columns: usize, density: f64, seed: u64) -> Vec<Vec<(usize, u64)>> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..rows)
        .map(|_| {
            (0..columns)
                .filter_map(|column| {
                    if rng.gen_bool(density) {
                        Some((column, rng.gen_range(1..P as u64)))
                    } else {
                        None
                    }
                })
                .collect()
        })
        .collect()
}

fn matrix_of<F: FiniteField>(entries: &[Vec<(usize, u64)>], columns: usize) -> SparseMatrix<F> {
    let rows: Vec<SparseRow<F>> = entries
        .iter()
        .map(|row| {
            let entries: Vec<(usize, F)> = row
                .iter()
                .map(|&(column, value)| (column, F::new(value)))
                .collect();
            SparseRow::new(&entries)
        })
        .collect();
    SparseMatrix::new(columns, rows)
}

// === Arm 3: F4's elimination stage ===

/// Every backend, because the width is worth different things to each.
///
/// `Sparse` stores `(usize, F)`, which the index's alignment pads to 16 bytes at either width, so
/// it is the arm where the narrower field is expected to buy nothing. `Dense` and `Adaptive` hold
/// bare cells, and are where it should pay.
const BACKENDS: [(&str, Backend); 3] = [
    ("sparse", Backend::Sparse),
    ("adaptive", Backend::Adaptive),
    ("dense", Backend::Dense),
];

fn f4_arm() {
    println!("\n=== F4 elimination at both widths, per backend ===\n");
    println!(
        "{:<12} {:<8} {:<9} {:>10} {:>10} {:>10} {:>10} {:>8} {:>9}",
        "system",
        "order",
        "backend",
        "u64 elim",
        "u64 total",
        "u32 elim",
        "u32 total",
        "elim x",
        "entry/MB"
    );

    let grevlex = MonomialOrder::GradedReverseLexicographic;
    let lex = MonomialOrder::Lexicographic;

    f4_row("cyclic-5", lex, &cyclic::<5, _>(), &cyclic::<5, _>());
    f4_row("katsura-5", grevlex, &katsura::<6, _>(), &katsura::<6, _>());
    f4_row("katsura-6", grevlex, &katsura::<7, _>(), &katsura::<7, _>());
}

/// One instance at both widths and every backend.
///
/// The systems are built twice because the coefficient type differs; they are the same system,
/// since every coefficient comes from `F::one()` and small integers. A backend that refuses the
/// instance — the dense one allocates `rows x columns` cells whatever the entry budget says —
/// prints its error rather than being silently dropped.
fn f4_row<const N: usize>(
    name: &str,
    order: MonomialOrder,
    wide: &[MultivariatePolynomial<N, Zp2147483647>],
    narrow: &[MultivariatePolynomial<N, Mersenne31>],
) {
    for (backend_name, elimination) in BACKENDS {
        let options = F4Options {
            measure_stages: true,
            elimination,
            ..Default::default()
        };

        let wide_result = f4_with_options(wide, order, &options);
        let narrow_result = f4_with_options(narrow, order, &options);
        let ((wide_basis, wide_statistics), (narrow_basis, narrow_statistics)): (
            (Vec<_>, F4Statistics),
            (Vec<_>, F4Statistics),
        ) = match (wide_result, narrow_result) {
            (Ok(wide), Ok(narrow)) => (wide, narrow),
            (wide, narrow) => {
                // Both widths have to refuse, or the comparison is not of one computation.
                println!(
                    "{:<12} {:<8} {:<9} {}",
                    name,
                    order_name(order),
                    backend_name,
                    match (wide, narrow) {
                        (Err(error), Err(_)) => format!("refused at both widths: {error}"),
                        (Err(error), Ok(_)) => format!("refused at 64 bits only: {error}"),
                        (Ok(_), Err(error)) => format!("refused at 32 bits only: {error}"),
                        (Ok(_), Ok(_)) => unreachable!(),
                    }
                );
                continue;
            }
        };

        // The same computation, or the stage times are not comparable.
        assert_eq!(wide_basis.len(), narrow_basis.len());
        assert_eq!(
            wide_statistics.max_live_nonzeros,
            narrow_statistics.max_live_nonzeros
        );

        let wide_elimination = millis(wide_statistics.stages.elimination);
        let narrow_elimination = millis(narrow_statistics.stages.elimination);
        println!(
            "{:<12} {:<8} {:<9} {:>10.2} {:>10.2} {:>10.2} {:>10.2} {:>8.2} {:>9.2}",
            name,
            order_name(order),
            backend_name,
            wide_elimination,
            millis(wide_statistics.total),
            narrow_elimination,
            millis(narrow_statistics.total),
            wide_elimination / narrow_elimination,
            // The entry budget is the same at either width: a sparse entry is `(usize, F)`, which
            // the index's alignment pads to 16 bytes whether the coefficient is four or eight.
            megabytes(wide_statistics.max_live_nonzeros * wide_statistics.bytes_per_entry),
        );
    }
}

fn order_name(order: MonomialOrder) -> &'static str {
    match order {
        MonomialOrder::Lexicographic => "lex",
        MonomialOrder::GradedLexicographic => "grlex",
        MonomialOrder::GradedReverseLexicographic => "grevlex",
    }
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1e3
}

fn megabytes(bytes: usize) -> f64 {
    bytes as f64 / (1024.0 * 1024.0)
}

fn main() {
    let arms: Vec<String> = std::env::args().skip(1).collect();
    let selected = |name: &str| arms.is_empty() || arms.iter().any(|arm| arm == name);

    println!("modulus 2^31 - 1, held in a u64 (`Zp2147483647`) and in a u32 (`Mersenne31`)");
    println!(
        "element size: {} bytes and {} bytes; sparse entry: {} bytes either way",
        std::mem::size_of::<Zp2147483647>(),
        std::mem::size_of::<Mersenne31>(),
        std::mem::size_of::<(usize, Mersenne31)>(),
    );

    if selected("axpy") {
        axpy_arm();
    }
    if selected("echelon") {
        echelon_arm();
    }
    if selected("f4") {
        f4_arm();
    }
}
