use std::{cmp::Ordering, hint::black_box, time::Instant};

use rand::{rngs::StdRng, Rng, SeedableRng};
use zeebra::{Monomial, MonomialOrder};

// A key is valid only for the order that produced it; callers retain the full monomial.
fn key<const N: usize>(monomial: &Monomial<N>, order: MonomialOrder) -> Option<u64> {
    if N > 7 || monomial.degree() > 255 {
        return None;
    }
    let mut key = 0u64;
    match order {
        MonomialOrder::Lexicographic | MonomialOrder::GradedLexicographic => {
            for &exponent in monomial.exponents() {
                key = (key << 8) | u64::from(u8::try_from(exponent).ok()?);
            }
        }
        MonomialOrder::GradedReverseLexicographic => {
            for &exponent in monomial.exponents().iter().rev() {
                key = (key << 8) | u64::from(!u8::try_from(exponent).ok()?);
            }
        }
        MonomialOrder::Weighted(_) => return None,
    }
    if order != MonomialOrder::Lexicographic {
        key |= monomial.degree() << 56;
    }
    Some(key)
}

fn compare<const N: usize>(a: &Monomial<N>, b: &Monomial<N>, order: MonomialOrder) -> Ordering {
    match (key(a, order), key(b, order)) {
        (Some(a), Some(b)) => a.cmp(&b),
        _ => order.cmp(a, b),
    }
}

fn run<const N: usize>() {
    let mut rng = StdRng::seed_from_u64(317);
    let data: Vec<_> = (0..2048)
        .map(|_| Monomial::<N>::new(&std::array::from_fn::<_, N, _>(|_| rng.gen_range(0..=7))))
        .collect();
    for order in [
        MonomialOrder::Lexicographic,
        MonomialOrder::GradedLexicographic,
        MonomialOrder::GradedReverseLexicographic,
    ] {
        let started = Instant::now();
        let keys: Option<Vec<_>> = data.iter().map(|m| key(m, order)).collect();
        let packing = started.elapsed();
        let Some(keys) = keys else {
            println!(
                "N={N} {} unsupported; full comparison required",
                order.name()
            );
            continue;
        };
        for i in 0..data.len() {
            assert_eq!(
                compare(&data[i], &data[(i + 7919) % data.len()], order),
                order.cmp(&data[i], &data[(i + 7919) % data.len()])
            );
        }
        let mut samples = [Vec::new(), Vec::new()];
        for repetition in 0..9 {
            for offset in 0..2 {
                let arm = (repetition + offset) % 2;
                let started = Instant::now();
                let mut checksum = 0i64;
                for _ in 0..1000 {
                    let data = black_box(&data);
                    let keys = black_box(&keys);
                    for i in 0..data.len() {
                        let j = (i + 7919) % data.len();
                        let ordering = if arm == 0 {
                            order.cmp(&data[i], &data[j])
                        } else {
                            keys[i].cmp(&keys[j])
                        };
                        checksum = checksum.wrapping_add(ordering as i64);
                    }
                }
                black_box(checksum);
                samples[arm].push(started.elapsed().as_secs_f64() * 1000.0);
            }
        }
        for sample in &mut samples {
            sample.sort_by(f64::total_cmp);
        }
        println!(
            "N={N} {} packing_ms={:.3} production_ms={:.3} packed_ms={:.3} ratio={:.3}",
            order.name(),
            packing.as_secs_f64() * 1000.0,
            samples[0][4],
            samples[1][4],
            samples[0][4] / samples[1][4]
        );
    }
}

fn main() {
    run::<5>();
    run::<7>();
    run::<8>();
}

#[cfg(test)]
mod tests {
    use super::*;

    // Packed keys agree with all built-in orders, including degree ties and equal operands.
    #[test]
    fn packed_orders_match_full_comparisons() {
        let monomials: Vec<_> = (0..64)
            .map(|n| Monomial::<3>::new(&[n % 4, (n / 4) % 4, n / 16]))
            .collect();
        for order in [
            MonomialOrder::Lexicographic,
            MonomialOrder::GradedLexicographic,
            MonomialOrder::GradedReverseLexicographic,
        ] {
            for a in &monomials {
                for b in &monomials {
                    assert_eq!(compare(a, b, order), order.cmp(a, b));
                }
            }
        }
    }

    // Oversized arities, degrees and exponents fall back without narrowing or truncation.
    #[test]
    fn packing_refuses_overflow_and_preserves_fallback() {
        let order = MonomialOrder::GradedReverseLexicographic;
        for a in [
            Monomial::<7>::univariate(0, 256),
            Monomial::new(&[128, 128, 0, 0, 0, 0, 0]),
            Monomial::univariate(6, u32::MAX),
        ] {
            let b = Monomial::one();
            assert!(key(&a, order).is_none());
            assert_eq!(compare(&a, &b, order), order.cmp(&a, &b));
            assert_eq!(compare(&b, &a, order), order.cmp(&b, &a));
        }
        assert!(key(&Monomial::<8>::one(), order).is_none());
        assert_eq!(key(&Monomial::<0>::one(), order), Some(0));
        assert!(key(&Monomial::<7>::univariate(0, 255), order).is_some());
    }
}
