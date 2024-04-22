use crate::integers::num_digits;
use std::cmp::{max, Ordering};

pub fn multi_word_cmp(a: &[u64], b: &[u64]) -> Ordering {
    // Ignore higher-order zero digits.
    let a = &a[0..num_digits(a)];
    let b = &b[0..num_digits(b)];

    // Compare each digit, most-significant first.
    for i in (0..max(a.len(), b.len())).rev() {
        let a_i = a.get(i).unwrap_or(&0u64);
        let b_i = b.get(i).unwrap_or(&0u64);
        let ordering = a_i.cmp(b_i);
        if ordering != Ordering::Equal {
            return ordering;
        }
    }
    Ordering::Equal
}

#[cfg(test)]
mod tests {
    use crate::integers::{big_integers::multi_word_cmp::multi_word_cmp, sample_n_words};
    use rand::thread_rng;
    use std::cmp::Ordering;

    #[test]
    fn test_equal() {
        for n in 1..13 {
            let mut rng = thread_rng();
            let a = sample_n_words(n, &mut rng);
            assert_eq!(multi_word_cmp(&a, &a), Ordering::Equal);
        }
    }

    #[test]
    fn test_unequal_lengths() {
        let a = [1, 1, 1, 1, 2];
        let b = [2, 2, 2, 2];
        assert_eq!(multi_word_cmp(&a, &b), Ordering::Greater);
        assert_eq!(multi_word_cmp(&b, &a), Ordering::Less);
    }
}
