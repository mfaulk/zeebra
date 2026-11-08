//! A short divisor mask over monomials, built to be **counted rather than used** (#331).
//!
//! msolve answers divisibility mask-first — one AND and one branch against a 32-bit summary — and
//! falls through to the exponent comparison only when the mask cannot decide (`hash.c:486-489`,
//! read in `docs/research/msolve-implementation.md` §1.2). Whether that pays here is a question
//! about Zeebra's divisibility tests, not about msolve's, so this module builds the mask and
//! reports what it *would* have decided; nothing in the solver's answer depends on it.
//!
//! **Soundness is the one property that matters and it does not depend on the calibration.** A bit
//! stands for "this variable's exponent is at least `t`". If the divisor has it and the dividend
//! does not, then `divisor_i >= t > dividend_i`, so the divisor cannot divide — whatever `t` is. A
//! mask can therefore only ever report *not divisible*, and a badly calibrated one is merely
//! uninformative. [`DivmaskCalibration::rejects`] is that test and
//! `test_the_mask_never_rejects_a_true_divisor` is the check.
//!
//! The thresholds are read off the input system rather than fixed, which is msolve's choice and
//! the interesting half of it: a fixed threshold spends its bits on exponent ranges the instance
//! does not have.

use crate::Monomial;

/// Bits in one mask. 32 because that is `sdm_t`, and because the counters exist to be compared
/// against msolve's own reported behaviour.
pub const DIVMASK_BITS: usize = 32;

/// Exponent thresholds per variable, calibrated once from a system's monomials.
///
/// `DIVMASK_BITS / N` bits per variable, so the mask is uninformative — permanently zero, hence
/// deciding nothing — above 32 variables. That is recorded rather than worked around: the measured
/// answer for a 32-variable system under a 32-bit mask is that it does not apply, and widening the
/// mask is a different experiment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DivmaskCalibration<const N: usize> {
    /// Bits assigned to each variable; `0` when `N > DIVMASK_BITS`.
    bits_per_variable: usize,

    /// `thresholds[i][k]` is the exponent at which variable `i`'s bit `k` turns on, ascending.
    ///
    /// Flattened to `N * bits_per_variable`, which is at most 32.
    thresholds: Vec<u32>,
}

impl<const N: usize> DivmaskCalibration<N> {
    /// Thresholds from the exponents these monomials actually use.
    ///
    /// Per variable, msolve's rule (`hash.c:460-464`): split the measured range into
    /// `bits_per_variable` steps and put a bit at each step boundary, with a step of at least one
    /// so that a variable of constant exponent still gets distinct thresholds. An empty input
    /// calibrates to all-zero ranges, which is a mask that decides nothing — the honest answer when
    /// there is nothing to calibrate against.
    pub fn calibrate<'a>(monomials: impl IntoIterator<Item = &'a Monomial<N>>) -> Self {
        let bits_per_variable = DIVMASK_BITS / N.max(1);
        if bits_per_variable == 0 {
            return Self {
                bits_per_variable: 0,
                thresholds: Vec::new(),
            };
        }

        let mut minimum = [u32::MAX; N];
        let mut maximum = [0u32; N];
        let mut seen = false;
        for monomial in monomials {
            seen = true;
            for (variable, exponent) in monomial.exponents().iter().enumerate() {
                minimum[variable] = minimum[variable].min(*exponent);
                maximum[variable] = maximum[variable].max(*exponent);
            }
        }
        if !seen {
            minimum = [0; N];
        }

        let mut thresholds = Vec::with_capacity(N * bits_per_variable);
        for variable in 0..N {
            let span = maximum[variable].saturating_sub(minimum[variable]);
            let step = (span / bits_per_variable as u32).max(1);
            for bit in 0..bits_per_variable as u32 {
                thresholds.push(minimum[variable].saturating_add(step * (bit + 1)));
            }
        }
        Self {
            bits_per_variable,
            thresholds,
        }
    }

    /// Whether this calibration can decide anything at all.
    ///
    /// False only above 32 variables, where there is no bit to give a variable. Reported so that a
    /// run whose mask is structurally empty is not read as a run whose mask found nothing.
    pub fn is_informative(&self) -> bool {
        self.bits_per_variable > 0
    }

    /// The mask of one monomial: bit `(i, k)` set when exponent `i` reaches threshold `k`.
    pub fn mask(&self, monomial: &Monomial<N>) -> u32 {
        if self.bits_per_variable == 0 {
            return 0;
        }
        let mut mask = 0u32;
        let mut bit = 0;
        for (variable, exponent) in monomial.exponents().iter().enumerate() {
            for offset in 0..self.bits_per_variable {
                if *exponent >= self.thresholds[variable * self.bits_per_variable + offset] {
                    mask |= 1 << bit;
                }
                bit += 1;
            }
        }
        mask
    }

    /// Whether the masks alone prove `divisor` does not divide `dividend`.
    ///
    /// msolve's `hd[b].sdm & ~hd[a].sdm` with `b` the divisor. One-sided: `false` means the mask
    /// could not decide, never that the divisor divides.
    pub fn rejects(&self, divisor_mask: u32, dividend_mask: u32) -> bool {
        divisor_mask & !dividend_mask != 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn monomial<const N: usize>(exponents: &[u32]) -> Monomial<N> {
        Monomial::<N>::new(exponents)
    }

    /// A mask never rejects a divisor that really divides, at any calibration.
    #[test]
    fn test_the_mask_never_rejects_a_true_divisor() {
        // Calibrated on a deliberately narrow range, then exercised over a wider one, so the
        // thresholds are wrong for most of the pairs tested and soundness still has to hold.
        let calibration = DivmaskCalibration::<3>::calibrate(
            [monomial::<3>(&[0, 1, 2]), monomial::<3>(&[3, 0, 1])].iter(),
        );
        for a in 0..6u32 {
            for b in 0..6u32 {
                for c in 0..6u32 {
                    let dividend = monomial::<3>(&[a, b, c]);
                    let dividend_mask = calibration.mask(&dividend);
                    for x in 0..=a {
                        for y in 0..=b {
                            for z in 0..=c {
                                let divisor = monomial::<3>(&[x, y, z]);
                                assert!(
                                    !calibration.rejects(calibration.mask(&divisor), dividend_mask),
                                    "{divisor} divides {dividend} and the mask rejected it"
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    /// The mask decides a non-divisor whose excess exponent crosses a calibrated threshold.
    #[test]
    fn test_the_mask_decides_an_excess_above_a_threshold() {
        let calibration = DivmaskCalibration::<2>::calibrate(
            [monomial::<2>(&[0, 0]), monomial::<2>(&[16, 16])].iter(),
        );
        let dividend = monomial::<2>(&[1, 1]);
        let divisor = monomial::<2>(&[16, 0]);
        assert!(calibration.rejects(calibration.mask(&divisor), calibration.mask(&dividend)));
    }

    /// Thresholds follow the input's range: the same pair is decided under one calibration and not
    /// under another, which is the whole claim for calibrating rather than fixing them.
    #[test]
    fn test_the_calibration_changes_what_the_mask_can_decide() {
        let dividend = monomial::<2>(&[1, 0]);
        let divisor = monomial::<2>(&[2, 0]);

        let narrow = DivmaskCalibration::<2>::calibrate(
            [monomial::<2>(&[0, 0]), monomial::<2>(&[2, 2])].iter(),
        );
        assert!(narrow.rejects(narrow.mask(&divisor), narrow.mask(&dividend)));

        let wide = DivmaskCalibration::<2>::calibrate(
            [monomial::<2>(&[0, 0]), monomial::<2>(&[4096, 4096])].iter(),
        );
        assert!(
            !wide.rejects(wide.mask(&divisor), wide.mask(&dividend)),
            "every threshold is above 2, so the two monomials have identical masks"
        );
    }

    /// Above 32 variables there is no bit per variable, and the calibration says so rather than
    /// silently reporting a mask that decides nothing.
    #[test]
    fn test_a_mask_is_uninformative_above_thirty_two_variables() {
        let calibration = DivmaskCalibration::<33>::calibrate([monomial::<33>(&[7; 33])].iter());
        assert!(!calibration.is_informative());
        assert_eq!(calibration.mask(&monomial::<33>(&[7; 33])), 0);
    }

    /// Calibrating on nothing yields a mask that decides nothing, rather than panicking.
    #[test]
    fn test_an_empty_calibration_decides_nothing() {
        let calibration = DivmaskCalibration::<4>::calibrate(std::iter::empty());
        assert!(calibration.is_informative());
        let a = calibration.mask(&monomial::<4>(&[0, 0, 0, 0]));
        let b = calibration.mask(&monomial::<4>(&[9, 9, 9, 9]));
        assert!(!calibration.rejects(a, b));
    }
}
