//! Shifted Schreyer signatures `lm(f_i)·t ⊗ i` (Lairez Remark 25): comparing two is one monomial
//! comparison and an index tie-break, and `S | T` is monomial divisibility at equal index.

use std::cmp::Ordering;

use crate::{poly::MonomialOrder, Monomial};

/// A module term in shifted form: `mono = t·lm(f_index)` stands for `t·e_index`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Signature<const N: usize> {
    pub mono: Monomial<N>,
    pub index: u32,
}

impl<const N: usize> Signature<N> {
    pub fn new(mono: Monomial<N>, index: u32) -> Self {
        Self { mono, index }
    }

    /// Schreyer (`<lt-pot`) order: shifted monomial first, then index.
    pub fn cmp_in(&self, other: &Self, order: MonomialOrder) -> Ordering {
        order
            .cmp(&self.mono, &other.mono)
            .then(self.index.cmp(&other.index))
    }

    pub fn divides(&self, other: &Self) -> bool {
        self.index == other.index && divides(&self.mono, &other.mono)
    }

    pub fn times(&self, t: &Monomial<N>) -> Self {
        Self::new(self.mono * t, self.index)
    }

    pub fn degree(&self) -> u64 {
        self.mono.degree()
    }
}

/// `a | b`, without allocating the quotient.
pub fn divides<const N: usize>(a: &Monomial<N>, b: &Monomial<N>) -> bool {
    a.exponents().iter().zip(b.exponents()).all(|(x, y)| x <= y)
}

/// A 64-bit divisibility filter: bit `k` of variable `v`'s band is set when `x_v^{k+1}` divides.
///
/// Not `f4::divmask`'s 32-bit calibrated mask: shifted signatures outgrow any calibration taken
/// from the input, and at `N = 12` the wider band keeps five exponent levels per variable.
pub fn mask<const N: usize>(m: &Monomial<N>) -> u64 {
    let band = (64 / N.max(1)).max(1);
    let mut mask = 0u64;
    for (v, &e) in m.exponents().iter().enumerate().take(64) {
        let levels = (e as usize).min(band);
        for k in 0..levels {
            let bit = v * band + k;
            if bit < 64 {
                mask |= 1 << bit;
            }
        }
    }
    mask
}

/// Where a syzygy signature came from (plan §2.2 asks for rejections by mechanism).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SyzygySource {
    /// `lm(β)·s(α)` or `lm(α)·s(β)`, the larger, from a pair of basis elements (EF Def 6.2).
    Koszul,
    /// A row that reduced to zero (EF Thm 5.3; RFC T6).
    ZeroRow,
}

#[derive(Clone, Debug)]
struct Entry<const N: usize> {
    mono: Monomial<N>,
    mask: u64,
    source: SyzygySource,
}

/// Minimal generators of the known syzygy signatures, bucketed by index.
#[derive(Clone, Debug)]
pub struct SyzygyStore<const N: usize> {
    buckets: Vec<Vec<Entry<N>>>,
    len: usize,
}

impl<const N: usize> SyzygyStore<N> {
    pub fn new(indices: usize) -> Self {
        Self {
            buckets: vec![Vec::new(); indices],
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The source of a stored signature dividing `t`, if any.
    pub fn covering(&self, t: &Signature<N>) -> Option<SyzygySource> {
        let m = mask(&t.mono);
        self.buckets[t.index as usize]
            .iter()
            .find(|e| e.mask & !m == 0 && divides(&e.mono, &t.mono))
            .map(|e| e.source)
    }

    /// Insert `s` unless it is already covered; drops entries `s` divides. True if kept.
    pub fn insert(&mut self, s: Signature<N>, source: SyzygySource) -> bool {
        if self.covering(&s).is_some() {
            return false;
        }
        let m = mask(&s.mono);
        let bucket = &mut self.buckets[s.index as usize];
        let before = bucket.len();
        bucket.retain(|e| !(m & !e.mask == 0 && divides(&s.mono, &e.mono)));
        self.len -= before - bucket.len();
        bucket.push(Entry {
            mono: s.mono,
            mask: m,
            source,
        });
        self.len += 1;
        true
    }
}
