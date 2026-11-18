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
    let full = if band >= 64 {
        u64::MAX
    } else {
        (1u64 << band) - 1
    };
    let mut mask = 0u64;
    for (v, &e) in m.exponents().iter().enumerate().take(64) {
        let shift = v * band;
        if shift >= 64 {
            break;
        }
        let levels = (e as usize).min(band);
        let bits = if levels >= 64 {
            full
        } else {
            (1u64 << levels) - 1
        };
        mask |= bits << shift;
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

/// One index's minimal syzygy signatures in insertion order, masks apart from monomials so the
/// filter scans eight bytes per entry rather than the whole entry.
#[derive(Clone, Debug, Default)]
struct Bucket<const N: usize> {
    masks: Vec<u64>,
    monos: Vec<Monomial<N>>,
    sources: Vec<SyzygySource>,
}

impl<const N: usize> Bucket<N> {
    /// The first entry, in insertion order, dividing `mono` (whose mask is `m`).
    fn first_dividing(&self, mono: &Monomial<N>, m: u64) -> Option<usize> {
        first_hit(
            &self.masks,
            |e| e & !m == 0,
            |k| divides(&self.monos[k], mono),
        )
    }
}

/// The first `k` in order with `filter(masks[k])` and `confirm(k)`. The filter is evaluated
/// eight masks at a time into a hit word, which the compiler vectorizes; only hits are confirmed.
fn first_hit(
    masks: &[u64],
    filter: impl Fn(u64) -> bool,
    mut confirm: impl FnMut(usize) -> bool,
) -> Option<usize> {
    const LANES: usize = 8;
    let (chunks, remainder) = masks.as_chunks::<LANES>();
    let mut base = 0;
    for chunk in chunks {
        let mut hits = 0u32;
        for (j, &e) in chunk.iter().enumerate() {
            hits |= u32::from(filter(e)) << j;
        }
        while hits != 0 {
            let k = base + hits.trailing_zeros() as usize;
            if confirm(k) {
                return Some(k);
            }
            hits &= hits - 1;
        }
        base += LANES;
    }
    remainder
        .iter()
        .enumerate()
        .find(|&(j, &e)| filter(e) && confirm(base + j))
        .map(|(j, _)| base + j)
}

/// Minimal generators of the known syzygy signatures, bucketed by index.
#[derive(Clone, Debug)]
pub struct SyzygyStore<const N: usize> {
    buckets: Vec<Bucket<N>>,
    len: usize,
}

impl<const N: usize> SyzygyStore<N> {
    pub fn new(indices: usize) -> Self {
        Self {
            buckets: vec![Bucket::default(); indices],
            len: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The source of the earliest-inserted stored signature dividing `t`, if any. Earliest, so
    /// the rejection counts by mechanism do not depend on the store's layout.
    pub fn covering(&self, t: &Signature<N>) -> Option<SyzygySource> {
        self.covering_masked(t, mask(&t.mono))
    }

    fn covering_masked(&self, t: &Signature<N>, m: u64) -> Option<SyzygySource> {
        let bucket = &self.buckets[t.index as usize];
        bucket.first_dividing(&t.mono, m).map(|k| bucket.sources[k])
    }

    /// Insert `s` unless it is already covered; drops entries `s` divides. True if kept.
    pub fn insert(&mut self, s: Signature<N>, source: SyzygySource) -> bool {
        let m = mask(&s.mono);
        if self.covering_masked(&s, m).is_some() {
            return false;
        }
        let bucket = &mut self.buckets[s.index as usize];
        let before = bucket.masks.len();
        let dropped = |bucket: &Bucket<N>, k: usize| {
            m & !bucket.masks[k] == 0 && divides(&s.mono, &bucket.monos[k])
        };
        let first = first_hit(
            &bucket.masks,
            |e| m & !e == 0,
            |k| divides(&s.mono, &bucket.monos[k]),
        );
        if let Some(first) = first {
            let mut kept = first;
            for k in first + 1..before {
                if !dropped(bucket, k) {
                    bucket.masks.swap(kept, k);
                    bucket.monos.swap(kept, k);
                    bucket.sources.swap(kept, k);
                    kept += 1;
                }
            }
            bucket.masks.truncate(kept);
            bucket.monos.truncate(kept);
            bucket.sources.truncate(kept);
            self.len -= before - kept;
        }
        bucket.masks.push(m);
        bucket.monos.push(s.mono);
        bucket.sources.push(source);
        self.len += 1;
        true
    }
}
