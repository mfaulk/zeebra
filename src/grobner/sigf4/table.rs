//! The run-wide monomial table for symbolic preprocessing (#971, M33 candidate G2-1).
//!
//! One id per monomial for the whole run, in place of a fresh map per batch. The hash is additive
//! under multiplication, `h(a·b) = h(a) + h(b)` (Monagan & Pearce 2015 §2.1), so a product's hash
//! is two words added and its exponent vector is never rehashed. Each entry carries the batch it
//! was last seen in and its first-occurrence id there, so a batch's columns cost one probe per
//! term. Lookups compare the full exponent vector on a hash match, so the table is exact.

use crate::Monomial;

#[cfg(feature = "research-sigf4-replay")]
use crate::poly::MonomialMap;

use super::engine::NONE;

/// `splitmix64`'s output sequence from a fixed seed: one odd weight per variable.
const fn weights<const N: usize>() -> [u64; N] {
    let mut out = [0u64; N];
    let mut state: u64 = 0x2545_f491_4f6c_dd1d;
    let mut i = 0;
    while i < N {
        state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        out[i] = (z ^ (z >> 31)) | 1;
        i += 1;
    }
    out
}

/// The additive hash: the exponent vector dotted with fixed weights, modulo 2⁶⁴.
pub(super) fn hash<const N: usize>(m: &Monomial<N>) -> u64 {
    let w = const { &weights::<N>() };
    m.exponents.iter().zip(w).fold(0u64, |h, (&e, &w)| {
        h.wrapping_add(u64::from(e).wrapping_mul(w))
    })
}

struct Entry<const N: usize> {
    mono: Monomial<N>,
    hash: u64,
    /// The batch this monomial was last interned in, and its first-occurrence id there.
    stamp: u32,
    local: u32,
}

pub(super) struct MonomialTable<const N: usize> {
    entries: Vec<Entry<N>>,
    /// Per id, the engine's cached reducer search `(best, scanned)`; `(NONE, 0)` until searched.
    reducers: Vec<(u32, u32)>,
    /// Open addressing, linear probing: `0` empty, else the hash's low half over `id + 1`.
    slots: Vec<u64>,
    shift: u32,
    stamp: u32,
}

impl<const N: usize> Default for MonomialTable<N> {
    fn default() -> Self {
        const SLOTS: usize = 1 << 10;
        Self {
            entries: Vec::new(),
            reducers: Vec::new(),
            slots: vec![0; SLOTS],
            shift: 64 - SLOTS.trailing_zeros(),
            stamp: 0,
        }
    }
}

impl<const N: usize> MonomialTable<N> {
    #[cfg(test)]
    pub(super) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Heap bytes held: entries, reducer cache and slots.
    pub(super) fn bytes(&self) -> usize {
        self.entries.capacity() * size_of::<Entry<N>>()
            + self.reducers.capacity() * size_of::<(u32, u32)>()
            + self.slots.len() * size_of::<u64>()
    }

    pub(super) fn mono(&self, id: u32) -> &Monomial<N> {
        &self.entries[id as usize].mono
    }

    pub(super) fn hash_of(&self, id: u32) -> u64 {
        self.entries[id as usize].hash
    }

    pub(super) fn reducer(&self, id: u32) -> (u32, u32) {
        self.reducers[id as usize]
    }

    pub(super) fn set_reducer(&mut self, id: u32, cached: (u32, u32)) {
        self.reducers[id as usize] = cached;
    }

    /// Starts a batch: every monomial is new to it until interned.
    pub(super) fn begin_batch(&mut self) {
        self.stamp += 1;
    }

    /// `m`'s first-occurrence id in this batch, appending its table id to `work` on first sight.
    /// `h` must be `hash(&m)`.
    #[inline]
    pub(super) fn intern(&mut self, m: Monomial<N>, h: u64, work: &mut Vec<u32>) -> u32 {
        let id = self.find_or_insert(m, h);
        self.local(id, work)
    }

    /// [`Self::intern`] of `mult` times run-wide id `id`'s monomial (#1240). `hm` must be
    /// `hash(mult)`.
    #[inline]
    pub(super) fn intern_times(
        &mut self,
        id: u32,
        mult: &Monomial<N>,
        hm: u64,
        work: &mut Vec<u32>,
    ) -> u32 {
        let entry = &self.entries[id as usize];
        let (m, h) = (entry.mono * *mult, entry.hash.wrapping_add(hm));
        self.intern(m, h, work)
    }

    /// Run-wide id `id`'s first-occurrence id in this batch, appending it to `work` on first
    /// sight: [`Self::intern`] without the product's probe.
    #[inline]
    pub(super) fn local(&mut self, id: u32, work: &mut Vec<u32>) -> u32 {
        let stamp = self.stamp;
        let entry = &mut self.entries[id as usize];
        if entry.stamp != stamp {
            entry.stamp = stamp;
            entry.local = work.len() as u32;
            work.push(id);
        }
        entry.local
    }

    /// `m`'s run-wide id, inserting it if new. `h` must be `hash(&m)`.
    pub(super) fn find_or_insert(&mut self, m: Monomial<N>, h: u64) -> u32 {
        debug_assert_eq!(h, hash(&m), "an additive hash must match its monomial");
        let tag = h << 32;
        let mask = self.slots.len() - 1;
        let mut slot = self.home(h);
        loop {
            let s = self.slots[slot];
            if s == 0 {
                break;
            }
            if s & !0xffff_ffff == tag {
                let id = (s as u32) - 1;
                if self.entries[id as usize].mono == m {
                    return id;
                }
            }
            slot = (slot + 1) & mask;
        }
        let id = self.entries.len() as u32;
        assert!(id < NONE - 1, "a run interns fewer than 2³² − 2 monomials");
        self.entries.push(Entry {
            mono: m,
            hash: h,
            stamp: 0,
            local: 0,
        });
        self.reducers.push((NONE, 0));
        self.slots[slot] = tag | u64::from(id + 1);
        if 2 * self.entries.len() > self.slots.len() {
            self.grow();
        }
        id
    }

    /// Fibonacci hashing: the top bits of an odd multiple, which depend on every bit of `h`.
    #[inline]
    fn home(&self, h: u64) -> usize {
        (h.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> self.shift) as usize
    }

    fn grow(&mut self) {
        let size = self.slots.len() * 2;
        self.slots = vec![0; size];
        self.shift -= 1;
        let mask = size - 1;
        for (id, entry) in self.entries.iter().enumerate() {
            let mut slot = self.home(entry.hash);
            while self.slots[slot] != 0 {
                slot = (slot + 1) & mask;
            }
            self.slots[slot] = (entry.hash << 32) | (id as u64 + 1);
        }
    }

    /// The reducer cache as the replay harness keys it: searched monomials only.
    #[cfg(feature = "research-sigf4-replay")]
    pub(super) fn reducer_map(&self) -> MonomialMap<N, (u32, u32)> {
        self.entries
            .iter()
            .zip(&self.reducers)
            .filter(|(_, r)| r.1 > 0)
            .map(|(e, r)| (e.mono, *r))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::{hash, MonomialTable};
    use crate::Monomial;

    fn m(e: [u32; 4]) -> Monomial<4> {
        Monomial::new(&e)
    }

    /// The hash of a product is the wrapping sum of its factors' hashes.
    #[test]
    fn test_hash_is_additive_under_multiplication() {
        let (a, b) = (m([3, 0, 7, 1]), m([0, 5, 2, 9]));
        assert_eq!(hash(&(a * b)), hash(&a).wrapping_add(hash(&b)));
        assert_eq!(hash(&Monomial::<4>::one()), 0);
        assert_ne!(hash(&m([1, 0, 0, 0])), hash(&m([0, 1, 0, 0])));
    }

    /// A monomial keeps one id for the run, across batches and table growth.
    #[test]
    fn test_ids_are_stable_across_batches_and_growth() {
        let mut table = MonomialTable::<4>::default();
        let mut ids = Vec::new();
        for i in 0..5_000u32 {
            let x = m([i % 17, i / 17 % 13, i / 221, 1]);
            ids.push((x, table.find_or_insert(x, hash(&x))));
        }
        assert_eq!(table.len(), 5_000);
        for (x, id) in ids {
            assert_eq!(table.find_or_insert(x, hash(&x)), id);
            assert_eq!(*table.mono(id), x);
            assert_eq!(table.hash_of(id), hash(&x));
        }
    }

    /// Batch-local ids are first-occurrence order within a batch and restart in the next.
    #[test]
    fn test_batch_local_ids_restart_per_batch() {
        let mut table = MonomialTable::<4>::default();
        let (a, b, c) = (m([1, 0, 0, 0]), m([0, 1, 0, 0]), m([0, 0, 1, 0]));
        table.begin_batch();
        let mut work = Vec::new();
        let first: Vec<u32> = [a, b, a, c, b]
            .iter()
            .map(|x| table.intern(*x, hash(x), &mut work))
            .collect();
        assert_eq!(first, [0, 1, 0, 2, 1]);
        assert_eq!(work.len(), 3);
        table.begin_batch();
        let mut work = Vec::new();
        let second: Vec<u32> = [c, a]
            .iter()
            .map(|x| table.intern(*x, hash(x), &mut work))
            .collect();
        assert_eq!(second, [0, 1]);
        assert_eq!(work, [table.find_or_insert(c, hash(&c)), 0]);
    }

    /// Distinct monomials get distinct ids, and each id's reducer cache starts unsearched.
    #[test]
    fn test_distinct_monomials_get_distinct_ids_and_empty_caches() {
        let mut table = MonomialTable::<4>::default();
        let (a, b) = (m([2, 0, 0, 0]), m([0, 0, 0, 3]));
        let (ia, ib) = (
            table.find_or_insert(a, hash(&a)),
            table.find_or_insert(b, hash(&b)),
        );
        assert_ne!(ia, ib);
        assert_eq!(table.reducer(ia), (super::NONE, 0));
        table.set_reducer(ib, (4, 9));
        assert_eq!(table.reducer(ib), (4, 9));
    }
}
