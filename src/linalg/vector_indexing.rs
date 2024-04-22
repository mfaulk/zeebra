//! Index the elements of a vector.

use crate::{linalg::vector::Vector, Ring};
use std::{
    ops::{Index, IndexMut},
    slice::SliceIndex,
};

impl<T: Ring, Idx> Index<Idx> for Vector<T>
where
    Idx: SliceIndex<[T]>,
{
    type Output = Idx::Output;

    fn index(&self, index: Idx) -> &Self::Output {
        &self.elements[index]
    }
}

impl<T: Ring, Idx> IndexMut<Idx> for Vector<T>
where
    Idx: SliceIndex<[T]>,
{
    fn index_mut(&mut self, index: Idx) -> &mut <Idx as SliceIndex<[T]>>::Output {
        &mut self.elements[index]
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        fields::{FiniteField, Zp541},
        linalg::vector::Vector,
        One, Zero,
    };
    use proptest::prelude::*;

    const MAX_SIZE: usize = 10;

    proptest! {
        #[test]
        fn test_indexing(v in (1..=MAX_SIZE).prop_flat_map(any_with::<Vector::<Zp541>>)) {
            for i in 0..v.len() {
                assert_eq!(v[i], v.elements[i]);
            }
        }
    }

    #[test]
    fn test_indexing_by_range() {
        let v = Vector::new(&[Zp541::ONE, Zp541::ZERO, Zp541::ONE]);
        assert_eq!(v[0..2], [Zp541::ONE, Zp541::ZERO]);
    }

    proptest! {
        #[test]
        fn test_indexing_mut(mut v in (1..=MAX_SIZE).prop_flat_map(any_with::<Vector::<Zp541>>)) {
            for i in 0..v.len() {
                v[i] = Zp541::new(i as u64);
                assert_eq!(v[i], Zp541::new(i as u64));
            }
        }
    }

    #[test]
    fn test_indexing_mut_by_range() {
        let mut v = Vector::new(&[Zp541::ONE, Zp541::ZERO, Zp541::ONE]);
        v[1..=2].iter_mut().for_each(|x| *x = Zp541::new(7));
        let expected = Vector::new(&[Zp541::ONE, Zp541::new(7), Zp541::new(7)]);
        assert_eq!(v, expected);
    }
}
