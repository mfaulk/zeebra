/// Given a borrow/borrow `Sub`, implement the remaining variants of Sub and SubAssign.
#[macro_export]
macro_rules! impl_sub_variants {
    // Impl Sub variants for a type with generic type parameters,
    // e.g. impl_sub_variants!([T: Clone], Foo<T>)
    ([$($parm:tt)*], $type_:ty) => {
        // Foo - &Foo
        impl<'b, $($parm)*> core::ops::Sub<&'b $type_> for $type_ {
            type Output = $type_;
            fn sub(self, rhs: &'b $type_) -> Self::Output {
                &self - rhs
            }
        }

        // &Foo - Foo
        impl<'b, $($parm)*> core::ops::Sub<$type_> for &'b $type_ {
            type Output = $type_;
            fn sub(self, rhs: $type_) -> Self::Output {
                self - &rhs
            }
        }

        // Foo - Foo
        impl<$($parm)*> core::ops::Sub<$type_> for $type_ {
            type Output = $type_;
            fn sub(self, rhs: Self) -> Self::Output {
                &self - &rhs
            }
        }

        // &mut Foo - &mut Foo
        impl<$($parm)*> core::ops::Sub<&mut $type_> for &mut $type_ {
            type Output = $type_;
            fn sub(self, rhs: &mut $type_) -> Self::Output {
                &*self - &*rhs
            }
        }

        impl<$($parm)*> core::ops::SubAssign for $type_ {
            fn sub_assign(&mut self, rhs: $type_) {
                *self = &*self - &rhs;
            }
        }
    };

    // Impl Sub variants for a type without generic type parameters.
    // e.g. impl_sub_variants!(Foo)
    ($type_:ty) => {
        impl_sub_variants!([], $type_)
    };
}

#[cfg(test)]
mod tests {

    use core::ops::Sub;

    /// A struct without generic type parameters.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    struct Foo {
        x: u32,
    }

    impl Sub<&Foo> for &Foo {
        type Output = Foo;
        fn sub(self, rhs: &Foo) -> Self::Output {
            Foo { x: self.x - rhs.x }
        }
    }

    /// A struct with a generic type parameter.
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Bar<T: Clone> {
        x: Vec<T>,
    }

    /// Subbing concatenates the vectors. That's not very meaningful, but it doesn't really matter what the operation is.
    impl<T: Clone> Sub<&Bar<T>> for &Bar<T> {
        type Output = Bar<T>;
        fn sub(self, rhs: &Bar<T>) -> Self::Output {
            let mut x = self.x.clone();
            x.extend_from_slice(&rhs.x);
            Bar { x }
        }
    }

    #[test]
    // Should implement Sub variants for a type without generic type parameters.
    fn test_impl_sub_variants() {
        impl_sub_variants!(Foo);

        let a = Foo { x: 10 };
        let b = Foo { x: 2 };
        let c = Foo { x: 8 };
        assert_eq!(&a - &b, c);
        assert_eq!(a - &b, c);
        assert_eq!(&a - b, c);
        assert_eq!(a - b, c);

        let mut d = Foo { x: 33 };
        d -= a;
        assert_eq!(d, Foo { x: 23 })
    }

    #[test]
    // Should implement Sub variants for a type with generic type parameters.
    fn test_impl_sub_variants_with_params() {
        impl_sub_variants!([T: Clone], Bar<T>);
        let a = Bar { x: vec![1, 2] };
        let b = Bar { x: vec![3, 4] };
        let c = Bar {
            x: vec![1, 2, 3, 4],
        };
        assert_eq!(&a - &b, c);
        assert_eq!(a - &b, c);

        let mut d = Bar { x: vec![5, 6] };
        let e = Bar { x: vec![7, 8] };
        d -= e;
        assert_eq!(
            d,
            Bar {
                x: vec![5, 6, 7, 8]
            }
        )
    }
}
