/// Given a borrow/borrow `Mul`, implement the remaining variants of Mul and MulAssign.
#[macro_export]
macro_rules! impl_mul_variants {
    // TODO: Impl Mul variants for Foo * Bar, with generic type parameters.

    // Impl Mul variants for a type with generic type parameters,
    // e.g. impl_mul_variants!([T: Clone], Foo<T>)
    ([$($parm:tt)*], $type_:ty) => {
        // Foo * &Foo
        impl<'b, $($parm)*> core::ops::Mul<&'b $type_> for $type_ {
            type Output = $type_;
            fn mul(self, rhs: &'b $type_) -> Self::Output {
                &self * rhs
            }
        }

        // &Foo * Foo
        impl<'b, $($parm)*> core::ops::Mul<$type_> for &'b $type_ {
            type Output = $type_;
            fn mul(self, rhs: $type_) -> Self::Output {
                self * &rhs
            }
        }

        // Foo * Foo
        impl<$($parm)*> core::ops::Mul<$type_> for $type_ {
            type Output = $type_;
            fn mul(self, rhs: Self) -> Self::Output {
                &self * &rhs
            }
        }

        // &mut Foo * &mut Foo
        impl<$($parm)*> core::ops::Mul<&mut $type_> for &mut $type_ {
            type Output = $type_;
            fn mul(self, rhs: &mut $type_) -> Self::Output {
                &*self * &*rhs
            }
        }

        impl<$($parm)*> core::ops::MulAssign for $type_ {
            fn mul_assign(&mut self, rhs: $type_) {
                *self = &*self * &rhs;
            }
        }
    };

    // Impl Mul variants for a type without generic type parameters.
    // e.g. impl_mul_variants!(Foo)
    ($type_:ty) => {
        impl_mul_variants!([], $type_)
    };
}

#[cfg(test)]
mod tests {

    use core::ops::Mul;

    /// A struct without generic type parameters.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    struct Foo {
        x: u32,
    }

    impl Mul<&Foo> for &Foo {
        type Output = Foo;
        fn mul(self, rhs: &Foo) -> Self::Output {
            Foo { x: self.x * rhs.x }
        }
    }

    /// A struct with a generic type parameter.
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Bar<T: Clone> {
        x: Vec<T>,
    }

    /// Muling concatenates the vectors.
    impl<T: Clone> Mul<&Bar<T>> for &Bar<T> {
        type Output = Bar<T>;
        fn mul(self, rhs: &Bar<T>) -> Self::Output {
            let mut x = self.x.clone();
            x.extend_from_slice(&rhs.x);
            Bar { x }
        }
    }

    #[test]
    // Should implement Mul variants for a type without generic type parameters.
    fn test_impl_mul_variants() {
        impl_mul_variants!(Foo);

        let a = Foo { x: 2 };
        let b = Foo { x: 3 };
        let c = Foo { x: 6 };
        assert_eq!(&a * &b, c);
        assert_eq!(a * &b, c);
        assert_eq!(&a * b, c);
        assert_eq!(a * b, c);

        let mut d = Foo { x: 4 };
        let e = Foo { x: 5 };
        d *= e;
        assert_eq!(d, Foo { x: 20 });
    }

    #[test]
    // Should implement Mul variants for a type with generic type parameters.
    fn test_impl_mul_variants_with_params() {
        impl_mul_variants!([T: Clone], Bar<T>);
        let a = Bar { x: vec![1, 2] };
        let b = Bar { x: vec![3, 4] };
        let c = Bar {
            x: vec![1, 2, 3, 4],
        };
        assert_eq!(&a * &b, c);
        assert_eq!(a * &b, c);

        let mut d = Bar { x: vec![5, 6] };
        let e = Bar { x: vec![7, 8] };
        d *= e;
        assert_eq!(
            d,
            Bar {
                x: vec![5, 6, 7, 8]
            }
        )
    }
}
