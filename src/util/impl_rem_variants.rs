/// Given a borrow/borrow `Rem`, implement the remaining variants of Rem and RemAssign.
#[macro_export]
macro_rules! impl_rem_variants {
    // Impl Rem variants for a type with generic type parameters,
    // e.g. impl_rem_variants!([T: Clone], Foo<T>)
    ([$($parm:tt)*], $type_:ty) => {
        // Foo % &Foo
        impl<'b, $($parm)*> core::ops::Rem<&'b $type_> for $type_ {
            type Output = $type_;
            fn rem(self, rhs: &'b $type_) -> Self::Output {
                &self % rhs
            }
        }

        // &Foo % Foo
        impl<'b, $($parm)*> core::ops::Rem<$type_> for &'b $type_ {
            type Output = $type_;
            fn rem(self, rhs: $type_) -> Self::Output {
                self % &rhs
            }
        }

        // Foo % Foo
        impl<$($parm)*> core::ops::Rem<$type_> for $type_ {
            type Output = $type_;
            fn rem(self, rhs: Self) -> Self::Output {
                &self % &rhs
            }
        }

        // &mut Foo % &mut Foo
        impl<$($parm)*> core::ops::Rem<&mut $type_> for &mut $type_ {
            type Output = $type_;
            fn rem(self, rhs: &mut $type_) -> Self::Output {
                &*self % &*rhs
            }
        }

        impl<$($parm)*> core::ops::RemAssign for $type_ {
            fn rem_assign(&mut self, rhs: $type_) {
                *self = &*self % &rhs;
            }
        }
    };

    // Impl Rem variants for a type without generic type parameters.
    // e.g. impl_rem_variants!(Foo)
    ($type_:ty) => {
        impl_rem_variants!([], $type_)
    };
}

#[cfg(test)]
mod tests {

    use core::ops::Rem;

    /// A struct without generic type parameters.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    struct Foo {
        x: u32,
    }

    impl Rem<&Foo> for &Foo {
        type Output = Foo;
        fn rem(self, rhs: &Foo) -> Self::Output {
            Foo { x: self.x % rhs.x }
        }
    }

    /// A struct with a generic type parameter.
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Bar<T: Clone> {
        x: Vec<T>,
    }

    /// Taking the remainder truncates the left vector to the right one's length.
    impl<T: Clone> Rem<&Bar<T>> for &Bar<T> {
        type Output = Bar<T>;
        fn rem(self, rhs: &Bar<T>) -> Self::Output {
            Bar {
                x: self.x[..rhs.x.len().min(self.x.len())].to_vec(),
            }
        }
    }

    #[test]
    // Should implement Rem variants for a type without generic type parameters.
    fn test_impl_rem_variants() {
        impl_rem_variants!(Foo);

        let a = Foo { x: 32 };
        let b = Foo { x: 5 };
        let c = Foo { x: 2 };
        assert_eq!(&a % &b, c);
        assert_eq!(a % &b, c);
        assert_eq!(&a % b, c);
        assert_eq!(a % b, c);

        let mut d = Foo { x: 67 };
        d %= Foo { x: 11 };
        assert_eq!(d, Foo { x: 1 })
    }

    #[test]
    // Should implement Rem variants for a type with generic type parameters.
    fn test_impl_rem_variants_with_params() {
        impl_rem_variants!([T: Clone], Bar<T>);
        let a = Bar { x: vec![1, 2, 3] };
        let b = Bar { x: vec![4, 5] };
        let c = Bar { x: vec![1, 2] };
        assert_eq!(&a % &b, c);
        assert_eq!(a % &b, c);

        let mut d = Bar { x: vec![5, 6, 7] };
        d %= Bar { x: vec![8] };
        assert_eq!(d, Bar { x: vec![5] })
    }
}
