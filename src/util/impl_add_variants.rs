/// Given a borrow/borrow `Add`, implement the remaining variants of Add and AddAssign.
#[macro_export]
macro_rules! impl_add_variants {
    // TODO: Impl Add variants for Foo + Bar, with generic type parameters.

    // Impl Add variants for a type with generic type parameters,
    // e.g. impl_add_variants!([T: Clone], Foo<T>)
    ([$($parm:tt)*], $type_:ty) => {
        // Foo + &Foo
        impl<'b, $($parm)*> core::ops::Add<&'b $type_> for $type_ {
            type Output = $type_;
            fn add(self, rhs: &'b $type_) -> Self::Output {
                &self + rhs
            }
        }

        // &Foo + Foo
        impl<'b, $($parm)*> core::ops::Add<$type_> for &'b $type_ {
            type Output = $type_;
            fn add(self, rhs: $type_) -> Self::Output {
                self + &rhs
            }
        }

        // Foo + Foo
        impl<$($parm)*> core::ops::Add<$type_> for $type_ {
            type Output = $type_;
            fn add(self, rhs: Self) -> Self::Output {
                &self + &rhs
            }
        }

        // &mut Foo + &mut Foo
        impl<$($parm)*> core::ops::Add<&mut $type_> for &mut $type_ {
            type Output = $type_;
            fn add(self, rhs: &mut $type_) -> Self::Output {
                &*self + &*rhs
            }
        }

        // &mut Foo += Foo
        impl<$($parm)*> core::ops::AddAssign for $type_ {
            fn add_assign(&mut self, rhs: $type_) {
                *self = &*self + &rhs;
            }
        }

        // &mut Foo += &Foo
        impl<'b, $($parm)*> core::ops::AddAssign<&'b $type_> for $type_ {
            fn add_assign(&mut self, rhs: &'b $type_) {
                *self = &*self + rhs;
            }
        }

    };

    // Impl Add variants for a type without generic type parameters.
    // e.g. impl_add_variants!(Foo)
    ($type_:ty) => {
        impl_add_variants!([], $type_)
    };
}

#[cfg(test)]
mod tests {

    use core::ops::Add;

    /// A struct without generic type parameters.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    struct Foo {
        x: u32,
    }

    impl Add<&Foo> for &Foo {
        type Output = Foo;
        fn add(self, rhs: &Foo) -> Self::Output {
            Foo { x: self.x + rhs.x }
        }
    }

    /// A struct with a generic type parameter.
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Bar<T: Clone> {
        x: Vec<T>,
    }

    /// Adding concatenates the vectors.
    impl<T: Clone> Add<&Bar<T>> for &Bar<T> {
        type Output = Bar<T>;
        fn add(self, rhs: &Bar<T>) -> Self::Output {
            let mut x = self.x.clone();
            x.extend_from_slice(&rhs.x);
            Bar { x }
        }
    }

    #[test]
    // Should implement Add variants for a type without generic type parameters.
    fn test_impl_add_variants() {
        impl_add_variants!(Foo);

        let a = Foo { x: 1 };
        let b = Foo { x: 2 };
        let c = Foo { x: 3 };
        assert_eq!(&a + &b, c);
        assert_eq!(a + &b, c);
        assert_eq!(&a + b, c);
        assert_eq!(a + b, c);

        let mut d = Foo { x: 4 };
        d += a;
        assert_eq!(d, Foo { x: 5 })
    }

    #[test]
    // Should implement Add variants for a type with generic type parameters.
    fn test_impl_add_variants_with_params() {
        impl_add_variants!([T: Clone], Bar<T>);
        let a = Bar { x: vec![1, 2] };
        let b = Bar { x: vec![3, 4] };
        let c = Bar {
            x: vec![1, 2, 3, 4],
        };
        assert_eq!(&a + &b, c);
        assert_eq!(a + &b, c);

        let mut d = Bar { x: vec![5, 6] };
        let e = Bar { x: vec![7, 8] };
        d += e;
        assert_eq!(
            d,
            Bar {
                x: vec![5, 6, 7, 8]
            }
        )
    }
}
