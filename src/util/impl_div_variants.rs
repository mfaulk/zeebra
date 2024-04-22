/// Given a borrow/borrow `Div`, implement the remaining variants of Div and DivAssign.
#[macro_export]
macro_rules! impl_div_variants {
    // Impl Div variants for a type with generic type parameters,
    // e.g. impl_div_variants!([T: Clone], Foo<T>)
    ([$($parm:tt)*], $type_:ty) => {
        // Foo / &Foo
        impl<'b, $($parm)*> core::ops::Div<&'b $type_> for $type_ {
            type Output = $type_;
            fn div(self, rhs: &'b $type_) -> Self::Output {
                &self / rhs
            }
        }

        // &Foo / Foo
        impl<'b, $($parm)*> core::ops::Div<$type_> for &'b $type_ {
            type Output = $type_;
            fn div(self, rhs: $type_) -> Self::Output {
                self / &rhs
            }
        }

        // Foo / Foo
        impl<$($parm)*> core::ops::Div<$type_> for $type_ {
            type Output = $type_;
            fn div(self, rhs: Self) -> Self::Output {
                &self / &rhs
            }
        }

        // &mut Foo / &mut Foo
        impl<$($parm)*> core::ops::Div<&mut $type_> for &mut $type_ {
            type Output = $type_;
            fn div(self, rhs: &mut $type_) -> Self::Output {
                &*self / &*rhs
            }
        }

        impl<$($parm)*> core::ops::DivAssign for $type_ {
            fn div_assign(&mut self, rhs: $type_) {
                *self = &*self / &rhs;
            }
        }
    };

    // Impl Div variants for a type without generic type parameters.
    // e.g. impl_div_variants!(Foo)
    ($type_:ty) => {
        impl_div_variants!([], $type_)
    };
}

#[cfg(test)]
mod tests {

    use core::ops::Div;

    /// A struct without generic type parameters.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    struct Foo {
        x: u32,
    }

    impl Div<&Foo> for &Foo {
        type Output = Foo;
        fn div(self, rhs: &Foo) -> Self::Output {
            Foo { x: self.x / rhs.x }
        }
    }

    /// A struct with a generic type parameter.
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Bar<T: Clone> {
        x: Vec<T>,
    }

    /// Dividing concatenates the vectors.
    impl<T: Clone> Div<&Bar<T>> for &Bar<T> {
        type Output = Bar<T>;
        fn div(self, rhs: &Bar<T>) -> Self::Output {
            let mut x = self.x.clone();
            x.extend_from_slice(&rhs.x);
            Bar { x }
        }
    }

    #[test]
    // Should implement Div variants for a type without generic type parameters.
    fn test_impl_div_variants() {
        impl_div_variants!(Foo);

        let a = Foo { x: 30 };
        let b = Foo { x: 5 };
        let c = Foo { x: 6 };
        assert_eq!(&a / &b, c);
        assert_eq!(a / &b, c);
        assert_eq!(&a / b, c);
        assert_eq!(a / b, c);

        let mut d = Foo { x: 66 };
        d /= c;
        assert_eq!(d, Foo { x: 11 })
    }

    #[test]
    // Should implement Div variants for a type with generic type parameters.
    fn test_impl_div_variants_with_params() {
        impl_div_variants!([T: Clone], Bar<T>);
        let a = Bar { x: vec![1, 2] };
        let b = Bar { x: vec![3, 4] };
        let c = Bar {
            x: vec![1, 2, 3, 4],
        };
        assert_eq!(&a / &b, c);
        assert_eq!(a / &b, c);

        let mut d = Bar { x: vec![5, 6] };
        let e = Bar { x: vec![7, 8] };
        d /= e;
        assert_eq!(
            d,
            Bar {
                x: vec![5, 6, 7, 8]
            }
        )
    }
}
