//! `c * p` for the crate's containers, which the orphan rule will not let a blanket impl provide.
//!
//! `impl<F: FiniteField> Mul<DensePolynomial<F>> for F` is rejected: `F` is a type parameter, so
//! the `Self` type of that impl is not local and the compiler cannot know a downstream crate will
//! not write the same impl. The way round it is to put a **concrete local type** in the `Self`
//! position, which is what [`impl_left_scalar_mul!`] does — once per field *struct* rather than
//! once per field, since `PrimeFieldElement64<P>` is local for every `P` and so one invocation
//! covers every prime the crate names.
//!
//! `scale` stays as the route for code that is generic over `F`, because none of this is reachable
//! from a `F: FiniteField` bound.

/// Implement `scalar * container` in all four ownership combinations, for one container.
///
/// Requires all four right-hand spellings to exist; each impl here delegates to **the one with the
/// same ownership**, so the left-hand operators cannot disagree with the right-hand ones about the
/// answer *or* about what they allocate. `c * p` on an owned `p` reaches the spelling that scales
/// in place, which `&c * &p` could not.
#[macro_export]
#[doc(hidden)]
macro_rules! impl_left_scalar_mul_for {
    ([$($parm:tt)*], $field:ty, $container:ty) => {
        impl<'l, 'r, $($parm)*> core::ops::Mul<&'r $container> for &'l $field {
            type Output = $container;
            fn mul(self, rhs: &'r $container) -> Self::Output {
                rhs * self
            }
        }

        impl<'l, $($parm)*> core::ops::Mul<$container> for &'l $field {
            type Output = $container;
            fn mul(self, rhs: $container) -> Self::Output {
                rhs * self
            }
        }

        impl<'r, $($parm)*> core::ops::Mul<&'r $container> for $field {
            type Output = $container;
            fn mul(self, rhs: &'r $container) -> Self::Output {
                rhs * self
            }
        }

        impl<$($parm)*> core::ops::Mul<$container> for $field {
            type Output = $container;
            fn mul(self, rhs: $container) -> Self::Output {
                rhs * self
            }
        }
    };
}

/// Implement `c * p`, `c * m` and `c * v` for one concrete field type.
///
/// Invoked once per field element struct, with that struct's own generics as the first argument:
///
/// ```ignore
/// impl_left_scalar_mul!([const P: u64], zeebra::fields::PrimeFieldElement64<P>);
/// ```
///
/// Covers the univariate and multivariate polynomials, matrices and vectors. The multivariate arm
/// introduces its own `NN` because the variable count is a const generic of the container rather
/// than of the field.
#[macro_export]
macro_rules! impl_left_scalar_mul {
    ([$($parm:tt)*], $field:ty) => {
        $crate::impl_left_scalar_mul_for!(
            [$($parm)*],
            $field,
            $crate::UnivariatePolynomial<$field>
        );
        $crate::impl_left_scalar_mul_for!(
            [const NN: usize, $($parm)*],
            $field,
            $crate::MultivariatePolynomial<NN, $field>
        );
        $crate::impl_left_scalar_mul_for!([$($parm)*], $field, $crate::linalg::Matrix<$field>);
        $crate::impl_left_scalar_mul_for!([$($parm)*], $field, $crate::linalg::Vector<$field>);
    };
}
