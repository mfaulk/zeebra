use super::{SigF4Error, SigF4Options, SigF4Statistics};
use crate::{poly::MonomialOrder, FiniteField, MultivariatePolynomial};

pub(super) fn run<const N: usize, F: FiniteField>(
    _generators: &[MultivariatePolynomial<N, F>],
    _order: MonomialOrder,
    _options: &SigF4Options,
    _statistics: &mut SigF4Statistics,
) -> Result<Vec<MultivariatePolynomial<N, F>>, SigF4Error> {
    Err(SigF4Error::Unsupported {
        reason: "not implemented",
    })
}
