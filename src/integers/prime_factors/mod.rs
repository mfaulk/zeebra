//! Prime factors of large integers.
//!
//! # References
//! * [DJB's Integer Factorization](https://cr.yp.to/2006-aws/notes-20060309.pdf)

mod factoring;
mod generator;
mod miller_rabin;
mod pollard_rho;
pub mod small_primes;

pub use factoring::{factor, from_prime_factorization};
pub use generator::find_generator;
pub use small_primes::*;
