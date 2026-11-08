//! Error-correcting codes over finite fields.
//!
//! One code so far: [`ReedSolomon`], in evaluation form over a caller-supplied
//! [`FFTDomain`](crate::FFTDomain).
//!
//! # The bound the decoder works to, and what it does past it
//!
//! A `[n, k]` Reed-Solomon code has minimum distance `d = n - k + 1`. [`ReedSolomon::decode`]
//! corrects up to `t = (n - k) / 2` errors at unknown positions, and
//! [`ReedSolomon::recover_erasures`] fills in up to `n - k` at known ones. Past `t` errors the
//! nearest codeword need not be the transmitted one, so there is nothing a decoder could return
//! that would be *right*; this one returns [`CodeError::Uncorrectable`] instead of a guess, and
//! verifies its candidate against the code before answering so that it cannot do otherwise. List
//! decoding past `t` is not implemented.
//!
//! # Cost, and the one size to avoid
//!
//! Encoding and syndrome extraction are one transform each, so they inherit whatever
//! [`crate::evaluate`] costs at the chosen block length: `O(n log n)` for a power of two or a
//! product of small coprime factors, but `O(n^2)` for a block length with a large prime factor,
//! which `fft::prime_factor` handles by the definition. [`crate::bluestein_transform`] removes
//! that case, and since #375 it **is** dispatched to automatically above a measured size — but
//! only for a domain prepared by [`crate::with_bluestein`], which needs
//! [`crate::KnownOrder`] and an rng. So a prime block length over an unprepared domain is still
//! quadratic, and preparing one is the deliberate choice rather than the prime length itself.

mod reed_solomon;

pub use reed_solomon::{CodeError, Correction, ReedSolomon};
