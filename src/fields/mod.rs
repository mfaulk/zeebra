//! Finite fields

mod binary_field;
mod extension_field;
mod finite_field;
mod irreducible_polynomials;
mod prime_field_128;
mod prime_field_64;

pub use finite_field::FiniteField;
pub use prime_field_128::PrimeFieldElement128;
pub use prime_field_64::PrimeFieldElement64;

// === 64-bit prime fields ===

/// Z mod 7
pub type Zp7 = PrimeFieldElement64<7>;

/// Z mod 13
pub type Zp13 = PrimeFieldElement64<13>;

/// Z mod 541
pub type Zp541 = PrimeFieldElement64<541>;

/// Z mod 1091
pub type Zp1091 = PrimeFieldElement64<1091>;

/// Z mod 65537, Proth prime 2^16 + 1.
pub type Zp65537 = PrimeFieldElement64<65537>;

/// Z mod 2147483647, Mersenne prime 2^31 - 1.
pub type Zp2147483647 = PrimeFieldElement64<2147483647>;

/// 2^62 - 111 * 2^39 + 1 = 4611624995532046337
pub type Zp4611624995532046337 = PrimeFieldElement64<4611624995532046337>;

/// 2^64 - 2^32 + 1 = 18446744069414584321
pub type Zp18446744069414584321 = PrimeFieldElement64<18446744069414584321>;

/// 2^64 - 59 = 18446744073709551557 is the largest 64-bit prime.
pub type Zp18446744073709551557 = PrimeFieldElement64<18446744073709551557>;

// === 128-bit prime fields ===

/// Z mod 221360928884514619393, Proth prime 3*2^66 + 1
pub type Zp221360928884514619393 = PrimeFieldElement128<221360928884514619393>;
