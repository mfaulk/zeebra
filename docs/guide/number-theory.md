# Integers and factoring

Integer roots, perfect powers, and Lenstra's elliptic curve method.

## Integer Roots and Perfect Powers
`BigUInt::isqrt` and `BigUInt::nth_root` return the floor of the root, and `perfect_power` writes
`n` as `m^k` with the largest `k` it can:

```rust
use zeebra::integers::{big_uint::BigUInt, perfect_power};

assert_eq!(BigUInt::new_from_u64(26).nth_root(3), BigUInt::new_from_u64(2));
assert_eq!(BigUInt::new_from_u64(17).isqrt(), BigUInt::new_from_u64(4));

// 64 = 8^2 = 4^3 = 2^6, and only the last has a base that is not itself a perfect power.
let (base, exponent) = perfect_power(&BigUInt::new_from_u64(64)).unwrap();
assert_eq!((base, exponent), (BigUInt::new_from_u64(2), 6));

assert_eq!(perfect_power(&BigUInt::new_from_u64(12)), None);
```

Both roots are Newton's iteration started at `2^ceil(bits/k)`, which is above the root — the side
on which the iteration decreases monotonically, so it terminates at the floor with no correction
step. Zero and one are not perfect powers: every exponent would answer for them.

`perfect_power` tests only **prime** exponents, which loses nothing because `m^(ab)` is `(m^a)^b`,
and recurses on the base to recover a composite exponent. That is why `64` is reported as `2^6`
rather than as the `8^2` the `k = 2` pass finds.

`factor` runs the test before Pollard rho, which is what the test is for: rho needs about
`p^(1/2)` iterations to split `p^k`, so `p^3` for a 20-digit prime does not factor in any practical
time without it and factors in a single primality check with it
(`test_factorization_of_a_prime_power_rho_cannot_reach`).

## Lenstra's Elliptic Curve Method
Pollard rho costs about `p^(1/2)` iterations in the smallest prime factor `p`, so it reaches
20-digit factors and not 40-digit ones. ECM's expected cost depends on the size of the factor it
finds rather than on the size of `n`, which makes it a complement to rho rather than a replacement.
The workload it is here for is the factorization of `q - 1` for a wide prime field `q`, which is
what finding a generator of the multiplicative group needs.

`ecm_find_factor` returns one non-trivial factor, and `None` when the budget ran out without
finding one. That `None` is an ordinary outcome, not an error:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::integers::{big_uint::BigUInt, ecm_find_factor, factor_with_budget, EcmBudget};

let mut rng = StdRng::seed_from_u64(20260131);
let budget = EcmBudget { b1: 200, b2: 20_000, curves: 40 };

// 10_007 * 10_009, past the small-prime table that trial division uses.
let n = BigUInt::new_from_u64(10_007) * &BigUInt::new_from_u64(10_009);
let factor = ecm_find_factor(&n, &budget, &mut rng).unwrap();
assert!(factor > BigUInt::one() && factor < n);
assert!((&n % &factor).is_zero());

// A prime has no factor to find, so the budget is spent and the answer is honest.
assert_eq!(ecm_find_factor(&BigUInt::new_from_u64(1_000_003), &budget, &mut rng), None);
```

`factor_with_budget` drives trial division, the perfect-power test and ECM together. What it could
not split is reported rather than dropped, so `product()` always returns the input:

```rust
use rand::{prelude::StdRng, SeedableRng};
use zeebra::integers::{big_uint::BigUInt, factor_with_budget, EcmBudget};

let mut rng = StdRng::seed_from_u64(3883);
let budget = EcmBudget::for_digits(10);

let n = BigUInt::new_from_u64(1_290_159_361_801_237); // 4409^3 * 15053
let factorization = factor_with_budget(&n, &budget, &mut rng);
assert!(factorization.is_complete());
assert_eq!(factorization.primes, vec![BigUInt::new_from_u64(4409), BigUInt::new_from_u64(15053)]);
assert_eq!(factorization.powers, vec![3, 1]);
assert_eq!(factorization.product(), n);

// A budget too small for the cofactor leaves it in `unfactored`, and the product still holds.
let tiny = EcmBudget { b1: 100, b2: 0, curves: 1 };
let hard = BigUInt::from_dec_str("1000000000000000003").unwrap()
    * &BigUInt::from_dec_str("1000000000000000009").unwrap();
let partial = factor_with_budget(&(BigUInt::new_from_u64(12) * &hard), &tiny, &mut rng);
assert!(!partial.is_complete());
assert_eq!(partial.unfactored, vec![(hard, 1)]);
assert_eq!(partial.product(), BigUInt::new_from_u64(12) * &partial.unfactored[0].0);
```

That budget is the point of the API shape. `prime_field_256`'s `try_primitive_element` returns
`Err(RootOfUnityError::NoKnownGenerator)` rather than searching, because finding a generator means
factoring a 254-bit `q - 1` and that should not start by accident. ECM does not change that: a
factorization of a 254-bit `q - 1` is still something a caller has to ask for, which is why the
entry point makes the effort explicit and can say "I did not finish". Wiring the two together is
tracked separately (#405); nothing in the crate calls it yet.

### How it works
Stage 1 multiplies a point on a **Montgomery curve** `B y^2 = x^3 + A x^2 + x` by every prime power
up to `b1`, using the Montgomery ladder over `XZ`-only projective coordinates. If the curve's order
modulo some prime factor `q` of `n` is `b1`-smooth, the point reaches the identity modulo `q`, and
`q` then divides the resulting `Z` while `n` does not — so `gcd(Z, n)` names it. The `y`-coordinate
is never needed, because `B` drops out of the `x`-only formulas.

Stage 2 is the **standard continuation**, which additionally catches an order that is `b1`-smooth
apart from a single prime in `(b1, b2]`. Writing such a prime as `p = v*D ± u` for a stride
`D = 210` and a `u < D/2` coprime to it, `[p]Q` being the identity modulo `q` means `[v*D]Q` and
`[u]Q` share an `x`-coordinate there — either sign of `u` will do, since `[-u]Q` and `[u]Q` have the
same `x`. Sharing an `x` is `X_vD * Z_u - X_u * Z_vD` vanishing, and those differences accumulate
into one product, so the whole stage costs a single gcd. A difference that is zero modulo *all* of
`n` is skipped rather than multiplied in, since its gcd is `n` and it would erase what every other
pair found. Coverage starts at `D/2 = 105`, so a `b1` below that would leave a gap; any realistic
`b1` is far above it.

Curves come from **Suyama's parameterization**, which forces the order to be divisible by 12 and so
raises the chance of smoothness. It needs `(A + 2) / 4`, and `BigUInt` has no modular inverse — so
the constant is carried as an unreduced fraction `num / den` and cleared projectively by scaling
both coordinates of the doubling by `den`. That costs one multiply per doubling and buys more than
it costs: inversion would fail exactly when `den` shares a factor with `n`, and that gcd is itself
the factor being hunted, so the degenerate case returns an answer instead of an error. It is also
why an even `n` is split immediately — `den` carries a factor of 16.

`EcmBudget::for_digits` follows the usual ECM parameter table (`b1` of 2e3, 1.1e4, 5e4 and 2.5e5 for
the 15-, 20-, 25- and 30-digit levels, with `b2 = 100 * b1`). Those are the asymptotically motivated
choices from the literature and **not** measurements of this implementation: the inner loop here is
a `BigUInt` multiply and remainder rather than Montgomery arithmetic, so a given budget costs
considerably more wall-clock time than a tuned implementation would pay. Treat the digit levels as
the shape of the parameter curve, not as a promise about runtime.

Quadratic Sieve is deliberately absent. Its cost depends on the size of `n`, which makes it the
right tool for a hard semiprime — and `q - 1` is not that. It is semi-smooth: a few small primes
and a handful of middling ones, which is exactly the shape ECM is for.
