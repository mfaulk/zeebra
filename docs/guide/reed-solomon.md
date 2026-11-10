# Error-correcting codes

Reed–Solomon codes over an FFT domain: encoding, erasure recovery, and a Euclidean decoder that
verifies its own correction.

`codes::ReedSolomon` is an `[n, k]` Reed-Solomon code in evaluation form: a codeword is a
polynomial of degree below `k` evaluated on an FFT domain of `n` points. The domain is the
caller's, as it is for `evaluate` and `interpolate` — only the caller knows which field it is
working over and which sizes that field can host.

```rust
use zeebra::{
    codes::{CodeError, ReedSolomon},
    fields::Zp65537,
    FFTDomain, FiniteField, KnownOrder,
};
use rand::{prelude::StdRng, SeedableRng};

let mut rng = StdRng::seed_from_u64(1);

// A [16, 10] code: six parity symbols, so three errors or six erasures.
let domain = FFTDomain::from_generator(Zp65537::two_adic_root_of_unity(4, &mut rng), 16);
let code = ReedSolomon::new(domain, 10).unwrap();
assert_eq!((code.distance(), code.max_errors(), code.max_erasures()), (7, 3, 6));

let message: Vec<Zp65537> = (1..=10).map(Zp65537::new).collect();
let codeword = code.encode(&message).unwrap();

// Three errors at unknown positions are located and corrected.
let mut received = codeword.clone();
received[2] += Zp65537::new(9);
received[7] += Zp65537::new(1234);
received[13] += Zp65537::new(5);
let decoded = code.decode(&received).unwrap();
assert_eq!(decoded.message, message);
assert_eq!(decoded.error_positions, vec![2, 7, 13]);

// A fourth error is past the radius, and is reported rather than mis-corrected.
received[0] += Zp65537::new(7);
assert_eq!(code.decode(&received), Err(CodeError::Uncorrectable));

// Six erasures are twice as many, because a known position needs no locator. The values at the
// erased positions are ignored, so any placeholder will do.
let mut punctured = codeword.clone();
for position in [0, 1, 4, 9, 11, 15] {
    punctured[position] = Zp65537::new(0);
}
let recovered = code.recover_erasures(&punctured, &[0, 1, 4, 9, 11, 15]).unwrap();
assert_eq!(recovered.codeword, codeword);
```

`encode` reads the message as the polynomial's coefficients, so it does not appear in the codeword.
`encode_systematic` reads it as the polynomial's values on the first `k` domain points instead, at
which point `codeword[..k]` *is* the message — one `O(k^2)` interpolation bought in exchange for
being readable without decoding.

## Why the syndromes are already there

Interpolating a received word over the domain gives `r(x)` with `r_j = (1/n) * sum_i y_i w^{-ij}`.
A codeword's `r_j` vanishes for `j >= k` by definition, so the top `n - k` coefficients of `r`
*are* the syndromes, and the decoder needs no transform the encoder did not already need. Writing
out the `j`th of them for an error `e` supported on a set `E`:

```text
S_j = r_{k+j} = sum_{i in E} Y_i X_i^j,   X_i = w^{-i},   Y_i = e_i w^{-ik} / n
```

which is the classical syndrome form, so the classical key equation
`Λ(x)S(x) ≡ Ω(x) mod x^{2t}` applies unchanged. It is solved here by the extended Euclidean
sequence on `(x^{2t}, S(x))`, halted at the first remainder of degree below `t` — which is
`gcd.rs`'s algorithm stopped early, rather than a second recurrence in Berlekamp-Massey's shape.
Error positions then come from evaluating the locator on the domain rather than from `roots`: the
roots of `Λ` are exactly domain points, so a scan is both cheaper than general root finding and
unable to return a root that is not a position. Magnitudes come from Forney's formula.

## A correction is a candidate until it is verified

Past `t` errors the nearest codeword need not be the transmitted one, so there is nothing a decoder
could return that would be *right*. The Euclidean step does not know that — it still produces some
locator of degree at most `t` — so `decode` re-interpolates its candidate and checks it is a
codeword before answering, and returns `CodeError::Uncorrectable` when it is not. Together with the
degree bound that caps the locator, and hence the number of symbols touched, at `t`, that is the
whole correctness argument: a word verified to be a codeword and at distance at most `t` from the
received word is the only such codeword, because two of them would be within `2t < d` of each
other.

The practical consequence is that a code of **odd** redundancy detects one more error than it can
locate. All `n - k` syndromes are checked, while only `2t = n - k - 1` of them feed the key
equation, so the spare one is left over to veto a correction that explains the others. Erasure
recovery spends its surplus the same way: `k` surviving symbols determine the codeword polynomial,
and every survivor beyond those `k` checks the answer, so an error at an *unerased* position is
reported rather than quietly interpolated into a different codeword.

## Cost, and the one block length to avoid

Encoding and syndrome extraction are one transform each, so they cost whatever `evaluate` costs at
the chosen block length: `O(n log n)` for a power of two or a product of small coprime factors, but
`O(n^2)` for a block length with a large prime factor, which `fft::prime_factor` handles by the
definition. `bluestein_transform` removes that case and is not dispatched to automatically, so a
prime block length is a choice to make deliberately rather than one to stumble into.

Not implemented: combined errors-and-erasures decoding, list decoding past `t`, and any code other
than Reed-Solomon. Characteristic two is also out for now — `interpolate` scales by `F::new(n)`,
and `FiniteField::new` is unimplemented for `BinaryFieldElement`, so the inverse transform has no
`1/n` to use over `GF(2^m)`.
