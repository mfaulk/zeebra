# Batch inversion: what Montgomery's trick is worth, and where it does not apply

**Measured at:** publication bound `c951cc1f` — the commits that published these figures,
recovered from git rather than recorded at the time ([§10](external-comparison-protocol.md#10-the-commit-and-what-a-publication-bound-is)).

Reference for #118.

Inversion is the most expensive operation a prime field has: `montgomery_256` reaches it through
the binary extended Euclidean algorithm and the narrower types through exponentiation. Montgomery's
trick replaces n inversions with **one** inversion and `3(n-1)` multiplications, which is a win
exactly when three multiplications cost less than one inversion — in every field this crate has, by
a wide margin.

Every number below comes from

```text
cargo run --release --example batch_inversion
```

on the development workstation, pinned with `taskset -c 2`, each timing the fastest of 25 runs.
Every comparison asserts that the two paths produce the same values before reporting a ratio; the
fast path being wrong is the failure mode that a speedup would otherwise hide.

## 1. The routine

`src/fields/batch_inverse.rs`. `batch_invert(&mut [F])` works in place and `batch_inverse(&[F])`
allocates; both are generic over `FiniteField`.

**A zero element is left as zero.** It has no inverse, and panicking would make the routine
unusable exactly where it is most wanted, since a batch comes from a container and a container of
field elements may legitimately hold zeros. `FiniteField::inverse` keeps its panic because there
the caller named the single element it was asking about; here it did not. `test_zeros_are_left_alone`
pins the behaviour at the front, the middle and the back of a batch — the three positions the
backward walk could index wrongly.

| n | Mersenne-31 | Goldilocks | BN254 `Fr` | BLS12-381 `Fr` |
|---|---|---|---|---|
| 1 | 0.93x | 0.97x | 0.96x | 0.96x |
| 2 | **1.84x** | **1.94x** | **1.76x** | **1.81x** |
| 16 | 10.5x | 13.6x | 9.4x | 9.2x |
| 256 | 30.8x | 70.9x | 40.5x | 37.3x |
| 1 024 | 34.2x | **90.5x** | **50.0x** | 39.9x |
| 16 384 | 35.2x | 67.6x | 38.1x | 38.0x |

**The crossover is n = 2** in every field, and a single-element "batch" loses by 3–7% to the copy
and the extra multiplication. The plateau is the ratio between an inversion and three
multiplications: 35x over Mersenne-31, 38x over both 254-bit fields, and 68–90x over Goldilocks,
whose `inverse` is an exponentiation by a 64-bit exponent and so the dearest relative to its
multiply.

> **The Mersenne-31 and Goldilocks columns predate #160**, which halved Fermat inversion by routing
> it through the iterative `pow_limbs` instead of the recursive `pow`. The plateau is a ratio to
> inversion, so for the fields that invert by Fermat it is now roughly half of what this table
> reports. Corroborated in a different harness rather than re-measured here: `field_arithmetic`'s
> `isolated/inverse` against its `batch/inverse` over 256 operands went from 29.6x to 14.8x over
> `Mersenne31` and from 54.6x to 27.6x over the largest 64-bit prime, while BN254 `Fr` held at
> 60.4x against 60.7x. Those absolute ratios are not this table's — different instrument, one
> fixed n — and should not be substituted into it; only the halving carries over. The two 254-bit
> columns invert by extended Euclid and are unaffected. The crossover at n = 2 is unchanged: it is
> set by the copy, not by the ratio. Re-running this table is the honest fix and was not #160's
> scope.

Per-element cost at the plateau is 7.6 ns over Mersenne-31 and 96 ns over BN254 — a 12.6x ratio
against the 4x element-width ratio, which is the wide field's multiplication showing through now
that the inversion is gone.

The scratch vector of prefix products is the cost: `nonzeros * size_of::<F>()` bytes. §3 shows it
is free in context at the one place it was wired in.

## 2. The integration: the two FFT call sites

`FFTDomain::inverse` inverted every power of the generator individually, and `fft::interpolate`
paid that *and* divided every coefficient by n — which is a second inversion per coefficient, since
`Div` on a field element is multiplication by `inverse()` and nothing memoized it.

Both are measured against a local reimplementation of exactly what each used to do, in the same
process on the same input, so the ratio is an A/B of two implementations of one function.

### 2.1 `FFTDomain::inverse`

| n | KoalaBear | Goldilocks | BN254 `Fr` |
|---|---|---|---|
| 256 | 32.1x | 62.3x | 45.7x |
| 4 096 | 36.8x | 88.5x | 44.7x |
| 65 536 | 21.8x | 65.6x | 43.9x |

It is **not** the cheaper `from_generator(self.generator().inverse(), self.size())` that the source
carried as commented-out code, and that form is not merely slower to reach — it is wrong. A domain
is not required to be a power sequence starting at one: `split()` produces the odd powers
`g, g^3, g^5, ...`, whose `generator()` is `g^3`, whose inverses are not the powers of `g^-3`, and
which `from_generator` would reject outright because `(g^3)^(n/2) = -1`.
`test_inverse_of_a_split_domain` pins all three facts.

### 2.2 `fft::interpolate`, with the two contributions separated

| field | n | batch the domain | hoist the `1/n` | both |
|---|---|---|---|---|
| KoalaBear | 256 | 3.52x | 1.02x | **3.58x** |
| KoalaBear | 4 096 | 2.88x | 1.14x | **3.29x** |
| KoalaBear | 65 536 | 2.78x | 0.95x | **2.65x** |
| Goldilocks | 256 | 7.58x | 1.00x | **7.57x** |
| Goldilocks | 4 096 | 7.13x | 1.00x | **7.10x** |
| Goldilocks | 65 536 | 5.69x | 1.02x | **5.81x** |
| BN254 `Fr` | 256 | 3.03x | **4.65x** | **14.12x** |
| BN254 `Fr` | 4 096 | 2.89x | **3.73x** | **10.79x** |
| BN254 `Fr` | 65 536 | 2.69x | **2.92x** | **7.86x** |

Separating them was worth doing, because the second column is the surprise: **hoisting the
loop-invariant `1/n` is worth nothing on the 64-bit-backed fields and 2.9–4.7x on BN254.** The
compiler was already doing it where `inverse` is a small recursive `pow` that inlines, and was not
where `inverse` is the `montgomery_256` loop. A reader of the source would have predicted n saved
inversions in both cases and been wrong about half of them; that is what the measurement is for.

### 2.3 End to end, through `examples/univariate_scaling`

The #83 instrument re-run unchanged, at one second of wall clock per measurement. `ntt` is
untouched, so the ratio between the two transforms — both measured in the same process — is the
robust quantity:

| field | `intt`/`ntt` at 2^18, before | after | `intt` ns/element at 2^18 | largest `intt` reached |
|---|---|---|---|---|
| KoalaBear | 2.39x | **1.02x** | 457.0 → 172.4 | 2^22 → **2^23** |
| Goldilocks | 5.19x | **1.07x** | 918.0 → 165.1 | 2^21 → **2^23** |
| BN254 `Fr` | 8.55x | **1.10x** | 7 209 → 867.2 | 2^18 → **2^20** |

**The inverse transform now costs what the forward transform costs**, to within 2–10%. The entire
gap #83 recorded was inversions — `2n` of them, where two would do. That removes what #83 named as
the `intt` stage's whole penalty, and the reachable transform size grows 2x over KoalaBear and 4x
over Goldilocks and BN254.

Peak bytes are **unchanged** at `9 n B`: the batch's scratch vector raises the domain-inversion
moment to `3 n B`, which is well under the recursive transform's own `7 n B` peak later in the
call, so it never becomes the maximum. The scratch is free here.

## 3. Where it does not apply: F4's pivot normalization

#118 proposed wiring batch inversion into `reduced_row_echelon`. **That was not done**, and the
argument is not about safety margins — it is that the inverses are never simultaneously available.

In `row_echelon_within` a row is normalized at the moment it becomes a pivot, and every later row
depends on it: the factor that clears a column is the incoming row's leading coefficient *because*
the pivot's is one. One could instead leave pivots unnormalized and store `c^-1` per pivot, scaling
the factor — that keeps the inversion count identical, so where the scaling is applied is not the
obstruction. **The obstruction is ordering.** Pivots are *discovered* one at a time, each after the
reductions that consumed the previous ones, so their coefficients are never all in hand at once,
and a batch needs exactly that. Collecting them first means reducing rows against unnormalized
pivots in a different order, which is a different elimination — precisely the change #118 said must
not be made without an independent equivalence argument.

`reduced_row_echelon`'s second pass, the suggested integration point, has nothing left to batch:
the first pass already normalized every pivot. The same ordering argument applies to
`linalg::echelon`, the dense kernels, `crout`'s LU and FGLM's incremental span, all of which invert
at pivot discovery. The one bulk site elsewhere in the crate is making a generator list monic,
where the leading coefficients *are* all available at once — but F4 and Buchberger keep their bases
monic, so that loop finds almost nothing to invert.

### 3.1 The headroom, measured

Even granting a way to batch, `pivot_inversions / row_operations` bounds what it could touch — and
it is a generous bound, since a row operation is many multiplications while an inversion is one:

| system | row operations | pivot inversions | share | F4 time |
|---|---|---|---|---|
| katsura-4 | 176 | 5 | 2.841% | 0.2 ms |
| katsura-5 | 1 609 | 13 | 0.808% | 0.7 ms |
| katsura-6 | 11 885 | 31 | 0.261% | 3.7 ms |
| katsura-7 | 82 082 | 88 | **0.107%** | 33.8 ms |
| cyclic-5 | 3 929 | 67 | 1.705% | 1.4 ms |
| cyclic-6 | 41 993 | 244 | 0.581% | 13.0 ms |

**The share falls monotonically as the systems grow**, to 0.107% on katsura-7. The reason is the
one `SparseRow::normalize` already documents: F4's rows are built from monic basis elements, so
most pivots are already one and cost no inversion at all. There is nothing here worth the risk of
touching the elimination.

So, in #118's own terms: **F4 total time does not change, because no F4 code path was modified.**
That is a statement about the diff rather than about a timing — `grep` over `src/grobner/` and
`src/linalg/` finds no reference to `FFTDomain`, `interpolate`, `batch_inverse` or `batch_invert` —
and it is a stronger claim than a measurement on this box could support, since the headroom above
is smaller than its run-to-run noise.

## 4. What this leaves open

- **A scratch-taking variant.** `batch_invert` allocates its prefix-product vector per call. The
  one caller allocates anyway and the scratch never sets the peak, so there is nothing to fix yet;
  `SparseRow::subtract_scaled`'s `&mut Vec` parameter is the pattern if a hot loop ever wants it.
- **The reversal identity.** For a domain that really is the n powers of a primitive n-th root,
  `w^-i = w^(n-i)`, so its inverse is a permutation of itself — zero inversions and zero
  multiplications, against this one inversion and `3n` multiplications. It is unavailable here
  because `FFTDomain` does not record whether it is geometric and `split()` produces domains that
  are not, and verifying the property costs as much as inverting. Recording provenance on the type
  would make the domain inverse free; it is a change to a public type's shape, so it belongs to
  whatever work next needs the transform to be faster.
- **`interpolate`'s remaining cost** is now the forward transform it calls, which is #83's gap list
  — the recursive `evaluate` and the absence of an NTT-based multiply.
