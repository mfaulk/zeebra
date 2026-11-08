# Groebner.jl 0.10.11: monomial encodings, the hashtable, and learn/apply traces

Source study for #265, read at the version Zeebra measures against: **Groebner.jl 0.10.11** on
**Julia 1.11.7** with **AbstractAlgebra 0.50.5**, installed by `tools/external/provision.sh` into
`$ZEEBRA_EXT_PREFIX/julia-depot`. Every `path:line` below is relative to the package root
(`julia-depot/packages/Groebner/Aqs1M`) and was read at that range rather than grepped for.

The adapter that drives it is `src/grobner/external/groebner_jl.rs`; what it is like to *run* is
`docs/research/external-comparands.md` §4. This note is about what is *inside* it.

**Read §1 before §3.** More than half of what #265 was commissioned to study is code Groebner.jl
says it adapted from msolve, so this note and #264's msolve note are reading the same design twice
and an agreement between them is not corroboration.

---

## 1. What is msolve's, and what is Groebner.jl's own

`src/Groebner.jl:1`:

```
# This file is a part of Groebner.jl. License is GNU GPL v2.
```

`src/Groebner.jl:8-15`:

```
# Parts of Groebner were adapted from msolve:
# https://github.com/algebraic-solving/msolve
# msolve is distributed under GNU GPL v2+:
# https://github.com/algebraic-solving/msolve/blob/master/COPYING
#
# More precisely, the F4 implementation in Groebner adapts monomial hashtable
# implementation and routines for critical pair handling, symbolic
# preprocessing, and linear algebra from msolve.
```

That statement is not decoration: **eight files carry the same four-line attribution header at
lines 3-6**, and they are exactly the files the sentence names.

| carries the msolve header at `:3-6` | what lives there |
|---|---|
| `src/f4/hashtable.jl` | the monomial hashtable, divmasks, the three-table split (§3) |
| `src/f4/f4.jl` | the F4 main loop, symbolic preprocessing, the reducer search |
| `src/f4/basis.jl` | the basis, the pairset, Gebauer–Möller |
| `src/f4/sort.jl` | matrix row and column sorting |
| `src/f4/linalg/backend.jl` | the deterministic sparse reduce-by-pivots kernels |
| `src/f4/linalg/backend_threaded.jl` | the CAS-sentinel threaded variant (§5) |
| `src/f4/linalg/backend_randomized.jl` | blocked randomized elimination |
| `src/f4/linalg/backend_randomized_threaded.jl` | both at once |
| `src/f4/linalg/backend_learn_apply{,_threaded}.jl` | the trace-recording and replaying backends |

**Files with no msolve attribution — Groebner.jl's own work, and the interesting half:**

| no attribution | what lives there |
|---|---|
| `src/monomials/*.jl` (7 files) + `src/utils/packed.jl` | **every monomial encoding**, including the hand-written LLVM IR (§2) |
| `src/arithmetic/Zp.jl`, `CompositeNumber.jl`, `generic.jl` | delayed and signed modular arithmetic, 4-prime SIMD lanes (§5) |
| `src/f4/trace.jl`, `src/f4/learn_apply.jl`, `src/groebner/{learn_apply,wrapped_trace}.jl` | **the trace structure itself** — what is recorded, pivot signatures, apply-time verification (§4) |
| `src/f4/linalg/backend_changematrix.jl` | the transformation-matrix backend |
| `src/groebner/modular.jl`, `src/reconstruction/*` | multi-modular lifting, CRT, rational reconstruction (`ratrec.jl:5` credits Nemo.jl) |

So the division is clean and useful: **msolve contributed the F4 skeleton and the linear algebra;
Groebner.jl contributed the monomial representations, the arithmetic, and the trace.** For #264's
purposes that means §3 and §5's "backend" rows are a second vantage on msolve's design and nothing
more. For Zeebra's purposes it means the opposite of what the issue titles suggest: the parts worth
studying *as Groebner.jl's* are §2 and §4, which #264 does not cover at all.

### 1.1 A licence tension inside Groebner.jl, found while reading

`src/groebner/auxiliary.jl:240`, in the backend for the `dimension` entry point:

```julia
# Copied from AlgebraicSolving.jl. The license is GNU GPL, Version 3.0+.
```

`LICENSE` is the GPL **version 2** verbatim and `src/Groebner.jl:1` elects "GNU GPL v2" with no
"or later". GPL-2.0-only cannot incorporate GPL-3.0-or-later code — the permission to use the
AlgebraicSolving code is conditional on distributing under GPL-3.0 or later, which GPL-2.0-only is
not.

**This is Groebner.jl's problem and not Zeebra's**, because Zeebra runs it as a subprocess and
copies nothing (`docs/research/external-provenance-policy.md` §7). Two things to carry anyway:
the policy's table at `:58` records Groebner.jl as GPL-2.0 on the strength of the header, which is
right about the election and incomplete about what is inside; and the function Zeebra's adapter
actually calls for its `@dim` marker is the GPL-3.0+ one. Neither changes the verdict — **reference
only** — it just makes the verdict more firmly correct than the single-licence reading suggested.

---

## 2. Monomial encodings: seven representations, chosen by variable count

This is the part with no msolve provenance and the part where Zeebra differs most.

### 2.1 Zeebra's baseline, for comparison

`src/poly/multivariate/monomial.rs:15-19` is a dense exponent array and nothing else:

```rust
pub struct Monomial<const N: usize> {
    pub(crate) exponents: [u32; N],
}
```

**No total degree is stored**; `degree()` at `:53` sums the array on every call. At `N = 7` a
Zeebra monomial is 28 bytes and a comparison is an array comparison.

### 2.2 The common interface, and the overflow contract

Every representation implements the same twenty-odd `monom_*` functions (union of accepted types at
`src/types.jl:8-16`): `monom_totaldeg`, `monom_hash`, `monom_isless`, `monom_lcm!`,
`monom_product!`, `monom_division!`, `monom_is_divisible[!]`, `monom_is_gcd_const`,
`monom_create_divmask`, and so on.

Overflow is a *recoverable* condition rather than a bug: `src/monomials/exponent_vector.jl:19-29`
defines `MonomialDegreeOverflow` with the threshold at `div(typemax(T), 2)`, and the driver retries
the whole computation with wider exponents — `src/groebner/learn_apply.jl:38-42` passes
`hint = :large_exponents`, which `src/groebner/parameters.jl:49-52` turns into
`ExponentVector{UInt64}`. **That retry loop is what makes the narrow representations safe to try
first**, and it is the structural reason Groebner.jl can afford a 4-bit exponent field.

### 2.3 The seven representations

| type | file | layout | variable ceiling | orders |
|---|---|---|---|---|
| `ExponentVector{T}` | `exponent_vector.jl` | heap `Vector{T}`, **slot 1 is the total degree**, slots `2..n+1` the exponents (`:41`, `:45-58`) | `2^32` (`:36`) — effectively none | **all** (`:91-94`) |
| `PackedTuple1..4{T,B}` | `packed_vector.jl` | 1–4 `UInt64` words, `UInt8` fields, **degree in the top byte of `a1`** (`:58`, `:78-89`) | 7 / 15 / 23 / 31 (`:57`) | DegRevLex only (`:286-288`) |
| `FixedVector{N,T}` | `fixedvector.jl` | inline `N` lanes, **last lane holds `~degree`** (`:11`, `:26`) | `N - 1` (`:10`) | DegLex, DegRevLex, Input (`:41-43`) |
| `FixedMonom{N,T}` | `fixedvector2.jl` | `FixedVector{N,T}` + a separate `deg` field (`:3-6`) | `N` (`:17`) | as above |
| `FixedMonomNoDeg{N,T}` | `fixednodeg.jl` | the same without `deg`; degree recomputed into `UInt16` (`:3-5`, `:10-13`) | `N` | as above |
| `NibbleMonom{N}` | `nibblemonom.jl` | **two 4-bit exponents per byte** + `deg` (`:16-19`), exponents capped at 15 (`:36`) | `2N` (`:27`) | as above |
| `NibbleNoDeg{N}` | `nibblenodeg.jl` | the same without `deg` (`:20-23`) | `2N` | as above |

### 2.4 The trick worth understanding: a degree order as one integer compare

Three independent encodings all arrange for **`monom_isless` under a degree order to be a single
whole-word unsigned comparison**, and each gets there differently.

`PackedTuple`: the degree sits in the *top* byte and the variables are laid out with the
highest-indexed block in `a1` and, within a word, variable 1 in the lowest byte. A plain unsigned
compare of `a1` is therefore degree-then-reverse-lex, and `monom_isless` for `DegRevLex{true}`
(`packed_vector.jl:290-308`) is exactly `deg`, then `!(ea.a1 <= eb.a1)`, then `a2`, and so on.

`FixedVector`: the last lane stores the **bitwise complement** of the degree, so a larger degree is
a smaller complement. `fixedvector.jl:49-60`:

```julia
if sizeof(a) <= 64
    bits(a) > bits(b)
```

One integer compare of the whole struct implements degrevlex, ties falling through to the
highest-index differing exponent, which *is* reverse lex. The complement also makes arithmetic one
vector operation plus a `±1` correction in the degree lane, because `~(da+db) = ~da + ~db + 1` —
`fixedvector.jl:77-82`:

```julia
c = a + b + u   # u = ntuple(k -> T(k == N))
```

`NibbleMonom`: multiplication and division are byte-wide add/subtract of the whole vector, with the
low-nibble carry caught by one mask — `nibblemonom.jl:101-105`:

```julia
ev, s = Base.Checked.sub_with_overflow(a.ev, b.ev)
lower_check = iszero((ev .⊻ a.ev .⊻ b.ev) .& 0x10)
isempty(s) & lower_check, NibbleMonom(ev, a.deg - b.deg)
```

Divisibility is a lane-compare bitmask with the degree lane masked out
(`fixedvector.jl:89-93`), or a borrow set from `Base.Checked.sub_with_overflow`
(`fixedvector2.jl:97-100`), or — for the packed types — explicit SIMD: `src/utils/packed.jl:8-26`
is `llvmcall` with `icmp uge <8 x i8>` and an all-lanes-set reduction, and
`packed_vector.jl:565-588` ANDs it across chunks. `_packed_vec_max` + a
`llvm.vector.reduce.add.v8i8` give `monom_lcm!` with a recomputed degree byte (`:385-447`).

`exponent_vector.jl:9-12` records why the general representation does *not* do this:

> not automatically vectorized with the use of AVX2 or AVX512 … hard to do masked load

### 2.5 Selection

One function, `param_select_monomtype` (`src/groebner/parameters.jl:41-136`), and the bound is
computed **at the selection site from `nvars` thresholds** rather than from `monom_max_vars` — I
found no call site of `monom_max_vars` outside `src/monomials/`. Forced fallbacks come first
(`:49-62`: `hint = :large_exponents → ExponentVector{UInt64}`,
`homogenize → ExponentVector{UInt32}`), then the automatic path (`:113-133`):

```julia
# in the automatic choice, we always prefer non-allocating representations
if monoms === :auto
    if nvars > 31
        N = max(8, nextpow(2, max(nvars, 1)) ÷ 2)
        if monom_is_supported_ordering(NibbleMonom{N}, ordering)
            return NibbleMonom{N}
```

then `PackedTuple1..4` by `nvars < k * 8`, with `ExponentVector{UInt8}` as the final fallback
(`:135`). The user can force any of them: `monoms ∈ {:auto, :dense, :packed, :fixed, :fixed2,
:fixednodeg, :nibble, :nibblenodeg}` (`src/utils/keywords.jl:151`), of which the public docstring
advertises four (`src/interface.jl:48-53`).

**Not determined:** why the "nodeg" variants exist. No source comment says. The plausible reading —
dropping the degree field makes the struct exactly `N` bytes, and
`scripts/native_code_for_hashtable/README.md:25` notes "whether the total degree contributes to
hash" as the axis those benchmarks vary — is inference, and is labelled as such here rather than
repeated as fact.

---

## 3. The hashtable (msolve's design)

`src/f4/hashtable.jl:30`: "Hashtable implements open addressing with linear scan."

### 3.1 The hash is a random dot product, and the reason is linearity

`monom_hash` is `Σ x[i] * b[i] mod 2^32` over a uniformly random `hash_vector`
(`exponent_vector.jl:71-77`, `:79-86`; `MonomHash = UInt32` at `hashtable.jl:20`). Not a
Vandermonde or divisibility-friendly hash — a plain random dot product, chosen because it is
**linear**. `hashtable.jl:478-480`:

```
# Iterate over monomials of the given polynomial, multiply them by a
# monomial multiple, and insert them into symbolic hashtable.
# We use the fact that the hash function is linear.
```

and the quotient's hash is got by subtraction, `src/f4/f4.jl:273-275`:

```julia
@inbounds quotient_hash = symbol_ht.hashvals[monomid] - ht.hashvals[poly[1]]
@invariant quotient_hash == monom_hash(quotient, ht.hash_vector)
```

So `h(m₁m₂) = h(m₁) + h(m₂)` and `h(m₁/m₂) = h(m₁) − h(m₂)`: **the inner loop of symbolic
preprocessing never re-hashes a monomial**, it adds. The `@invariant` on the next line is the
self-check, and it compiles to nothing by default (`invariants_enabled() = false`,
`src/Groebner.jl:28`).

### 3.2 Layout

Struct of arrays, `hashtable.jl:36-62`:

```julia
monoms::Vector{M}
hashtable::Vector{MonomId}     # the open-addressing index: slot -> id
labels::Vector{Int32}          # matrix column label / column index
hashvals::Vector{MonomHash}
divmasks::Vector{DivisionMask}
```

* Probing is stride-1 linear under a power-of-two mask: `((h + j) & mod) + 1` (`:268-270`), with
  `@invariant ispow2(ht.size)` at `:281`.
* Resize threshold **0.4**, doubling (`:68-69`), and the rebuild **re-indexes from the stored
  `hashvals` without re-hashing any monomial** (`:224-262`). Side arrays are allocated at half the
  index size (`:84-91`).
* `MonomId = Int32`; ids index `monoms`; `offset = 2` because slot 1 is a scratch buffer
  (`:102-104`).
* **`labels` does double duty** — first as the matrix column classification
  (`NON_PIVOT_COLUMN` / `UNKNOWN_PIVOT_COLUMN` / `PIVOT_COLUMN`, `src/f4/matrix.jl:26-28`), then as
  the monomial→column map itself (`src/f4/matrix.jl:341`). **There is no separate column
  dictionary.** This is the single most transferable fact in §3; see §6.1.
* No per-entry degree. The degree comes from the monomial, which is why §2's encodings store it.

### 3.3 The divmask

`DivisionMask = UInt32`, so **32 bits total** (`:28`). Configured once at init (`:106-117`):

```julia
nbits = 8 * sizeof(DivisionMask)
bits_per_var = max(div(nbits, nvars), 1)
ndivvars = min(nvars, nbits)
divmap = zeros(DivisionMask, ndivvars * bits_per_var)
```

Thresholds are **data-dependent**: `hashtable_fill_divmasks!` (`:345-409`) scans the table for each
variable's observed min and max exponent (`:356-372`) and lays `ndivbits` increasing thresholds per
variable spaced by that range (`:374-387`). Bit `k` is set iff `e[i] >= divmap[k]`
(`exponent_vector.jl:348-357`).

The payoff is one instruction, `hashtable.jl:341-343`:

```julia
function divmask_is_probably_divisible(d1::DivisionMask, d2::DivisionMask)
    iszero(~d1 & d2)
```

used as a pre-filter in the reducer scan (`src/f4/f4.jl:211-222`) and in Gebauer–Möller pruning
(`src/f4/basis.jl:500-505`). Groebner.jl **measures its own false-positive rate** —
`_DIVMASK_CHECKS` and `_DIVMASK_FALSE_POSITIVES` at `f4.jl:208-209`, incremented at `:269`.

Two things a reader should not miss:

* **The thresholds are calibrated once, on the input generators** (`src/f4/f4.jl:24` is the only
  call to `hashtable_fill_divmasks!`), and never recalibrated as the basis grows and the exponent
  ranges move.
* **With more than 32 variables, only the first 32 get a bit.** The `:compact_variables` strategy
  that would pack several variables per bit is implemented for `ExponentVector`
  (`exponent_vector.jl:358-372`) and **disabled** by
  `const _DIVMASK_STRATEGY_MANY_VARIABLES = Ref(:first_variables)` (`hashtable.jl:71-72`). The
  packed, fixed and nibble encodings implement only `:first_variables` at all.

### 3.4 Three tables, one interning discipline

All three share `hash_vector`, `divmap`, `ndivvars` and `ndivbits`, so ids and masks are mutually
meaningful (`hashtable_initialize_secondary`, `:143-193`, explicitly "preserve division info" at
`:160-166`):

* **main** — the persistent interning table for basis monomials and accepted lcms;
* **`symbol_ht`** — the symbolic-preprocessing frontier, holding the matrix's columns, and
  **reinitialized every F4 iteration** (`src/f4/f4.jl:438`; `:195-222` resets size to `2^6`);
* **`update_ht`** — lcm candidates during Gebauer–Möller only (`src/f4/basis.jl:431`, `:444-450`),
  and **never reinitialized**, so it grows monotonically.

Survivors migrate from `symbol_ht` into the main table by
`matrix_insert_in_basis_hashtable_pivots!` (`src/f4/matrix.jl:363-412`), which copies `labels` and
`divmasks` and **reuses the already-computed hash** (`:380`). A `frozen` flag (`:62`) guards against
mutation during an apply replay.

---

## 4. Learn/apply traces (Groebner.jl's own)

### 4.1 What is recorded

`src/f4/trace.jl:5-44`, per F4 iteration:

```julia
matrix_infos::Vector{NamedTuple{(:nup, :nlow, :ncols), ...}}
matrix_nonzeroed_rows::Vector{Vector{Int}}
matrix_upper_rows::Vector{Tuple{Vector{Int}, Vector{MonomId}}}
matrix_lower_rows::Vector{Tuple{Vector{Int}, Vector{MonomId}}}
matrix_sorted_columns::Vector{Vector{Int32}}
matrix_pivot_signatures::Vector{UInt64}
matrix_pivot_indices::Vector{Vector{Int}}
critical_pair_sequence::Vector{Tuple{UInt64, Int}}
```

In words: the matrix shape; **the symbolic-preprocessing result as `(polynomial index, multiplier
MonomId)` pairs**, upper and lower; **which lower rows did not reduce to zero**; the column sort
order; the pivot schedule as leading-monomial ids plus a rolling 64-bit signature of the whole
pivot support; and a per-iteration `(degree, npairs)` summary. Pair *identities* are not stored —
they are implied by the recorded row lists.

Only the reducers actually used are kept, which is a real saving —
`src/f4/linalg/backend_learn_apply.jl:262-277`:

```
# NOTE: we sort reducers by their original position in the array of pivots.
# This way, the rows are already sorted at the apply stage.
useful_reducers_sorted = sort(collect(useful_reducers))
```

collected by `record_active_reducer` (`:86-90`) from inside the reduction kernels
(`src/f4/linalg/backend.jl:409`, `:485`, `:568`, `:644`).

### 4.2 What apply skips

`f4_apply!` (`src/f4/learn_apply.jl:479-544`) replays a fixed iteration count and does **none** of:
pair generation, Gebauer–Möller, pair selection by degree, the reducer search, or building the rows
that reduced to zero. `f4_symbolic_preprocessing!` for apply (`:294-363`) just re-multiplies the
recorded pairs, taking the multiplier's hash straight out of the table (`:319-324`). Column sorting
is skipped from the second apply onward (`:257-262`), and end-of-run redundancy and sort
permutations are replayed rather than recomputed (`:456-461`).

### 4.3 How a bad apply is caught

Three layers, and the failure mode is always `false` and never a wrong answer:

1. **Support check before anything runs** — `src/groebner/wrapped_trace.jl:91-106` compares every
   exponent vector of the new input against the learned one, called at
   `src/groebner/learn_apply.jl:225-226`.
2. **Per-iteration structural checks** (`src/f4/learn_apply.jl:271-289`): the apply linalg backend
   returns `false` on any zero row or non-invertible lead
   (`backend_learn_apply.jl:138-144`); then every new pivot's leading monomial is compared against
   `matrix_pivot_indices`; then the 64-bit pivot signature is compared.
3. **Recovery** (`src/groebner/learn_apply.jl:257-273`): on failure the coefficient buffer is reset
   from `input_basis`, the cached column order is dropped so the next apply re-sorts, `nfail` is
   incremented, and the public call returns `(false, polynomials)`. `Base.show` on a trace prints
   `apply : napply / nfail` (`src/f4/trace.jl:204`).

### 4.4 What it is for

The public `groebner_learn` / `groebner_apply!`, including a **batched form over several primes at
once** (`src/interface.jl:444`) which packs `N` primes' residues into `CompositeNumber{N, UInt64}`
(§5.2). Internally it is the **default strategy over Q**: `modular = :auto` selects
`:learn_and_apply` (`src/groebner/parameters.jl:376-380`), and
`_groebner_learn_and_apply` (`src/groebner/groebner.jl:240-387`) learns once modulo one lucky prime
and replays over batches of `composite × tasks` primes in parallel.

---

## 5. Linear algebra and arithmetic

### 5.1 Backends (msolve's, except the change-matrix one)

Dispatcher `src/f4/linalg/linalg.jl:144-172`. `backend.jl` is the deterministic reference with
**four** specializations of `linalg_reduce_dense_row_by_pivots_sparse!` — generic Zp reducing every
operation (`:369-437`), delayed arithmetic (`:440-520`), signed arithmetic (`:523-600`), generic
field (`:603-673`). `backend_threaded.jl` publishes new pivots through a compare-and-swap sentinel
protocol (`:83-89` `Atomix.replace!` with `acquire_release`, retry loop `:59-120`), engaged only
when `nlow >= 2*tasks` **and** `nleft + nright >= 1000` (`linalg.jl:128-142`).

**The randomized backend replaces the lower block by random linear combinations within row
blocks** — `backend_randomized.jl:66-69` — with `floor(sqrt(nrows/3)) + 1` blocks (`:32-34`),
redrawing until a block stops producing pivots (`:76`, `:118`). It is the **default**
(`parameters.jl:316-318` maps `:auto → :randomized`), and:

* **no failure probability is stated anywhere.** `src/interface.jl:107-109`: "Results are correct
  with high probability, however, no precise bound on the probability is known."
* it is disabled below characteristic 500 (`parameters.jl:294-307`);
* `linalg = :las_vegas` turns it Las Vegas by enabling a deterministic basis check and retrying
  (`parameters.jl:308-312`, `:262`);
* over Q the multi-modular lift checks (`src/groebner/modular.jl:373-403`) are the real net.

`linalg = :experimental_1/2/3` are accepted by the keyword validator (`keywords.jl:129-136`) and
have **no dispatch branch**, so they reach `throw(DomainError("Cannot pick a suitable linear
algebra backend"))` at `linalg.jl:168`. Likewise `selection ∈ {:normal, :sugar,
:be_divided_and_perish}` is accepted (`keywords.jl:174`) and **has no consumer**: selection is
always by minimal degree (`src/f4/f4.jl:308`). Two dead knobs, worth knowing before trusting a
keyword to change anything.

### 5.2 Arithmetic (Groebner.jl's own)

Every Zp reduction is a Shoup/Barrett multiply-high-and-shift over Julia's
`Base.MultiplicativeInverses.UnsignedMultiplicativeInverse` (`src/Groebner.jl:54`), core kernel
`src/arithmetic/Zp.jl:112-125`. Five implementations: `ArithmeticZp`,
`SpecializedArithmeticZp` (the default, specializing on `magic.add` as a *type* parameter),
`DelayedArithmeticZp`, `CompositeArithmeticZp`, and `SignedArithmeticZp`.

**Delayed reduction** budgets its own spare bits, `Zp.jl:163-171`:

```julia
n_spare_bits(a) = leading_zeros(divisor(a)) - (8 >> 1) * sizeof(T)
n_safe_consecutive_additions(a) = T(1) << (2 * n_spare_bits(a) - 1)
```

and the elimination loop reduces only every `n_safe` additions
(`src/f4/linalg/backend.jl:459-497`). It is selected automatically for
`2^16 <= p < 2^28`, `2^8 <= p < 2^12`, and `p < 2^4` (`Zp.jl:363-381`).

**Signed arithmetic** avoids the branch with the add-`p²` trick,
`src/f4/linalg/backend.jl:810-819`:

```rust
a = row[idx] - A(mul) * A(coeffs[j]);
a = a + ((a >> (8 * sizeof(A) - 1)) & p2);
```

**Accumulator width** is chosen from whether the coefficients were stored tightly, `Zp.jl:330-338`:
a tight `UInt32` coefficient accumulates in `UInt64`; a `UInt64` coefficient accumulates in
`UInt128`, and delayed arithmetic is then skipped (`:373`).

`CompositeNumber{N,T}` (`src/arithmetic/CompositeNumber.jl:5-7`) holds one rational coefficient's
residues modulo **N different primes in SIMD lanes**, default `N = 4`
(`src/utils/keywords.jl:29`). The *signed* composite kernels genuinely vectorize
(`backend.jl:825-847`); the unsigned one does not, and says so — `Zp.jl:210`:
`# No chance vectorizing this!`

### 5.3 The characteristic bound, which is the adapter's `MAX_CHARACTERISTIC`

Layered, and only partly enforced:

* **Enforced input validation**: `src/input_output/intermediate.jl:64-70` — nonnegative,
  `<= typemax(C)`, and `Primes.isprime`. A non-prime characteristic or an extension of degree > 1
  demotes the whole computation to `CoeffGeneric` (`src/input_output/AbstractAlgebra.jl:65-81`),
  which is a different and far slower implementation.
* **Representation**: `src/groebner/parameters.jl:174-175` asserts `0 < char < typemax(UInt64)`.
* **Not enforced**: `Zp.jl:24`'s `less_than_half` is an `@invariant`, and
  `invariants_enabled() = false` by default, so it compiles away.
* **Over Q the internal primes are always below 2^31** by design
  (`src/groebner/modular.jl:3-8`).

Measured, through the adapter's own script: a basis comes back at 2^31 − 1, 2^32 − 5,
Goldilocks 2^64 − 2^32 + 1, 2^64 − 353 and 2^64 − 59. Hence
`groebner_jl::MAX_CHARACTERISTIC = u64::MAX`, and hence the capability finding that matters most
for M25: **Groebner.jl and Sagebrush are the only comparands that accept a prime above 2^31**
(msolve and Singular both stop at 2^31 − 1), so above it there is no third party to check either of
them.

**And it is one ceiling, not two.** This is worth stating because the other two comparands have
task-specific bounds that a single constant would misrepresent: msolve's eliminant stops at
`1515531529` where its basis stops at `2^31`, and Sagebrush's FGLM stops at `2^31` where its basis
stops at `2^62` (`docs/research/sagebrush-implementation.md` §5.1.1). Measured here, Groebner.jl's
lex route returns the same basis and the same quotient dimension at every prime its basis route
accepts, up to `2^64 − 59` — which follows from §5.4: `LexBasis` is the *identical* F4 under a
different ordering, because there is no FGLM to have a narrower bound.

**One consequence for the corpus, now landed.** The Anemoi rungs are over `2^64 − 353`, and
Groebner.jl represents that field and returns a correct basis there — the same six leading
monomials and `vdim = 12` as the reference system at `2^30 + 3`. So the adapter's `supports()` says
**yes**, because [`ExternalSolver::supports`](../../src/grobner/external/contract.rs) is a
statement about declared capability and nothing else. The constraint on an Anemoi row was never
that no tool can represent it; it is that **nothing corroborates Groebner.jl above 2^31**, which is
a different and weaker claim. The rungs recorded `NoComparand` until `1d17b6e` (#341) and now
record

```rust
Equivalence::SoleComparand {
    tool: "Groebner.jl",
    reason: "2^64 - 353 is above Sagebrush's 2^62 gate and msolve's and Singular's \
             2^31, so Groebner.jl is the only external engine that reaches it",
}
```

which splits the question the way the evidence does: `licenses_timing()` is **true** — one engine
at one field on one machine is a valid ratio against a checkable invariant — and
`is_corroborated()` is **false**, because a two-way disagreement cannot name the odd one out.
Resolved as the intended encoding in #386, and **stated beside the figure** since #518: the board's
speedup table carries a provenance column reading `sole-comparand (Groebner.jl)` for these rungs
and prints `NOT CORROBORATED` in the cell of any ratio they publish.

### 5.4 Capability surface, confirmed by running it

`names(Groebner)` at 0.10.11 is exactly `DegLex, DegRevLex, InputOrdering, Lex, MatrixOrdering,
ProductOrdering, WeightedOrdering, dimension, groebner, groebner_apply!, groebner_learn,
groebner_with_change_matrix, isgroebner, leading_ideal, normalform, quotient_basis`. Grepping the
tree for `fglm`, `eliminant` and `kbase` returns **zero hits**, and there is no solver.

So, for the task taxonomy in `src/grobner/external/contract.rs`:

| `Task` | Groebner.jl 0.10.11 |
|---|---|
| `ReducedGrobnerBasis` | **yes**, under Lex, DegLex or DegRevLex |
| `LexBasis` | **yes**, by a *direct lex F4* |
| `LexBasisByConversion` | **no** — there is no FGLM |
| `UnivariateEliminant` | **no** |
| `OneFiniteFieldSolution`, `AllFiniteFieldSolutions` | **no** |
| `CryptanalyticWitness` | **no** |

`quotient_basis` and `dimension` are useful independent invariants and are what the adapter's
`@vdim` and `@dim` markers carry. **Confirming the coordinator's conjecture: none of the four M25
comparands enumerates finite-field solutions** — msolve returns a rational parametrization over a
prime field (`external-comparands.md` §3.5), Singular's `solve` is numerical, Sagebrush exposes no
variety in Rust (`docs/research/sagebrush-implementation.md` §5), and Groebner.jl has no solver at
all. `OneFiniteFieldSolution` and `AllFiniteFieldSolutions` therefore have **no external comparand
at any characteristic**. That is a result for the competitive report, not a gap in it.

---

## 6. Hypotheses for Zeebra, each with the measurement that would settle it

**The premise correction first, because three of these would otherwise be aimed at the wrong
stage.** M16's "elimination is 65–88% of F4 runtime" is obsolete and must not be cited:
`docs/MILESTONE-F4-OPTIMIZATION.md` §8.5 measures elimination at **7–22%** after M16's own
optimizations, and names the two stages that replaced it:

| system | order | total | symbolic | construction | elimination | interreduction |
|---|---|---|---|---|---|---|
| katsura-6 | lex | 19.53 | 4.42 | **9.33 (48%)** | 1.28 (7%) | 2.33 |
| cyclic-5 | lex | 3.14 | 0.65 | **1.48 (47%)** | 0.37 | 0.35 |
| katsura-7 | grlex | 46.72 | 2.58 | 6.21 | 8.00 (17%) | **28.71 (61%)** |
| katsura-7 | grevlex | 32.13 | 1.64 | 5.53 | 7.12 (22%) | **16.90 (53%)** |

**#269's title still cites 65–88%.** Whatever #269 becomes, its premise needs replacing with the
table above, and a hypothesis that buys 2x on elimination now buys at most 1.2x overall.

Every hypothesis below is stated with the measurement that would confirm *or refute* it, and the
measurement is an existing Zeebra instrument — `examples/f4_profile recommended`, whose columns are
the ones in that table.

### 6.1 Replace the per-matrix monomial→column `HashMap` with a persistent interning table

**The best-aimed hypothesis in this study**, because it targets the stage §8.5 names as the largest
on lex, and it is a data-structure change rather than an algorithm change.

§8.5's own diagnosis: matrix construction "is now the largest stage there, because the pair
criteria replaced 59 large matrices with 107 small ones and construction's per-matrix cost (the
monomial-to-column `HashMap`, the sort) does not shrink with the matrix." Groebner.jl pays that cost
once per *run* rather than once per *matrix*: monomials are interned in a persistent table, and
`labels` (§3.2) **is** the column index — there is no second dictionary, and a monomial that was
already seen is already numbered. The hash never recomputes on resize (`hashtable.jl:224-262`), and
migration out of the frontier table reuses the stored hash (`matrix.jl:380`).

* **Confirms it:** the `construction` column drops on katsura-6 lex (from 9.33 ms of 19.53) and
  cyclic-5 lex (1.48 of 3.14), and the drop scales with the *matrix count*, which the pair criteria
  pushed to 107 on katsura-6 lex.
* **Refutes it:** construction is dominated by the column *sort* rather than the map, in which case
  the interning table changes little and §6.2 is the right target instead. The sort and the map are
  separable, so **measure them apart before building anything** — that is the cheap first
  experiment and it is a one-counter change to `examples/f4_profile`.

### 6.2 Cache the total degree in `Monomial<N>`

Groebner.jl stores the degree in *every* representation (§2.3) and never recomputes it; Zeebra's
`degree()` sums `[u32; N]` on each call (`monomial.rs:53`). Under a degree order, every comparison
needs the degree, so the sum is on the hot path of selection, sorting and interreduction.

* **Confirms it:** `interreduction` falls on katsura-7 grlex (28.71 ms of 46.72) and grevlex
  (16.90 of 32.13), and `symbolic` falls on the lex instances. These are the two largest remaining
  costs.
* **Refutes it:** no measurable change, which would mean LLVM already hoists the sum out of the
  comparison loops for small `N` — entirely possible at `N = 7` with a fully unrolled array. A
  microbenchmark of `MonomialOrder::cmp` is the five-minute version of this experiment and should
  precede touching the type, because `Monomial` is serialized (`monomial.rs:17`) and a new field is
  a format change.

### 6.3 Pack small-`N` monomials into one `u64` so a degree comparison is one integer compare

The §2.4 trick: degree in the top byte, variables laid out so an unsigned word compare is
degree-then-reverse-lex. At `N <= 7` with 8-bit exponents, a Zeebra monomial goes from 28 bytes to
8, and `cmp` under grevlex goes from an array walk to one instruction. Zeebra's whole benchmark
corpus at the sizes that matter — katsura-7 is 7 variables, cyclic-5 is 5 — sits inside that bound.

This subsumes §6.2 and is strictly more work. **Do §6.2's microbenchmark first**: if caching the
degree alone captures most of the comparison win, packing is not worth a second monomial type and
an overflow-retry path. Groebner.jl can afford seven representations because
`MonomialDegreeOverflow` plus `hint = :large_exponents` (§2.2) lets it retry the whole computation
wider; Zeebra has no such retry, so a packed representation means building that escape hatch too.

* **Confirms it:** `interreduction` and `symbolic` both fall on katsura-7 grevlex beyond whatever
  §6.2 achieved, and the gap between the two measurements is the packing's own contribution.
* **Refutes it:** the gap is within noise, i.e. the win was the cached degree and not the word
  compare. This box's noise floor is the reason to interleave (`docs/research/` perf A/B method).

### 6.4 Do **not** port the divmask first

It is the most elegant thing in §3 and its headroom in Zeebra is capped at about 5%.

The divmask accelerates divisibility scanning, which lives in symbolic preprocessing. §8.5 puts
`symbolic` at **2.58 ms of katsura-7 grlex's 46.72 (5.5%)** and 1.64 of 32.13 on grevlex. A divmask
that eliminated symbolic preprocessing *entirely* would buy 1.06x. It also costs a 32-bit field per
interned monomial, a calibration pass, and the §3.3 caveats — thresholds fixed on the input, and no
coverage past 32 variables.

* **Would make it worth revisiting:** `symbolic` rising above ~20% of total on some instance, which
  is exactly what §6.1 and §6.2 succeeding would cause. Re-read this section after them, not
  before.
* **Measurement:** the `symbolic` column. If it is still single-digit percent, the answer is no
  regardless of how good the technique is.

### 6.5 A learn/apply trace for same-shape cryptanalysis families

Groebner.jl's traces amortize over **many primes for one rational system** (§4.4), which Zeebra has
no use for — it computes over finite fields and has no multi-modular loop. But the trace's actual
precondition is weaker than "same system, different prime": `wrapped_trace_check_input`
(`wrapped_trace.jl:91-106`) requires the same *monomial support*, and the coefficients may differ
freely.

Zeebra's cryptanalysis sweeps solve many instances of **identical shape with different constants** —
Anemoi and Poseidon CICO at different round constants. Those share monomial support exactly. §4.2's
list of what apply skips maps onto §8.5's `symbolic` + `construction`, which is **13.75 ms of
katsura-6 lex's 19.53 — 70%**.

* **Confirms it:** across a family of same-shape instances, the second and later solves lose most
  of their `symbolic` and `construction` time. The measurement is per-instance F4 stage timings over
  one cryptanalysis family, which the existing scoreboard machinery already collects.
* **Refutes it:** the pivot schedule does not actually transfer — different constants change which
  rows reduce to zero, which §4.3's layer 2 catches as a failed apply. **That is the thing to test
  first and it is cheap:** instrument an existing family to record each instance's leading-monomial
  sequence and matrix shapes, and check whether they coincide. If they do not, the whole hypothesis
  dies for the cost of a counter, and that is the honest order to find out.

### 6.6 Do **not** port randomized linear algebra

Zeebra's value proposition is a checked answer, and §5.1 is clear that Groebner.jl's default
randomized backend **has no stated failure bound**. Buying at most 22% of elimination for an
unquantified probability of a wrong basis is a bad trade here, and the Las Vegas variant
(`parameters.jl:308-312`) pays for its certainty with a full deterministic basis check — which is
most of the saving back.

* **Would change this:** elimination returning to dominance on some instance *and* a Las Vegas
  formulation whose check is cheaper than the saving. Both conditions, not either.

### 6.7 Delayed reduction in the elimination accumulator

§5.2's `n_safe_consecutive_additions` is a clean, self-budgeting formulation and Zeebra's
`-C target-cpu=x86-64-v3` floor makes the wide accumulator cheap. The share is the problem:
elimination is 7–22%.

* **Confirms it:** the `elimination` column falls on katsura-7 grlex (8.00 ms of 46.72) and grevlex
  (7.12 of 32.13), the only two instances where elimination is above 10%.
* **Refutes it:** Zeebra's accumulator already delays, or the field types in play have too few spare
  bits for `n_safe` to exceed 1 — which is the case for a 64-bit prime in a `u128` accumulator, and
  Goldilocks is one of Zeebra's main fields. **Check the spare-bit arithmetic for Zeebra's actual
  fields before implementing anything**, because for the large primes the answer is arithmetic
  rather than empirical.

---

## 7. Verdicts

**Licensing: algorithmic reference only, and more firmly so than the one-line classification
suggested.** Groebner.jl elects GPL-2.0 (`src/Groebner.jl:1`), declares itself an adaptation of
GPL-2.0-or-later msolve (`:8-15`), and embeds GPL-3.0-or-later code from AlgebraicSolving.jl
(`src/groebner/auxiliary.jl:240`) — §1.1. **No line of it may enter Zeebra's MIT core.** Running it
as a subprocess creates no derivative work in either direction
(`docs/research/external-provenance-policy.md` §7), which is exactly and only what
`src/grobner/external/groebner_jl.rs` does: it writes a script, spawns `julia`, and parses text.

Groebner.jl is also the **worked example of a licence-compliant adaptation** — named upstream, named
licence, enumerated list of what was taken, in the first fifteen lines of the entry point. Zeebra
cannot do that for a GPL upstream because the result would be GPL; it is precisely what Zeebra
*would* have to do for Sagebrush, where reuse is permitted
(`docs/research/sagebrush-implementation.md` §7).

**What to carry into #264.** The hashtable, the pairset and Gebauer–Möller, symbolic preprocessing,
the matrix sorting and every linear-algebra backend are **msolve's design** (§1), so a reading of
them here and a reading of them in C are not two witnesses. The parts that are Groebner.jl's own —
the monomial encodings (§2), the arithmetic (§5.2), the trace (§4) — are the parts #264 cannot
cover, and are where §6's two best hypotheses come from.

**Priority order for Zeebra**, which is not the order of elegance: §6.1 (interning table, aimed at
48% of lex), then §6.2's microbenchmark (cached degree, aimed at 61% of grlex), then §6.5's
cheap transfer test (same-shape traces, aimed at 70% of katsura-6 lex), and **not** §6.4 or §6.6
until a measurement says otherwise.

> ### That order is superseded — #447 measured the comparand
> **`docs/research/groebner-jl-gap.md`** re-screened all seven hypotheses against **grevlex shares
> on `mq-random-10`**, the instance every competitive row is measured on, instead of lex and grlex
> shares on katsura and cyclic. Five of the seven are bounded at or below **1.16x** there, including
> **§6.1 at 1.04x** — construction is 3.43% of that run, not 48%. Only §6.2 and §6.3 survive, and
> they survive because they are not stage hypotheses at all: they attack a per-operation constant
> measured at **11.6x–25.5x uniformly across every stage**.
>
> Two corrections to the sections above, both measured rather than argued:
> * **§6.6 understates what it declines by about 20x.** Randomized linear algebra is worth **4.89x**
>   to Groebner.jl on that instance (424.6 ms deterministic against 86.8 ms). The won't-do verdict
>   is unaffected — the correctness argument is independent — but the factor is a permanent floor on
>   the comparison, not "at most 22% of elimination".
> * **§6.7 has no comparand behaviour to imitate at Zeebra's reference prime.** Groebner.jl ran that
>   instance on `SpecializedArithmeticZp`, not `DelayedArithmeticZp`, because `p = 2^31 − 1` is
>   outside every window `Zp.jl:363-381` selects delayed arithmetic for.
>
> And the item that now ranks first is **not in §6**: Groebner.jl's final interreduction is one
> Macaulay matrix (`src/f4/f4.jl:106-171`, measured at 250 × 604 and **1.74 ms**) where Zeebra runs
> 247 sequential polynomial divisions and spends **24.1 s**. §6 looked for stages to speed up; that
> stage needs replacing.
