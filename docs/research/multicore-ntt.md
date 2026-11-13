# Multicore NTT: caller and crossover gate (#732)

**Measured at:** `e22b9b58cd29fd074a4234593d8790303a99c5f5` plus the
[reporting-only probe](../../research/ntt-caller-gate/probe.patch), 2026-11-13.
The [manifest](../../research/ntt-caller-gate/manifest.json) binds compiler,
lockfile, effective build configuration, binary, source and input SHA-256s.
The [predeclared plan](../../research/ntt-caller-gate/PLAN.md), raw outputs and
reproduction commands are retained with it. No transform implementation changes.

**Verdict: defer a multicore/tiled implementation.** A reachable, large NTT
caller exists: the public Graeffe **one-root** polynomial example. That warrants
retaining a bounded future experiment, but neither its enclosing forward-stage
timer nor #591's access curve measures the transform-only eligible wall share.
#592's worker-count-specific dispatch/barrier table is also unfinished at this
audit ([draft PR #735](https://github.com/mfaulk/zeebra/pull/735), `aaa4255d`). This gate does not establish a multicore crossover or justify integration.
It does establish which caller and costs a later proposal must measure. This is
a completed research decision, not a claim that NTT cannot benefit from cores.

## Reachability at the source pin

| caller | actual route | field/size constraint | disposition |
|---|---|---|---|
| F4/FGLM polynomial arithmetic | `Mul` / generic field arithmetic; not `fft::multiply` | no `KnownOrder` requirement in core | no direct NTT work to accelerate |
| Explicit `multiply` / `try_multiply_via_fft` | two evaluations, pointwise product, inverse transform; next power of two above product degree | needs that radix-2 root; fallback is schoolbook/Karatsuba | reachable public arithmetic, but multiplication diagnostics alone do not establish a solver application |
| Generic multipoint/subproduct tree | `SubproductTree::build`, `div_with_remainder`, generic `Mul` | `FiniteField` only; arbitrary abscissae | no current NTT; #606 owns transform arithmetic economics before any parallel tree proposal |
| Resultant, reference route | `lagrange_interpolate`, through generic tree at large sizes | arbitrary consecutive points | no current NTT interpolation to thread |
| Resultant, explicit subgroup route | `bivariate_resultant_ntt_with`: sample determinants, join workers, then `interpolate` | `interpolation_route`: degree bound rounded up, with root availability checked | reachable inverse NTT; charge extra determinant samples and domain construction, not just interpolation |
| Graeffe, order two | `graeffe_root_with_stats` → `graeffe_2_over_domain` → two `evaluate` + one `interpolate` per step | `next_power_of_two(degree+1)`; KoalaBear's odd residual is only 127 | selected complete arithmetic caller, below |
| Graeffe, odd steps | `graeffe_l_over_domain`, products of scaled copies via `multiply_over_domain` | domain must hold the expanded product; `plan_odd_steps` also gates search economics | a different arithmetic/memory question; no extrapolation from the selected order-two case |
| Reed–Solomon | coefficient `encode` uses `evaluate`; `decode` uses interpolation and further polynomial arithmetic | caller supplies valid domain; systematic encoding/erasures include generic interpolation | genuine consumer; current guide's `[16,10]` example is too small to justify a large-transform campaign |
| Non-power-of-two DFT / Bluestein | `prime_factor::transform_any`; prepared Bluestein reduces large prime factors to radix-2 convolution | original root and convolution root must both exist | separate algorithm/domain sizing; a radix-2 curve does not price the complete prime-length route |

Source anchors: [multiplication](../../src/fft/multiply.rs),
[generic tree](../../src/poly/univariate/subproduct_tree.rs),
[resultant](../../src/grobner/resultant.rs),
[Graeffe](../../src/poly/univariate/graeffe.rs),
[codes](../../src/codes/reed_solomon.rs),
[prime-factor dispatch](../../src/fft/prime_factor.rs).
Search both the root reexports and `fft::` names when repeating the census.

Resultant sampling workers **finish before** interpolation at this revision;
there is no current nested NTT pool. A later outer pipeline processing several
resultants, or transform work added inside sampling, would need a shared worker
budget. Multiplying outer workers by inner workers would oversubscribe. Historic
resultant stage shares are not current measurements: #598 and the matched-kernel
study changed the arithmetic. Reuse those instruments before proposing inner NTT
workers. The original subgroup route's sample-padding cost remains real.

## Field and domain limits

These are algebraic/source-derived bounds, not affordable allocation sizes. For
radix two, `n <= 2^s`, where `s = v2(q-1)`. For nonzero input products of degrees
`a,b`, `n = next_power_of_two(a+b+1)`; for order-two Graeffe,
`n = next_power_of_two(d+1).max(2)`.

| field / representation | element bytes | s | largest radix-2 n | coefficient array at that n |
|---|---:|---:|---:|---:|
| GF(32003), u32 / u64 | 4 / 8 | 1 | 2 | 8 / 16 bytes |
| Mersenne31, current u32 | 4 | 1 | 2 | 8 bytes |
| Zp65537, u64 | 8 | 16 | 65,536 | 512 KiB |
| KoalaBear, current u32 / example u64 | 4 / 8 | 24 | 16,777,216 | 64 / 128 MiB |
| BabyBear, current u32 | 4 | 27 | 134,217,728 | 512 MiB |
| Goldilocks, u64 | 8 | 32 | 4,294,967,296 | 32 GiB |
| BN254 Fr | 32 | 28 | 268,435,456 | 8 GiB |
| BLS12-381 Fr | 32 | 32 | 4,294,967,296 | 128 GiB |

Computed from the current modulus definitions and `two_adic.rs`, with existing
root/decomposition tests as the independent regression checks. The older
[fast-univariate table](fast-univariate.md#11-the-two-adicity-figures-verified-rather-than-quoted)
uses historical eight-byte representations for some narrow fields; those widths
are not the current `fields::KoalaBear` / `fields::BabyBear` aliases. No large
radix-2 NTT is available over either primary MQ10 field here. Availability over
Goldilocks says nothing about either MQ field or a wide-field memory budget.
Binary fields GF(2^m) have odd multiplicative-group order, so no nontrivial
radix-2 domain; they are excluded from this experiment. Current binary-field
integer embedding also prevents the usual inverse-transform normalization.

## Selected caller and bounded serial profile

The [existing public example](../../examples/graeffe_root.rs) constructs a dense
random cofactor times four planted linear factors. The selected large degree is
`3^13 = 1,594,323`, giving maximum `n = 2^21`; the small control is `3^8 = 6561`,
giving `n = 2^13`. These are complete public polynomial arithmetic examples,
**not** imported eliminants, all-roots solves, or full elimination tasks. Their
field/seed/coefficient encoding and SHA-256s are in the manifest. Every returned
root is retained and checked by evaluation of its original polynomial. That is
an exact certificate for this one-root task; there is no claim of completeness
of a root set or of a Gröbner basis.

See the generated [stage table](../../research/ntt-caller-gate/table.md).
All 18 attempts completed: three identity executions and 15 timing executions,
with no time/memory stops or verification failures. The large u64 call median
was 3.162440 s (range 3.135908–3.199303 s), with maximum process RSS 221,156 KiB;
the current u32 caller median was 2.488752 s (2.461371–2.510976 s), with maximum
RSS 111,644 KiB. These are different-seed caller profiles, not a measured width
speedup. Median forward fractions were 97.74% and 97.79%, respectively, versus
94.94% for the small control. Source/model evidence therefore **does not reject
parallelism for lack of work**; it defers a prototype until eligible work and
runtime cost are distinguished.

Using the enclosing-stage fraction as the optimistic bound gives about 6.91x
at p=8 and 26.38x at p=64 for the large u64 call. These are mathematical upper
ceilings under unrealistically perfect forward scaling, not predictions.
Each large profile reports 72 transforms, summed sizes 75,496,704 elements,
and 18,023,881 stored coefficients. Call-attributed peak live heap is
194,655,368 bytes (u64) / 97,327,976 bytes (u32), distinct from process RSS and
the conservative storage reservations below. Initial load under lock was 4.83,
ending at 4.79; other builds were possible. Large-call ranges are below 2.1%
of the median, while small-call noise is wider. No noisy baseline comparison
or uninstrumented speed claim is made.

Five interleaved fresh processes per case, one physical core, with identity
executions excluded. The enclosing call is unmodified; the patch writes input
identity before its timer and reports exact existing timers after verification.
The raw output retains forward/subgroup/descent duration, total call duration,
maximum transform size, sum of transform sizes, retained coefficients and peak
live allocated heap. Full-process wall/CPU/RSS includes input construction,
verification and printing; it is not interchangeable with the arithmetic timer.
Counting-allocator overhead is inherited from the existing example; these are
profiles, not an uninstrumented adoption campaign.

Forward time includes domains, parity splitting, three transforms, pointwise
squaring/combining, normalization, folding and retained-polynomial handling.
Consequently `s_NTT <= forward_time / total_time`; for a later p-worker proposal,
`1 / ((1-s_forward) + s_forward/p)` is only an optimistic **upper** ceiling.
Do not substitute the number of transforms, products or bytes for elapsed share.
No transform-only wall fraction, speedup or p=1–64 curve is asserted here.

## Cost and memory before scheduling

The current radix-2 kernel has `log2(n)` stages with `n/2` butterflies per stage.
Each butterfly performs one field product and two add/subtract operations.
There is one serial bit-reversal permutation before stages. Domain generation
materializes n powers; the inverse builds an inverse domain through batch
inversion and scales n coefficients. Threading butterfly stages does not remove
those costs or the caller's parity/copy/fold/retention costs.

A stage-partition design needs a barrier between successive stages. Partitioning
only complete `chunks_mut(m)` gives `n/m` independent jobs: at `m=n`, one job
remains. Keeping p workers useful late in the transform requires splitting
butterflies **within** a block, with disjoint output slices and shared immutable
twiddles. Repartitioning each stage also has a cost. Do not choose a block-only
implementation and interpret its last-stage serialization as a hardware limit.
For each stage, compare useful work to the measured #592 p-worker batch+barrier
cost `D(p)`. A necessary, optimistic bound is
`T_NTT(1)*(1-1/p) > log2(n)*D(p)` per transform. Bit reversal and other serial
work make the real bound stricter. Without `T_NTT(1)` and `D(p)`, there is no
numerical worker crossover. Never replace D(p) with a guessed nanosecond value.

A source-level traffic count, **not measured DRAM traffic**, is `2nB` value
read/write bytes plus up to `nB/2` twiddle-load bytes per stage. Cache reuse can
change the latter and DRAM traffic in both terms. At n=2^21, B=8, 21 stages
account for 840 MiB of nominal value/twiddle traffic per transform, excluding
permutation, domains and caller work. The 32-bit representation halves this
byte count, not necessarily elapsed time. The historical #591 curve
[§6.3.1](graeffe-root-finding.md#631-the-binary-landed-and-the-answer-access-binds-at-1632-mb-and-not-at-the-l3-boundary)
observes a rate drop around 16–32 MB of coefficients. It does not identify an
L3 capacity boundary, measured memory bandwidth, or a multicore win. This study
reuses that result and does not rerun the standalone sweep.

| component, largest selected n | u64 accounting | interpretation |
|---|---|---|
| original input, `(d+1)B` | 12,754,592 bytes | outside call-attributed heap baseline |
| one n-element vector/domain | 16 MiB | each caller/domain allocation must be counted |
| current Graeffe step plus domain | up to `4nB = 64 MiB` | source's step workspace model; add retained polynomials |
| retained polynomials, conservative `24(d+1)B` | 306,110,208 bytes | upper reservation for order-two outputs, not observed simultaneous RSS |
| input + retention bound + step workspace | 385,973,664 bytes | conservative coefficient-storage bound, excluding allocator/capacity/runtime overhead |
| one out-of-place transpose buffer | +16 MiB | one shared reusable scratch vector, if that design is chosen |
| one full n-element buffer per worker at p=64 | +1 GiB | avoid this naive design; not required by butterfly partitioning |

All attempts are externally capped at 60 seconds and 2 GiB address space, with
process peak RSS separately recorded. The address-space limit is a hard guard,
not a claim to measure resident use. Production entry/byte budgets are untouched.
A future design must reserve total simultaneously live storage before allocation
and account for capacities, worker stacks, queues and retained polynomials.
At the declared 1.25x serial RSS adoption ceiling, merely being below 2 GiB is
insufficient. No NUMA/first-touch speedup is inferred from a one-core profile.

## Locality, arithmetic and independent jobs are separate factors

[Bailey, *FFTs in External or Hierarchical Memory*, pp. 2–3, 7](https://www.davidhbailey.com/dhbpapers/fftq.pdf)
factors n into two dimensions. Its six-step variant adds three transposes around
two families of short transforms and a twiddle multiplication. This motivates
contiguous short transforms; it does not transfer its Cray performance to NTT.
For an out-of-place implementation here, three unfused transposes alone cost
`6nB` read/write bytes and a reusable `nB` scratch vector; the twiddle pass adds
n products and `2nB` value traffic. Compare those charges against permutations
and locality savings at p=1 before attributing any gain to threads.

[Frigo–Johnson, *The Design and Implementation of FFTW3*, §II and §IV-D](https://math.mit.edu/~stevenj/papers/FrigoJo05.pdf)
discusses radix/decomposition choice, recursive locality and reordering. Its
floating-point operation economics do not determine finite-field radix costs.
A serial radix-4/tiled proposal would need a field-specific product/add count,
root/layout proof and comparison with the current serial kernel. No transform
code or external GPL implementation is imported in this gate.

For the selected order-two caller, the two forward evaluations in **one** step
are independent, but the inverse needs their combined values and the next
Graeffe step needs the previous polynomial. Parallelizing independent forward
transforms therefore offers at most two jobs at that point, and simultaneous
values/parity buffers can raise peak storage. Independent products/tree nodes
are another route; the generic tree currently supplies no transform jobs and
#606 must settle that arithmetic choice. An inner-stage pool, two independent
transforms, and parallel tree levels require separate experiments and one
shared thread budget. They are not multiplicative speedup factors.

## Reopening gate and uncertainty

Keep the current serial transform and dispatch policy. Before a separate bounded
prototype, obtain #592's warm/cold dispatch/barrier curves, separately measure
eligible transform wall time within this pinned caller, and inspect whether
bit reversal, inverse-domain construction or locality is the cheaper first
change. The saved large example makes that follow-up concrete without inventing
a solver workload. The manifest's different-width seeds preclude an identical-
input width speedup claim. A real eliminant would require its own canonical
input/provenance and complete-task profile.

The [plan](../../research/ntt-caller-gate/PLAN.md) predeclares numerical wall/RSS
adoption and small-control regression thresholds for that follow-up, plus all
1–64 worker counts and refusal rules. Today there are no parallel arms, so no
scaling, SMT, cancellation, atomic-publication or race claims to validate. No
production policy or new runtime dependency follows from this study. Exact NTT
share, measured scheduling cost, useful worker count, tiled crossover and
complete-elimination benefit remain **unknown**. The research maintenance cost
is the retained profile parser/provenance checks; a runtime would add failure,
shutdown, nesting and resource-accounting obligations not paid for here.
