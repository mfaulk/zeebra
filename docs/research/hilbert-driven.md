# A Hilbert-driven cap, against a cap chosen without one

Reference for M22-C (#74). Every figure comes from

```sh
tools/fetch-mq-challenge.sh
cargo run --release --example hilbert_driven -- <instance>     # one instance per process
```

under `F4Options::recommended()` with `profile_degrees`, `max_matrix_columns = 60_000`,
`max_live_bytes = 400 MB` (slack: the effective live cap is the `min` of the two budgets, so `max_live_nonzeros` bound first at 20 000 000 entries — **320 MB** over these fields' 16-byte entry; #322, #469), `max_batches = 20_000`, grevlex throughout. **Every row's basis is
asserted equal to the uncapped baseline's, and every row is also run with `certify` on and asserted
to pass** — a differing basis would be a defect, not a result.

## 1. What is being compared, and against what

M22-B established the quantity:

```text
N_d = (predicted dim I_d) − dim (current leading-term ideal)_d
```

The second term is **exact**; the first is the semiregular prediction, which M22-B measured exact on
random and genuine overdetermined MQ and wrong — in the unsafe direction — on the inhomogeneous
systems this milestone is about. `N_d` inherits that error, so the design does not let completeness
depend on it:

- `CertifiedLimited { slack }` caps the batch at `N_d + slack`; the pairs not taken stay **pending**
  and are the next thing selected, because degree is primary under every schedule.
- `Deferred { slack }` moves the rest of the degree out of the pending set and goes on, promoting
  them back before the loop can end. While deferred they stay visible to Gebauer–Möller and are
  **not** recorded as processed, so the chain criterion cannot use one as a witness.

Both are complete by construction. A wrong prediction costs batches, never the answer. **§4 is the
verdict on the second one**: it is correct and it is unusable, and the failure is a refused budget
rather than a wrong basis, which is what the design was for.

**The reference is the fixed cap, not the uncapped baseline.** M22-A measured a plain cap of 64 at
3.6x on Fukuoka type III `n=10`, with no prediction and no certification — and M22-B measured the
Hilbert-derived quota at the decisive degree on that same instance as 65. A strategy that beats
"uncapped" while losing to "cap 64" has established nothing.

`held` below is pairs a cap left pending for a later batch **at that degree** — not across the
queue, which would charge a cap with withholding pairs it was never offered. `pred/obs` is the
predicted new leading monomials against the new basis elements the same degrees produced, so below
one means the prediction caps too hard.

## 2. Fukuoka type III `n=10`, the instance where capping pays

| configuration | pairs | batches | held | cols | peak entries | solve ms | cert ms | **total ms** |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| uncapped | 743 | 6 | 0 | 859 | 168 020 | 118.6 | 0.4 | 118.9 |
| fixed cap 256 | 499 | 6 | 0 | 821 | 111 063 | 65.0 | 0.4 | 65.4 |
| fixed cap 64 | 334 | 8 | 0 | 652 | 60 809 | 32.7 | 0.4 | **33.1** |
| fixed cap 16 | 295 | 21 | 0 | 596 | 48 755 | 37.9 | 0.3 | 38.2 |
| observe | 743 | 6 | 0 | 859 | 168 020 | 117.7 | 0.3 | 118.0 |
| hilbert limited+0 | **280** | 180 | 20 959 | 534 | **43 381** | 136.4 | 0.4 | 136.7 |
| hilbert limited+4 | 288 | 49 | 5 420 | 577 | 47 073 | 59.1 | 0.3 | 59.4 |
| hilbert limited+16 | 298 | 15 | 1 576 | 598 | 50 843 | 30.5 | 0.3 | **30.8** |
| hilbert deferred+0 | 264 | 164 | 3 414 | 509 | 41 810 | 107.0 | 0.3 | 107.3 |
| hilbert deferred+4 | 289 | 51 | 1 607 | 577 | 47 073 | 58.6 | 0.3 | 58.9 |

Four things here, in order of how much they decide.

**The Hilbert cap at slack 16 is the fastest configuration measured — 30.8 ms against the best fixed
cap's 33.1 ms and the uncapped 118.9 ms.** That is 3.86x over uncapped and **1.07x over a cap picked
without any model**, which is inside this machine's run-to-run variation. So the honest statement is
that the Hilbert-derived cap *matches* the best fixed cap and finds it without tuning — which is
worth something, and is not the 1.25x M22-I asks for.

**The prediction underestimates by 39%** (`pred/obs = 103/168`), exactly M22-B's unsafe direction on
an inhomogeneous instance, and here it manifests as capping too hard rather than as a wrong answer —
which is what the deferred-not-discarded design is for. The slack is what repairs it, and the
required slack is large: 0 is 4.4x slower than 16.

**Minimum memory and minimum time are different optima, and the Hilbert cap at slack 0 picks the
memory one.** `limited+0` has the smallest matrices of anything measured — 534 columns and 43 381
peak entries, a **74% reduction** from uncapped — while being the slowest capped configuration,
because 180 batches pay the per-matrix cost 180 times. A caller bounded by memory and a caller
bounded by time want different slacks.

**Deferral does what it was predicted to — here.** `deferred+0` reduces 264 pairs against
`limited+0`'s 280 and the uncapped 743 — a 64% reduction — and is 1.28x faster than `limited+0`
despite deferring 3 414 pairs and promoting them all back. By the time they return the basis is
larger, so more are eliminated and the rest reduce against more reducers. It is still 3.2x slower
than `limited+16`, and **§3 shows the same mechanism being 214x slower on a structured system**, so
this row is not evidence that deferral is a good idea.

## 3. Poseidon, where the prediction is 27x wrong

| configuration | pairs | batches | held | cols | peak entries | solve ms | cert ms | total ms |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| uncapped | 409 | 13 | 0 | 925 | 103 112 | 142.2 | 4 824.7 | 4 966.9 |
| fixed cap 64 | 409 | 15 | 0 | 919 | 78 038 | 140.0 | 4 853.5 | 4 993.4 |
| fixed cap 16 | 390 | 30 | 0 | 897 | 52 447 | 168.5 | 4 836.0 | 5 004.5 |
| observe | 409 | 13 | 0 | 925 | 103 112 | 126.6 | 4 890.6 | 5 017.1 |
| hilbert limited+0 | 403 | **400** | 21 412 | 916 | **50 274** | **918.0** | 4 904.4 | 5 822.4 |
| hilbert limited+4 | 406 | 107 | 5 484 | 908 | 51 565 | 326.7 | 4 779.7 | 5 106.4 |
| hilbert limited+16 | 390 | 30 | 1 062 | 897 | 52 447 | 162.4 | 4 877.6 | 5 040.1 |
| hilbert deferred+4 | 1 133 | 259 | 12 779 | 9 472 | 854 834 | 4 152.4 | 4 931.2 | 9 083.5 |
| hilbert deferred+0 | **1 514** | 1 147 | 55 370 | **19 779** | **3 552 410** | **30 416.3** | 5 265.3 | 35 681.6 |

`t=2 R_F=2 R_P=2`, nine S-box variables. `pred/obs = 4/107`: the model predicts **four** new leading
monomials where a hundred and seven appear. That is a 27x underestimate, and it is the same sign
M22-B measured on the inhomogeneous Poseidon system — so this is a confirmation, not a surprise.

The consequence is exactly what the sign predicts: the cap at slack 0 splits 409 pairs into **400
batches**, one pair each, and the solve goes from 142 ms to 918 ms — **6.5x slower**. The pair count
barely moves (409 to 403), so there is no work to avoid; all 400 matrices are overhead.

The memory story survives for the *limiting* modes: 50 274 peak entries against 103 112, a 51%
reduction. But a fixed cap of 16 reaches 52 447 at 168 ms, so the prediction buys 4% less memory for
5.5x the time.

### Deferral is catastrophic here, and the reason generalizes

The last two rows are the strongest negative result in M22. `deferred+0` reduces **1 514 pairs
against the uncapped 409** — 3.7x *more* — in 1 147 batches, reaching **19 779 columns against 925**
and **3 552 410 peak entries against 103 112**. That is 21x wider, 34x more memory, and **214x
slower**. The basis it returns is still correct — asserted equal to the baseline's, as every row is —
so this is a performance catastrophe and not a correctness one.

The mechanism is the degree-by-degree discipline that deferral abandons. Capping a batch keeps the
computation at the same degree; deferring the rest of a degree moves it to a *higher* one with the
lower degree unresolved. On an inhomogeneous system the ascending-degree order is doing real work —
it is what keeps intermediate polynomials small — and working at degree `d + 1` before degree `d` is
finished produces relations that then have to be reduced against a basis that is missing the
low-degree elements which would have simplified them. The deferred pairs come back later against a
basis built from those larger relations, and the effect compounds: `pred/obs` moves from 4/107 to
812/896, because the degrees visited are no longer the same degrees.

So `pred/obs` is **not comparable across modes that change which degrees are visited**, and deferral
is one. The two limiting modes are comparable with each other and with the fixed caps; the deferring
ones are only comparable with themselves.

## 4. Deferral turns a solvable instance unsolvable

Poseidon `t=2 R_F=4 R_P=0`, nine variables — the instance M21 solved in 371 ms:

| configuration | pairs | batches | cols | peak entries | solve ms | pred/obs |
|---|---:|---:|---:|---:|---:|---|
| uncapped | 897 | 22 | 1 341 | 237 265 | 373.7 | — |
| fixed cap 64 | 872 | 28 | 1 351 | **94 621** | 358.5 | — |
| observe | 897 | 22 | 1 341 | 237 265 | 359.4 | 4/186 |
| hilbert limited+0 | 978 | **975** | 1 280 | 114 146 | 5 066.9 | 4/297 |
| hilbert limited+4 | 934 | 236 | 1 268 | 105 699 | 1 651.5 | 4/278 |
| hilbert limited+16 | 888 | 63 | 1 344 | 100 843 | 681.6 | 4/234 |
| hilbert deferred+0 | — | — | — | — | — | **column budget crossed** |
| hilbert deferred+4 | — | — | — | — | — | **column budget crossed** |

**Both deferring configurations fail on an instance the baseline finishes in 374 ms**, crossing the
60 000-column budget. That is the end of the question. A strategy whose purpose is to reduce matrix
growth instead takes a computation from feasible to infeasible, and it does so on one of the two
systems the milestone exists for.

It is still *correct* — the budget is a refusal, not a wrong answer, and that is the whole point of
F4 returning a `Result`. But it is the clearest possible verdict on the aggressive form of the idea,
and it is consistent with §3's 214x: abandoning the ascending-degree discipline on an inhomogeneous
system is not a tuning choice.

The limiting modes behave as on `t=2 R_F=2 R_P=2`: `limited+0` is **13.6x slower** on the solve for
52% less peak memory, and `limited+16` converges on the fixed cap's behaviour because the quota plus
sixteen stops binding. `pred/obs = 4/186` — a 46x underestimate, confirming `t=2 R_F=2 R_P=2`'s 27x.

## 5. Certification costs more than the computation, except where it matters

| instance | basis | solve ms | certification ms | ratio |
|---|---:|---:|---:|---:|
| Fukuoka III `n=10` | 10 | 118.6 | **0.4** | **0.003x** |
| katsura-5 | 13 | 0.7 | 1.8 | 2.6x |
| cyclic-5 | 41 | 1.7 | 3.9 | 2.3x |
| katsura-6 | 18 | 3.8 | 22.5 | 5.9x |
| Poseidon `t=2 R_F=2 R_P=2` | 70 | 142.2 | **4 824.7** | **34x** |
| Poseidon `t=2 R_F=4 R_P=0` | 102 | 373.7 | **25 140.4** | **67x** |

This answers the plan's §8.5 and it answers it in both directions.

Certification is `|G|²/2` S-polynomial normal forms and each normal form divides against all of
`G`, so the cost tracks the **basis**, not the system — and quadratically: 70 elements cost 4.8 s and
102 cost 25.1 s, a 2.1x basis for 5.2x the work. The Fukuoka instance has a unique solution, so
its grevlex basis is ten essentially linear polynomials and certification is 0.3% of the solve. The
Poseidon instance's basis has seventy elements of degree 3 over nine variables, and certification is
**34 times** the computation it is checking.

So: **the §8.5 worry is false exactly where the saving is, and true exactly where it is not.** On
Fukuoka III `n=10` the whole 3.86x survives the check intact. On Poseidon there is no saving to
erase, and certification would dominate the total whatever the strategy did.

That is a reason to keep `certify` off by default and to report its cost rather than fold it in — not
a reason to skip it. The algorithm's completeness does not rest on it; it rests on no pair being
discarded.

## 6. What this decided

| question | answer |
|---|---|
| Does a Hilbert-driven cap beat the uncapped baseline? | **Yes, 3.86x** on Fukuoka III `n=10`. |
| Does it beat a cap chosen without a model? | **No — it matches it.** 30.8 ms against 33.1 ms is inside run-to-run variation. |
| Is the prediction accurate enough to cap on? | **Only with large slack.** It underestimates by 39% on Fukuoka and 27x on Poseidon, and slack 0 is 4.4x and 6.5x slower than the best configuration on those two. |
| Does it reduce matrix size? | **Yes, substantially** — 74% fewer peak entries on Fukuoka III `n=10` at slack 0, the smallest of any configuration measured, and 51% on Poseidon. |
| Does certification erase the gain? | **Not on the instance where there is a gain** (0.3% of the solve). It is 34x the solve on Poseidon, where there is no gain to erase. |
| Is deferral worth having? | **No.** It is 1.28x *faster* than the same slack's cap on Fukuoka III `n=10`, **214x slower** on Poseidon `t=2 R_F=2 R_P=2`, and on Poseidon `t=2 R_F=4` it **crosses the column budget on an instance the baseline finishes in 374 ms**. Correct throughout — a refused budget is not a wrong answer — and measured and rejected. |
| Should it become a default? | **No.** It matches rather than beats the plain cap it has to beat, needs an instance-dependent slack, and the deferring variant is catastrophic on the structured systems. Selectable, documented, not default — the same disposition as `ReducerSelection::LargestLeadingMonomial` and the `PairSchedule` variants. |

Against M22-I's thresholds — 20% fewer peak matrix bytes, or 1.25x end to end on a nontrivial
external instance — the cap **clears the memory threshold decisively** (74% on Fukuoka III `n=10`,
51% on Poseidon) and **does not clear the time threshold against the right reference**. The honest
summary is that M22-C found a *memory* strategy, not a speed one, and that the model's contribution
over a fixed number is that it needs no tuning.

## 7. Reproducing

```sh
cargo run --release --example hilbert_driven -- list
cargo run --release --example hilbert_driven -- mq3-n10
cargo test --lib hilbert
```

The tests assert what the tables assume: every mode returns the identical basis on the correctness
corpus under every order and every criterion combination; `Observe` is bit-identical to `Off` on
every work counter; the limiting modes demonstrably do cap and defer, so the equality tests are not
passing vacuously; certification passes on every corpus system and rejects **every** single-element
truncation of a correct basis; and the one thing certification cannot catch — a reduced Gröbner basis
of a strictly *larger* ideal — is recorded as its own test rather than left to be discovered.
