# External comparands: what is installed, how to invoke it, and what each one means by "degrevlex"

Provisioning and invocation record for M25 (#259, #260). This is the *operational* companion to
`docs/research/external-provenance-policy.md`, which is the authority on what may be reused:
msolve, Groebner.jl and Singular are GPL and are **run as separate processes only**
(policy §7); nothing from them enters Zeebra's MIT core. Sagebrush is `MIT OR Apache-2.0` and
is in the policy's "reuse permitted" class, and **nothing is reused from it here either** — the
driver in `tools/external/sagebrush-driver` only calls its public library.

Everything below was executed on this machine on **2026-11-06**. Provisioning is
`tools/external/provision.sh`; the environment is `tools/external/env.sh`; the smoke test is
`tools/external/smoke/smoke.sh`.

**Machine.** AMD Ryzen Threadripper PRO 5995WX, 64 cores / 128 threads, 503 GB RAM; Fedora,
`gcc (GCC) 16.2.1 20260819 (Red Hat 16.2.1-2)`, `cmake 4.3.0`, `perl 5.42.3`,
`rustc 1.99.1`. **No root**, so every dependency is built from source into
`${ZEEBRA_EXT_PREFIX:-$HOME/.local/opt/zeebra-ext}`.

---

## 1. What is installed, pinned

| component | version / commit | provenance | why |
|---|---|---|---|
| GMP | **6.3.0** (`sha256 a3c2b802…38898`) | `gmplib.org` tarball | msolve, FLINT |
| MPFR | **4.2.2** (`sha256 b67ba038…6ce01`) | `mpfr.org` tarball | FLINT, msolve |
| FLINT | **3.6.0** (`sha256 b95e2c77…4c36b`) | GitHub release tarball | msolve |
| **msolve** | **0.11.0** (`sha256 0f32011c…cdb98`) | `msolve.lip6.fr/downloads/v0.11.0/` | comparand |
| **Julia** | **1.11.7** (`sha256 aa592411…68c05`) | official generic-linux-x86_64 tarball | Groebner.jl host |
| **Groebner.jl** | **0.10.11** | Julia General registry | comparand |
| AbstractAlgebra.jl | **0.50.5** | Julia General registry | Groebner.jl's ring API |
| **Sagebrush** | **`86d9f1c787030752dcaab1ddb8d99cf1b7fa5e1b`** | `github.com/sagemathinc/sagebrush` | comparand |
| **Singular** | **4.4.1 (44105, 64 bit)**, Jun 20 2026 | pre-existing system package | comparand |

Singular is *not* provisioned by the script: it is already on `PATH` and links its own
GMP 6.3.0 / NTL 11.6.0 / FLINT 3.4.0, independent of the prefix. `provision.sh` reports it as
present and otherwise leaves it alone.

The system's FLINT and GMP **runtime** libraries exist (`/usr/lib64/libflint.so.22`,
`libgmp.so.10`, `libmpfr.so.6` — pulled in by Singular) but there are no headers and no
`.pc` files, so nothing could be built against them. That is why GMP, MPFR and FLINT are built
here rather than detected.

### 1.1 Three build obstacles on this machine, and the chosen way around each

Recorded because each one will recur for anyone reproducing this, and the third changed the
pinning decision.

**GMP's and MPFR's configure probes fail under GCC 16 by default.** GMP 6.3.0's configure ends
in `error: could not find a working compiler`, after rejecting every ABI with
`no, long long reliability test 1`. The real error is in `config.log`:
`conftest.c:12:48: error: too many arguments to function 'g'; expected 0, have 6`. GCC 16
defaults to `__STDC_VERSION__ 202311L`, and in C23 a declaration `int g();` means *no*
parameters rather than *unspecified*, so calling it with six arguments is an error rather than
the warning the probe expects. `CC="gcc -std=gnu17"` is sufficient and is what `provision.sh`
passes to GMP, MPFR and msolve (`C_STD` in that script). FLINT 3.6.0 builds clean under the
C23 default and is left alone.

**There are no autotools and they cannot be installed.** `autoconf`, `automake` and `libtool`
are all absent and there is no root. autoconf 2.72 and libtool 2.5.4 build into the prefix
without trouble, but **automake 1.17 and 1.18.1 both fail**, and not for a fixable reason:
`make` runs the freshly-built `bin/aclocal` under `help2man`, and it dies with
`Can't locate threads.pm in @INC`. Perl 5.42 removed the core `threads` module, which
`Automake/ChannelDefs.pm` uses unconditionally. (The man pages can be stubbed to get
`make install` to finish — `provision.sh` does not bother — but the *installed* `automake` then
fails at run time for the same reason, so it is useless.)

**Consequence, and the reason for the pin.** Both remaining targets were therefore taken from
distributions that ship a generated `configure`:

- FLINT from the **release tarball**, not git. A `flintlib/flint` checkout needs `bootstrap.sh`.
- msolve from **`msolve.lip6.fr/downloads/v0.11.0/msolve-0.11.0.tar.gz`**, which `INSTALL`
  calls the preconfigured distribution and explicitly distinguishes from the GitHub release
  ("note this *.tar.gz differs from the unconfigured one provided via github releases"); both a
  git checkout and the GitHub release require `./autogen.sh`, i.e. `autoreconf -fiv`.

So **msolve is pinned by release tarball and sha256, not by git commit.** Its `configure.ac:5`
declares `AC_INIT([msolve], [0.11.0], …)`, the same version git `master` declares at
`b364edcb04a1ad32bff34f5ca3ca35f299d2f477` (the SHA in the provenance policy's table, fetched
the same day), but *the tarball is the artefact that was built and measured* and the two are not
proven identical. **Source line citations below are to the 0.11.0 tarball**, whose line numbers
differ from the git tree — the prime-field check is `iofiles.c:563` in the tarball and
`:650` in git. Cite the tarball when quoting what was built.

---

## 2. The one thing most likely to silently produce an incomparable basis

All four tools were asked for a degrevlex basis with `x > y > z` and all four returned the
**same six polynomials with the same coefficients** (§7). But they say it four different ways,
and three of the four have a trap.

| tool | how degrevlex is requested | how the variable order is set | trap |
|---|---|---|---|
| msolve | **default and only order** for `-g`; `-e` makes a two-block elimination order, each block degrevlex | the order of names on line 1 of the input file, greatest first | none for `-g`; msolve may **add a variable** (§3.4) |
| Groebner.jl | `ordering = DegRevLex()` on `groebner` | the order of the name vector given to `polynomial_ring`, greatest first | `leading_monomial` reports against the **ring's** `internal_ordering`, not `ordering=` (§4.2) |
| Sagebrush | `Order::DegRevLex` argument to `f4::groebner_p` | index in the packed exponent word: variable 0 in the **highest** bit field | terms are stored in **lex** order whatever the order argument is (§5.2) |
| Singular | `dp` in the ring declaration | the order of variables in the ring declaration, greatest first | `Dp` is degree **lexicographical**; `dp` is degree **reverse** lexicographical |

Reading the first column as "they all just do degrevlex" is the error. §4.2 and §5.2 are both
cases where the *basis* is right and the *leading monomials you read off it* are wrong, which is
the failure mode that does not announce itself.

---

## 3. msolve 0.11.0

**Licence GPL-2.0-or-later; subprocess comparand only** (policy §2, §7). Binary at
`$PREFIX/bin/msolve`. Built with
`CC="gcc -std=gnu17" ./configure --prefix=$PREFIX CPPFLAGS=-I$PREFIX/include
LDFLAGS="-L$PREFIX/lib -Wl,-rpath,$PREFIX/lib"`; OpenMP is on by default
(`configure.ac:44-53`). The `-Wl,-rpath` matters: msolve runs with **no `LD_LIBRARY_PATH`**,
verified with `env -u LD_LIBRARY_PATH msolve -V`.

`./configure` warns `unrecognized options: --with-gmp, --with-flint`. That is correct and
harmless — msolve has no such flags, it finds the libraries through `AC_SEARCH_LIBS`
(`configure.ac:29-41`), which is why the paths go in `CPPFLAGS`/`LDFLAGS`.

### 3.1 Input syntax

Three parts, from `main.c:86-92`: variables comma-separated on line 1, characteristic on line 2,
then the generators one per line, comma-separated, **no trailing comma**.
`tools/external/smoke/system.ms` is the working example:

```
x,y,z
1073741827
x^2+y^2+z^2-1,
x*y+y*z+z*x-1,
x*y*z-1
```

`^` for powers, `*` for products, both required. Characteristic `0` means Q.

### 3.2 The three operations

| want | invocation | output |
|---|---|---|
| **(a) Gröbner basis only** | `msolve -f sys.ms -g 2 -o out` | full reduced degrevlex basis, one element per line, comma-separated, after a `#` header |
| (a′) leading ideal only | `msolve -f sys.ms -g 1 -o out` | the leading monomials only — the cheapest correctness check there is |
| **(b) parametrization / eliminant** | `msolve -f sys.ms -o out` (i.e. `-g 0`, the default) | over a prime field, a rational parametrization of the solution set |
| | `msolve -f sys.ms -P 1 -o out` | same, requested explicitly |
| **(c) solutions over GF(p)** | **not available** | see §3.5 |

`-g` is `main.c:104-109`: `0` nothing (default), `1` leading ideal, `2` full reduced basis,
"for first prime characteristic **w.r.t. grevlex ordering**". So `-g` answers (a) and the
default answers (b), and **the two stages can be timed separately** by running `-g 2` and then
`-g 0` — which is what #259 asked about and is the capability no other comparand here has.

Output goes to the `-o` file. `-g` output is self-documenting, which makes it the easiest
format to parse defensively:

```
#Reduced Groebner basis data
#---
#field characteristic: 1073741827
#variable order:       x, y, z
#monomial order:       graded reverse lexicographical
#length of basis:      6 elements sorted by increasing leading monomials
#---
[1*x^1*y^1+1*x^1*z^1+1*y^1*z^1+1073741826,
 … ]:
```

Every exponent is explicit (`x^1`, not `x`), coefficients are in `[0, p)`, the list is bracketed
and ends in `]:`. **An adapter should assert on those three header lines** rather than trusting
its own request; they are msolve telling you what it actually did.

### 3.3 Field support — p < 2^31

`iofiles.c:563-564` in the 0.11.0 tarball:

```c
if(tmp_mod > 2147483647){
  fprintf(ERRSTREAM, "Warning: characteristic must be 0 or < 2^31\n");
```

followed by `exit(1)`. Confirmed by running it: `p = 2147483647` (= 2^31 − 1) is accepted,
`p = 2147483659` prints that warning and exits **1**. Note the message says `< 2^31` while the
comparison is `> 2^31 - 1`; both mean p ≤ 2147483647.

**This is a capability gap and not a speed result.** Zeebra's 31-bit fields are covered;
its 64-bit and 254/255-bit fields are **not**, and neither is any BN254/BLS12-381 scalar field.
Over characteristic 0 msolve works with rationals and is unaffected. Two further narrowings
inside the prime-field range: `-S` (f4sat) is "restricted to 32 bit prime fields"
(`main.c:189-190`), and `-n` (normal form) "only works for prime field computations"
(`main.c:153`).

### 3.4 msolve may add a variable, and the eliminant degree is not what you expect

On the smoke system the default mode returns a parametrization in **four** variables,
`['x', 'y', 'z', 'A']`, with an eliminant of degree 12. `A` is msolve's own addition: `-c`
defaults to `2`, "Change order of variables, then try adding a random linear form"
(`main.c:110-119`), used when the staircase is not generic enough. The quotient ring has
dimension 12 (Singular's `vdim` and Groebner.jl's `quotient_basis` both agree, §7), so degree 12
is right *for A*; the lex basis in the original variables has `z`-eliminant of degree only **6**
(§6.2), because `z` is not in shape position. An adapter comparing "the eliminant degree"
across tools without noticing the added variable will compare two different polynomials.
`-c 0` makes msolve quit instead.

### 3.5 No enumeration of GF(p) points

Over a prime field msolve's output is the rational parametrization; the real-solution path is
for rational input ("When input coefficients are rational numbers: real solutions to the input
system", `main.c:96-97`). So operation (c) over GF(p) is **not a mode msolve has** — it has to
be derived from the parametrization by root-finding in GF(p), which is the adapter's work and
not msolve's. Record it as unsupported, with that message, per #259's acceptance criteria.

### 3.6 Threads

`-t THR`, **default 1** (`main.c:76-78`). The default being serial is the single most
important flag for a fair comparison: an unflagged msolve run is single-threaded while an
unflagged Sagebrush run uses all 128 hardware threads (§5.3). `-v 1` echoes the whole
configuration, `#threads` included, which is worth capturing into the run record.

### 3.7 `-g 2` really does stop, and `-v 1` breaks the basis down by F4 stage

Verified rather than assumed, because the whole value of msolve as a comparand rests on it.
With `-v 1`, `-g 2` prints **one** `TIMINGS` block and stops; the default `-g 0` prints several,
going on through genericity retries to the parametrization. So `-g 2` times the Gröbner stage
alone and `-g 0` times basis-plus-conversion, and the difference is the conversion.

Better than that, `-g 2 -v 1` decomposes the basis computation itself:

```
---------------- TIMINGS ----------------
overall(elapsed)  …   select  …  4.3%   symbolic prep.  …  4.6%
update  … 25.7%   convert  … 24.8%   linear algebra  …  7.9%   reduce gb  …  0.0%
---------- COMPUTATIONAL DATA -----------
size of basis  6      #terms in basis  31
```

Those are **Zeebra's own stage names** — selection, symbolic preprocessing, update, matrix
conversion, linear algebra — so `docs/MILESTONE-F4-OPTIMIZATION.md` §6.2's claim that
elimination dominates can be checked against an independent implementation stage by stage,
not just end to end. (The percentages above are from the smoke system and are meaningless at
3 ms; the point is the instrument, not the number.) No other comparand here exposes this.

### 3.8 Failure modes, and the one that is silent

`-v 0` is the default and it is **completely silent**: on the smoke system, 0 bytes of stdout,
0 bytes of stderr, exit 0. Everything in this section is therefore invisible unless `-v 1` is
passed, which an adapter should treat as mandatory rather than optional.

| condition | exit | where | message / behaviour |
|---|---|---|---|
| characteristic ≥ 2^31 | **1** | stderr | `Warning: characteristic must be 0 or < 2^31` (§3.3) |
| not in generic position, `-c 2` (default) | 0 | **stdout, only at `-v 1`** | `Ideal not in generic position, parametrizations are not correct`, then `Changing variable order for possibly more generic staircase:`, then a new variable `A` (§3.4) |
| not in generic position, `-c 0` | **1** | stderr | `=====> Computation failed <=====` plus advice to use `-c2`; **output file is empty** |
| no solution in the algebraic closure | 0 | output file | `[-1]:` (`main.c:94`) |
| infinitely many solutions | 0 | output file | `[1, nvars, -1,[]]:` (`main.c:95`) |

The third row is the clean one — non-zero exit, stderr, empty output — and the second is the
trap: **msolve recovers by changing the problem, and says so only on stdout at `-v 1` while
exiting 0.** The smoke system hits it. An adapter that runs `-v 0`, sees exit 0 and parses the
output file gets a correct parametrization *of a system with a variable msolve added*, and
nothing anywhere tells it so except the variable list in the output (`['x','y','z','A']`).
**Compare the output's variable list against the input's**; that check is cheap and it is the
only reliable signal.

---

## 4. Groebner.jl 0.10.11 on Julia 1.11.7

**Licence GPL-2.0, and self-declaredly adapted from msolve** (policy §2, §3.3, §5.4) —
subprocess comparand only, and **not an independent second opinion on msolve's design**.

Installed into a depot inside the prefix, `JULIA_DEPOT_PATH=$PREFIX/julia-depot`, so it cannot
disturb a user's `~/.julia`. `env.sh` exports it; **a `julia` invoked without it will not see
the pinned packages.** AbstractAlgebra 0.50.5 is a deliberate direct dependency: Groebner.jl
takes polynomials from a ring and does not re-export `polynomial_ring`.

### 4.1 Input syntax and the three operations

There is no input file format — the input is Julia source. `tools/external/smoke/system.jl` is
the working example.

| want | invocation |
|---|---|
| **(a) Gröbner basis** | `groebner(system; ordering = DegRevLex())` |
| **(b) lex basis** | `groebner(system; ordering = Lex())` — a **direct lex F4**, not an FGLM change of order |
| **(c) solutions over GF(p)** | **not available** |

`names(Groebner)` at 0.10.11 is exactly: `DegLex, DegRevLex, InputOrdering, Lex, MatrixOrdering,
ProductOrdering, WeightedOrdering, dimension, groebner, groebner_apply!, groebner_learn,
groebner_with_change_matrix, isgroebner, leading_ideal, normalform, quotient_basis`. **There is
no FGLM, no eliminant and no solver.** So (b) is answered by a different algorithm than
msolve's or Singular's answer to (b), which is a capability difference worth stating rather than
a timing to compare directly. `dimension` and `quotient_basis` are useful independent checks:
on the smoke system they give `0` and `12`.

### 4.2 The `leading_monomial` trap

`leading_monomial` reports against the **AbstractAlgebra ring's** `internal_ordering`, not the
`ordering=` passed to `groebner`. Measured, on the same correct lex basis:

```
ring internal_ordering=:lex,       ordering=Lex()  ->  z^6, y^2, x     # matches Singular
ring internal_ordering=:degrevlex, ordering=Lex()  ->  z^6, y*z^5, z^5 # same basis, wrong lms
```

Singular's lex basis has leading monomials `z^6, y^2, x` (§6.2), so the first line is right and
the second is an artefact of reading a lex basis through a degrevlex lens. **Build the ring with
`internal_ordering` equal to the order you are computing**, or compute leading terms yourself.
Nothing errors, and the basis itself is correct either way.

### 4.3 Threads, and why the process wall time is meaningless

`Threads.nthreads()` follows `julia -t N`; there is no `threaded` keyword on `groebner` at
0.10.11 (`:threaded in Base.kwarg_decl(first(methods(groebner)))` is `false`).

**The whole-process time is dominated by JIT compilation and must not be reported as a
timing.** Measured on the smoke system: **5.47 s wall and 698 MB peak RSS for the process**,
against **0.00018 s for the second `groebner` call**. That is a factor of ~30 000. An adapter
must either time the inner call (one warm-up call first — `system.jl` does this), or use
`groebner_learn` / `groebner_apply!`, or amortize startup across many instances. Timing
`julia script.jl` under `tools/benchlock.sh` would measure the Julia compiler.

---

## 5. Sagebrush at `86d9f1c7` — runnable, and explicitly not yet authoritative

**Licence `MIT OR Apache-2.0`** (`engine/mpoly/Cargo.toml:5`), the one permissively-licensed
comparand (policy §2). Nothing is reused from it; see §5.5.

### 5.1 There is no Gröbner CLI, so there is a driver

Sagebrush is not on crates.io, so the repository is cloned at a pinned commit. It *does* build a
binary — `engine/cli` produces `sagebrush` — but that crate depends only on
`sagebrush-bigint`, `sagebrush-modsym`, `sagebrush-ap` and `sagebrush-par`
(`engine/cli/Cargo.toml:12-15`) and **exposes no Gröbner entry point**. The engine is a library:
`engine/mpoly/src/f4.rs:671`,

```rust
pub fn groebner_p(fs: &[QPoly], o: Order, p: u64) -> Result<Vec<QPoly>, String>
```

So `tools/external/sagebrush-driver` (Zeebra's own code, MIT, committed here) reads the **same
msolve-format file** and calls it. It is a path dependency on the clone and is built with
`CARGO_TARGET_DIR=$PREFIX/cargo-target`, so it cannot share or invalidate Zeebra's own target
directory, and with `RUSTC_WRAPPER=""` so a globally configured sccache cannot serve a stale
rlib. Its own `[workspace]` table keeps it out of Sagebrush's `engine/` workspace, whose members
declare `[lints] workspace = true`. Toolchain: `engine/rust-toolchain.toml` pins `1.99.1`, which
is what `stable` already is here, so the driver builds on `stable` and no extra toolchain is
downloaded.

### 5.2 Exponent packing and the lex-storage trap

`engine/mpoly/src/order.rs:1-9` states the layout: `bits` bits per variable in one 64-bit word,
**the first variable in the highest field**, so words compare in lex order and add as monomials
multiply. `Packing::shift(i) = (n - 1 - i) * bits`. For degrevlex with n = 3 the usable width is
`64 / n = 21` bits per exponent; `groebner_p` repacks and widens on overflow and returns
`Err("exponents too large to pack")` at the ceiling.

The trap: **a polynomial's terms are kept in decreasing lex order of the packed word whatever
the monomial order is**, so for degrevlex the first term is *not* the leading term. On the smoke
system the second basis element stores as `x*z + … + z^4 + …`, whose degrevlex leading monomial
is `z^4`, not `x*z`. The driver therefore computes leading terms with the public
`Packing::key(o, w)` (`order.rs:104`) rather than taking `exps[0]`. Taking the first term
yields a plausible-looking and entirely wrong leading-monomial list — which is exactly what the
first version of the driver did, and the three-way agreement is what caught it.

### 5.3 Field support and threads

`engine/bigint/src/nmod.rs:1` — "Arithmetic modulo a word-size integer n (2 <= n < 2^64)".
Measured: the driver returns the same six leading monomials at `p = 2147483659`,
`p = 4294967291` and `p = 2305843009213693951` (2^61 − 1), i.e. **well past msolve's and
Singular's 2^31 ceiling**. Caveat on how far to trust that: `groebner_p` hands coefficients
back through `Coeffs::Small(Vec<i64>)` (`f4.rs:687-692`, `lib.rs:46-51`), so the
representation above 2^63 is not obviously sound, and **no other comparand here can corroborate
any p > 2^31**, so those runs are unverified in the §7 sense.

Threads: **`SAGEBRUSH_THREADS`**, and if unset `available_parallelism()`
(`engine/mpoly/src/lib.rs:992`, `:1005`) — **all 128 hardware threads on this machine**. The
parallel elimination path only engages at `rows.len() >= 32` (`f4.rs:317`). Any comparison
against msolve's default of 1 thread must set this explicitly; `env.sh` documents it and leaves
it unset rather than guessing.

Also worth knowing for #264/#266: the engine is switchable at run time through environment
variables — `SB_F4_FL` selects the Faugère–Lachartre elimination
(`f4.rs:325-328`), `SB_SIGF4` the signature path (`f4.rs:483`), `SB_FGLM` (`lib.rs:1661`),
`SB_F4_DEBUG`, `SB_F4_SHAPE`. That makes it the only comparand here whose *internal* algorithm
choice can be varied from outside, which is useful and also means a benchmark must pin them.

### 5.4 Maturity — do not quote its timings as authoritative yet

Stated plainly because the M25 plan requires it:

- **The repository is five weeks old.** First commit `2026-10-02`, HEAD `86d9f1c7` dated
  `2026-11-06`, 6864 commits in between. Extremely active, and young.
- **No engine release of any kind.** Every `engine/*` crate is `version = "0.1.0"`; the only
  git tags are `mcp-v*`, which are for an unrelated component. Nothing is on crates.io. The
  pin is a commit SHA because there is nothing else to pin to.
- **`engine/mpoly/src/f4.rs` carries six `#[test]`s** (`small_q`, `lex_elimination`,
  `signature_path_matches`, `verify_rejects`, and two more); `f4q.rs` and `sigf4.rs` carry
  none in-crate. There is oracle testing at the repository level — `NOTICE.md:16-19`: "PARI,
  Sage, Magma and FLINT are used only from the outside, as oracles in tests and as
  benchmarks", with `sage-tests/`, `magma-tests/` trees to match — so this is not an untested
  engine, but the in-crate coverage of the F4 path is thin.
- **What is actually established here is one system.** Exact agreement with three independent
  engines on the §7 system is real evidence, and it is one zero-dimensional system in three
  variables. It is not evidence about larger instances, other characteristics, or the `f4q`
  and `sigf4` paths.

**Conclusion: Sagebrush is runnable and its correctness is confirmed on exactly one instance.
Its timings should not be quoted as a baseline until it agrees with msolve across the
benchmark corpus.** That is a gate on the M25 results table, not a reason to leave it out.

### 5.5 Nothing is reused from it

Policy §5.3 and §10's permissive-reuse checklist are not engaged: the driver calls
`sagebrush_mpoly::f4::groebner_p` across a crate boundary and copies no code, so no
`THIRD-PARTY-NOTICES` obligation arises (policy §8.1 applies to *copied* code). The clone
lives in the prefix and is **not** committed — the only Sagebrush-derived artefact in this
repository is the pinned SHA in `provision.sh`.

---

## 6. Singular 4.4.1

**Licence GPL-2.0 *or* GPL-3.0 at the licensee's choice, no linking exception**
(policy §3.1); subprocess only, which is what `src/grobner/differential/singular.rs` already
does. Already installed; `provision.sh` only records it. Version string:
`Singular for x86_64-Linux version 4.4.1 (44105, 64 bit) Jun 20 2026`, built against
`GMP(6.3.0), NTL(11.6.0), FLINT(3.4.0)`.

### 6.1 Input syntax and the three operations

A Singular script; `tools/external/smoke/system.sing` is the working example. The ring
declaration carries characteristic, variable order and monomial order at once:

```
ring r = 1073741827,(x,y,z),dp;
```

`dp` is degree reverse lexicographical; `Dp` is degree lexicographical; `lp` is lexicographical.

| want | invocation |
|---|---|
| **(a) Gröbner basis** | `std(I)` in a `dp` ring. `std` does **not** normalize leading coefficients — follow with `simplify(G, 1)` to make it monic, or the comparison against msolve fails on scaling alone |
| **(b) lex basis / eliminant** | `fglm(r, G)` from a `dp` basis `G` into an `lp` ring — a genuine FGLM change of order, and the only comparand here that times order conversion as a separate step the way msolve's `-g` staging does |
| **(c) solutions over GF(p)** | **not available**; `solve` (`solve.lib`) is numerical and for characteristic 0 |

`vdim(G)` gives the quotient-ring dimension, 12 here. Output is stdout; `leadexp(G[i])` prints
an exponent vector (`1,1,0`), which is the one leading-monomial format that needs no parsing —
preferred over `leadmonom`, whose compact `xy` / `x2` spelling differs from every other tool's.

### 6.2 Field support, and the lex basis

`p ≤ 2147483647`, the **same 2^31 ceiling as msolve**, measured: `ring r = 2147483647,…`
constructs, `2147483659` and `4294967291` both give
`? Wrong or unknown ground field specification / ? cannot make ring`.

The FGLM lex basis has 3 elements with leading monomials `z^6, y^2, x` — a `z`-eliminant of
degree **6** against `vdim = 12`, because `z` is not in shape position. Groebner.jl's direct
lex F4 gives the same three leading monomials when the ring's `internal_ordering` is `:lex`
(§4.2). msolve's degree-12 eliminant is in its own added variable `A` (§3.4). **All three are
correct and they are not the same polynomial.**

### 6.3 Threads

Singular's `std` is serial. There is a `modstd` library for modular parallelism and a
`Singular --cpus N` flag, neither used here; for M25's purposes Singular is a **single-threaded
baseline**, which is the honest way to report it.

---

## 7. Smoke test: four tools, one system, exact agreement

The system, over **GF(1073741827)** (= 2^30 + 3, prime; inside every tool's range), degrevlex,
`x > y > z`:

```
x^2 + y^2 + z^2 - 1,   x*y + y*z + z*x - 1,   x*y*z - 1
```

`tools/external/smoke/smoke.sh` runs every available tool and compares canonical
leading-monomial exponent vectors — canonical because the four tools spell one monomial four
ways (`x^1*y^1`, `x*y`, `xy`, `1,1,0`) and a textual diff would report a purely notational
disagreement. A tool that is not installed is reported **absent**, never as agreement, which is
the same discipline as the existing oracle (`src/grobner/differential/singular.rs:8`).

**All four produce a 6-element basis with leading monomials
`xy, x^2, xz^2, y^3, z^4, y^2z^2`** (increasing in degrevlex), and the agreement is not only on
leading monomials: normalizing all six polynomials to sorted exponent→coefficient term lists,
**Groebner.jl, Sagebrush and Singular are each term-for-term identical to msolve, every
coefficient included.** The common basis is

```
x*y + x*z + y*z - 1
x^2 + y^2 + z^2 - 1
x*z^2 + y*z^2 - z + 1
y^3 + y^2*z + y*z^2 + z^3 + x - y - z - 1
z^4 + x*z + y*z - z^2 - x - y - 2*z
y^2*z^2 - y*z + y + z
```

(msolve and the Sagebrush driver print `p-1` for `-1`; Singular prints the signed
representative. Same element.)

Corroborating invariants: `vdim = 12` (Singular), `quotient_basis` length 12 and
`dimension = 0` (Groebner.jl), parametrization degree 12 (msolve).

| tool | invocation | wall (process) | inner call | peak RSS | threads | result |
|---|---|---|---|---|---|---|
| msolve 0.11.0 | `msolve -f system.ms -g 2 -o out` | **0.003 s** | — | 5.2 MB | 1 (default) | 6 elements, reference |
| Groebner.jl 0.10.11 | `julia system.jl` | 5.47 s **(JIT-dominated)** | **0.00018 s** | 698 MB | 1 | identical |
| Sagebrush `86d9f1c7` | `sagebrush-gb-driver system.ms` | 0.002 s | **0.000096 s** | 2.1 MB | all (unset) | identical |
| Singular 4.4.1 | `Singular -q system.sing` | **0.033 s** | < 0.01 s (its `timer` reads 0 cs) | 19.0 MB | 1 | identical |

**These numbers are not a benchmark and must not be quoted as one.** The system is far too
small — three of the four are at or below their own process-startup and timer granularity, and
Groebner.jl's process figure measures the Julia compiler (§4.3). Their only purpose is the
correctness gate #259 requires before any timing is quoted. Real measurement belongs under
`tools/benchlock.sh` with the M25 protocol.

Reproduce:

```bash
tools/external/provision.sh          # idempotent; ~0.2 s warm, ~10 min cold
. tools/external/env.sh
tools/external/smoke/smoke.sh        # exits non-zero on disagreement
```

---

## 8. Blockers and what is not provisioned

- **No comparand covers Zeebra's large prime fields.** msolve and Singular stop at 2^31 − 1
  (§3.3, §6.2). Groebner.jl and Sagebrush accept 64-bit primes, and for p > 2^31 **nothing
  corroborates them**, so any such run is a single unverified data point. Zeebra's 254/255-bit
  fields have **no external comparand at all** at any size. That is a capability gap to record
  in the results table, not a gap to paper over.
- **Operation (c), solutions over a finite field, is unsupported by all four.** msolve returns
  a parametrization over prime fields (§3.5); Groebner.jl has no solver; Singular's `solve` is
  numerical. Any GF(p) point enumeration is the adapter's root-finding, not a comparand's
  output.
- **msolve is pinned by tarball, not by commit**, because autotools cannot be installed here
  (§1.1). If a git-commit pin is required later, the blocker is precisely
  `Automake/ChannelDefs.pm`'s use of Perl's removed core `threads` module; the fix is a CPAN
  `threads` into a private `PERL5LIB` (this perl has `useithreads=define`, so it would build),
  and it was not worth it for an identically-versioned tree.
- **Sagebrush's timings are not yet authoritative** (§5.4): five-week-old repository, no
  release, six in-crate F4 tests, correctness confirmed on one system.
- **Not provisioned, deliberately:** Sage, Magma, Macaulay2, CoCoA, OpenF4, MathicGB, GBLA,
  M4RI. Magma is commercial; the rest are out of M25's scope as stated in #259/#260. Singular
  is not rebuilt because a working install exists.
- **CI is unchanged.** The shellcheck step in `.github/workflows/rust.yml:206` is an explicit
  file list (`scripts/agent/*.sh scripts/agent/test/*.sh`), not a glob reaching `tools/`, so
  adding these scripts to it was out of scope; and a CI job that builds GMP, MPFR and FLINT
  from source would add ~10 minutes to every run for no benefit, since no test depends on a
  comparand. `shellcheck -S warning tools/external/*.sh tools/external/smoke/*.sh` is clean and
  was run by hand.
