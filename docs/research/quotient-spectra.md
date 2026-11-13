# Bounded quotient spectra

**Measured at:** `e4ea4655a02b429cda8a7e0b40088fc281c9ea54` on 2026-11-13 UTC.

Implementation and feasibility check for #686. Mathematical implementation is
independent of external source code. The public contract, budget accounting and
Berkowitz recurrence are in the
[quotient operator guide](../guide/grobner-bases.md#quotient-operator-polynomials).

Exact tests cover nonradical and nonseparating examples, characteristic two and
three, GF(32003), GF(256), BN254, zero multiplication, unit and zero ideals,
cyclic nilpotents and a field quotient. A separate permutation expansion of
`det(tI-T)` verifies every characteristic coefficient on dimension-four examples;
full-operator annihilation and minimal-divides-characteristic are also checked.
The shared first Krylov dependence establishes minimality and agrees with the
existing shape diagnostic. Typed refusal tests include exact work/workspace
boundaries, invalid variables, dimension limits and zero duration.

The initial implementation uses conservative defaults D<=128, 30 seconds,
256 MiB incremental workspace and 100 million coefficient-update work units.
The bounded eight-fixture run below supports keeping these conservative defaults.
No speedup or solver strategy change is claimed.

## Retained feasibility run

[Raw records](../../research/quotient-spectra/) retain every attempt, the complete
command transcript, compiler/CPU/lockfile/binary identities and benchmark-lock
start/end events. The only untracked files named in the manifest are the output
records being created; tracked source was clean at the declared commit.

Rust 1.99.1, LLVM 23.1.1, release/fat LTO/one codegen unit, x86-64-v3,
`-fuse-ld=mold`, Threadripper PRO 5995WX, one worker pinned to CPU 0.
One fresh process per fixture, all under the machine benchmark lock. Each had a
40-second external timeout and a hard 1 GiB address-space cap (`prlimit --as`),
which is stricter than a 1 GiB resident-memory cap. No process hit either cap.
Ambient load was 9.10 with other builds active. These are single feasibility
samples, not repeated performance comparisons or crossover evidence.

| D | Operator | Nonzeros | Construction | Minimal | Characteristic | Minimal work | Characteristic work | Workspace allowance | Materialized matrix | Reported VmHWM | time(1) max RSS |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 4 | sparse | 4 | 12.203 µs | 2.395 µs | 2.204 µs | 365 | 145 | 1696 B | 64 B | 2812 kB | 2164 kB |
| 4 | dense | 12 | 11.632 µs | 2.475 µs | 2.044 µs | 283 | 145 | 1696 B | 64 B | 2872 kB | 2148 kB |
| 16 | sparse | 16 | 37.972 µs | 7.053 µs | 99.689 µs | 17969 | 19057 | 9760 B | 1024 B | 2700 kB | 2160 kB |
| 16 | dense | 240 | 38.593 µs | 2.164 µs | 66.295 µs | 3811 | 19057 | 9760 B | 1024 B | 2820 kB | 2132 kB |
| 64 | sparse | 64 | 83.578 µs | 27.202 µs | 8.985 ms | 1073345 | 4334785 | 88096 B | 16384 B | 2724 kB | 2148 kB |
| 64 | dense | 4032 | 320.256 µs | 4.879 µs | 10.560 ms | 58243 | 4334785 | 88096 B | 16384 B | 2844 kB | 2160 kB |
| 128 | sparse | 128 | 108.705 µs | 69.131 µs | 124.507 ms | 8487297 | 68194689 | 307232 B | 65536 B | 3032 kB | 2136 kB |
| 128 | dense | 16256 | 644.410 µs | 7.414 µs | 127.892 ms | 231171 | 68194689 | 307232 B | 65536 B | 3040 kB | 2164 kB |

Both memory reporters are retained because their kernel-provided values disagree.
VmHWM is the largest in-process reading; GNU time reports `ru_maxrss` at process
exit. Neither is interpreted as incremental memory for a stage or subtracted
from another reading. The kernel caveat already documented in
`src/util/peak_memory.rs` applies. The hard address-space bound supplies the
resource guarantee independently of those reports. Stage clocks exclude the
extra diagnostic operator-nonzero scan and final formula checks; total process
wall/RSS, including those, is in each raw record.

The sparse fixture is x=y with y^D=1; both polynomials equal t^D-1. The dense
fixture is x=y+...+y^(D-1) with y^D=1. Since 32003 does not divide D, the Dth
roots are distinct: x has value D-1 at y=1 and -1 at each other root. Thus its
minimal polynomial is `(t-(D-1))(t+1)` and characteristic polynomial is
`(t-(D-1))(t+1)^(D-1)`. The runnable example asserts these complete independent
answers for every measured fixture. In particular, dense does not imply cyclic:
its minimal degree is two, explaining the small minimal-polynomial work count.

Decision: **adopt the bounded variable API**, with D<=128 as a conservative
starting default. Work grows as expected: the characteristic operation charges
68,194,689 coefficient updates at D=128, below the 100-million default.
These examples do not characterize arbitrary quotients or wide-field cost at
D=128; wide-field correctness is tested on the small exact fixtures. Larger
bounds, arbitrary residue-class overloads and faster characteristic algorithms
remain outside this change.

To reproduce after checking out the measured source commit (use a fresh output
folder rather than replacing the retained records):

```sh
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-686
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=""
mkdir -p "$TMPDIR"
cargo build -j4 --release --example quotient_spectra
tools/benchlock.sh quotient-spectra-replay timeout --signal=INT --kill-after=5s 40s \
  prlimit --as=1073741824 taskset -c 0 \
  "$CARGO_TARGET_DIR/release/examples/quotient_spectra" 128 dense
```

Repeat the final command with D=4,16,64,128 and modes sparse,dense to reproduce
all eight fixtures. The retained `command.txt` is the exact historical runner,
including the absolute checkout path; the command above is the portable replay.
