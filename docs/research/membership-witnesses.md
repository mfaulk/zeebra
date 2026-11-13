# Exact ideal-membership witness feasibility

**Measured at:** `54187fb23dd0e25851377c4575a11775db2aea7b`.

On 2026-11-13 UTC (2026-11-12 local), the public `membership_witness` example verified
`(x-y², y³-1)` as the reduced lex basis of `(x²-y, xy-1)` in three variables. The third
variable is free, so this is a positive-dimensional ideal. Its two explicit cofactor rows are
`(y, -x)` and `(-y², xy+1)`: five total cofactor terms, with ten coefficient products.
The example additionally checks the unit ideal, and forces a zero-product-budget refusal.
The guide's executable two-variable example exercises the corresponding zero-dimensional ideal.

Build and reproduction:

```bash
mkdir -p /buildcache/cargo-target/zeebra-681/tmp
CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-681 \
TMPDIR=/buildcache/cargo-target/zeebra-681/tmp RUSTC_WRAPPER='' \
    cargo build --release --example membership_witness -j12
tools/benchlock.sh issue-681-witness \
    /buildcache/cargo-target/zeebra-681/release/examples/membership_witness
```

Environment: `rustc 1.99.1 (58cf8f9c3 2026-10-13)`, Linux
`7.3.3-200.fc44.x86_64`, AMD Ryzen Threadripper PRO 5995WX, default features,
repository target ISA `x86-64-v3`, release optimization level 3, fat LTO,
`codegen-units=1`, and the workstation's `-C link-arg=-fuse-ld=mold`.
No affinity was imposed. The machine-wide benchmark lock was acquired immediately;
its START and END records report load 3.86, `status=0 end=exited`.

One locked example execution produced:

| Field | Existing certification | Added witness phase | Cofactor terms | Process peak RSS |
|---|---:|---:|---:|---:|
| GF(32003) | 20,910 ns | 2,344 ns | 5 | 2,531,328 bytes |
| BN254 Fr | 4,258 ns | 4,127 ns | 5 | 2,539,520 bytes |

These are illustrative single executions, **not stable performance estimates or a speedup
comparison**. Existing certification runs first; allocation/code warmup differs by phase and
field. The witness time excludes subsequent basis checks in the combined route. Peak RSS is
Linux's process-wide high-water mark, including inputs, parsing, prior field fixtures and
certification; it is not an incremental witness allocation measurement.

Both fields returned `ResourceLimited(TermProducts)` with a zero coefficient-product cap,
without running the combined route's legacy basis checks. Integration tests separately exercise
input-term, live-residual-term and deadline refusals and verify that the product cap is shared
across rows. Witnesses are checked exactly; malformed cofactor counts, order arity mismatch and
exponent overflow have typed errors. Limits on the witness phase do not bound existing normal
forms, S-polynomial checks or process RSS. No scalability claim or measured justification of
large default-budget workloads follows from this tiny fixture.

The narrow verifier is feasible and ships without a witness producer. Carrying full cofactor
vectors through a tracked Buchberger reference is mathematically straightforward, but its term
growth and generation cost remain unmeasured. A bounded producer or an independent execution-trace
certificate needs a separate workload-driven study. Production F4 provenance propagation is
outside this increment. No external engine code was copied or consulted for implementation.
