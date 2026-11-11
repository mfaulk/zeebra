# F4 live-entry budget study (#659, #490)

`examples/f4_live_budget.rs` measures one F4 computation per process. Arguments are a built-in
case (`mq-random-10`, `katsura-11`, `cyclic-9`) or an input path, an entry allowance (`default` or
an integer), and a row form (`reduced` or `echelon`). Input files list comma-separated variable
names, the prime, then comma-separated polynomials. Only the field/arity pairs matched in the
example are compiled. This is an opt-in diagnostic, not a general system-file API.

Use a private target directory and `TMPDIR` under `/buildcache`, `RUSTC_WRAPPER=''`, and the release
profile with repository ISA flags. Build before acquiring `tools/benchlock.sh`. Set
`ZEEBRA_MACHINE`, `ZEEBRA_AFFINITY`, and `ZEEBRA_WALL_SECONDS`; use an external watchdog and memory
ceiling. One fresh process per row makes RSS attributable. JSON records distinguish stopped runs'
completed-batch peaks from their error's construction demand or elimination crossing; a stopped
run does not establish a full-run peak. Basis digests sort the displayed reduced polynomials.

```sh
CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-659 RUSTC_WRAPPER='' \
  cargo build --release --no-default-features --example f4_live_budget
ZEEBRA_MACHINE=fedora ZEEBRA_AFFINITY=2 ZEEBRA_WALL_SECONDS=120 \
  tools/benchlock.sh live-budget timeout --signal=INT --kill-after=10s 150 \
  taskset -c 2 /buildcache/cargo-target/zeebra-659/release/examples/f4_live_budget \
  mq-random-10 20000000 reduced
```

## Input provenance

The separate `mfaulk/cryptanalysis` checkout at
`7839a7a3f222a1668a8bcb7df0cc344b86cd2b8c` supplies the previously reported workload generators.
`export_inputs.rs` is a standalone exporter template; it does not reintroduce cipher modules into
the library. Put it at `src/main.rs` in a scratch Cargo package, symlink `src/cryptanalysis` to
that checkout, and depend on this Zeebra checkout and `rand = "0.8.5"`. Use `[workspace]` for an
isolated package. Run with the output directory as its sole argument. The exporter uses the exact
registered fields, models and parameters, including the full 80-variable Poseidon system without
slicing or affine elimination. No solution or cryptanalytic frontier is claimed by an F4 run.

Generator source SHA-256:

- `src/primitives/anemoi.rs`: `3a8adae9c199c99f21427b82bed0576035ef0bf5f67bcc59a84059a406100e41`
- `src/attacks/anemoi_cico.rs`: `5a46d9ccca2b728bef56ed2ab422481e500e8615005d462a5d94d6928257265b`
- `src/primitives/poseidon.rs`: `f89e7e32fa3a75d6e4d91f133a648a66bd1324a2f9bb8cf449bb15c94e39ac78`

The public MQ control uses `GeneratedSystem::generate`, seed 10, ten variables, degree at most two
and at most forty terms per equation, matching `external::corpus::random_mq_instance(10, 10, …)`.
Katsura-11 uses eleven variables, matching the corpus's naming convention. All public controls use the corpus reference prime 2147483647
in its 64-bit representation; the private-generator controls likewise preserve their original
64-bit field representation. Every record pins its exact input text by SHA-256.

An initial Katsura pilot used twelve variables under an eleven-variable label. It was excluded;
published Katsura comparisons use the corpus's eleven-variable input. The example's automated
control-arity test guards that boundary, and its MQ test checks the generators against the actual
competitive corpus.
