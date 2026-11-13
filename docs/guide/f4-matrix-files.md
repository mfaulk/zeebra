# F4 matrix files

Capture a pinned matrix once, then replay elimination without computing a Gröbner
basis or regenerating its polynomial system. Files are local cache artifacts; do
not commit generated matrices. This implements the offline-replay path in #646.

## Commands

List identities with `cargo run --example f4_matrix_corpus -- list` (or
`list-large` for the separately gated large set). Use the complete label:

```sh
mkdir -p /buildcache/cargo-target/zeebra-646/tmp
export CARGO_TARGET_DIR=/buildcache/cargo-target/zeebra-646
export TMPDIR="$CARGO_TARGET_DIR/tmp"
export RUSTC_WRAPPER=""
cargo build --release --example f4_matrix_files

"$CARGO_TARGET_DIR/release/examples/f4_matrix_files" dump \
  cyclic-6/grevlex/m31/default /buildcache/cyclic-6.zbf4
"$CARGO_TARGET_DIR/release/examples/f4_matrix_files" replay \
  cyclic-6/grevlex/m31/default /buildcache/cyclic-6.zbf4
"$CARGO_TARGET_DIR/release/examples/f4_matrix_files" sms \
  cyclic-6/grevlex/m31/default /buildcache/cyclic-6.zbf4 > /buildcache/cyclic-6.sms
```

`dump` captures only the named entry and checks its complete pinned fingerprint.
It refuses an existing output path and removes a partial output on a reported
error. `replay` and `sms` load only the archive: their dispatch never invokes the
lazy system generator. Both require the same field, arity, shape, reducer count
and pinned digest as the named entry. Unknown labels and malformed files fail.

Replay uses the entry's current option preset, its structured/unstructured plan,
its echelon/reduced row form, the sparse backend, and its live-entry allowance.
It prints the input digest, output digest and rank. It does not reconstruct
symbolic preprocessing or a final Gröbner basis, and makes no timing claim.
For kernel experiments, load with `read_matrix` and select the backend explicitly.

The large label is `mq-random-14/grevlex/p31x64/default-64m`. Its capture and replay
are expensive and opt-in. Run resource-bounded experiments under
`tools/benchlock.sh`, affinity pinning and an RSS guard as described in the
[benchmarking guide](benchmarking.md). Existing small-corpus walks and benchmark
smoke tests do not load or generate it.

## Native archive version 1

`grobner::f4::macaulay::io::{write_matrix, read_matrix, ReadLimits}` streams the
format with no new dependency. Use buffered file readers/writers and explicitly
flush writers so delayed I/O errors are reported. This is a matrix archive, not a
serialization of `CapturedMatrix`: the basis, critical pairs, option preset,
batch index, completion state and source commit remain external metadata. Keep
the corpus label and producing commit alongside a cache used for research.

All integers below are unsigned little-endian. A **count** occupies eight bytes,
independent of the host's pointer width; an exponent occupies four bytes. A
**string** is a count of UTF-8 bytes followed by exactly those bytes.

| Order | Encoding |
|---|---|
| Magic/version | Seven ASCII bytes `ZBF4MAT` followed by byte `0x01` (eight bytes total) |
| Arity | One count, equal to the reader's const `N` |
| Field identity | One string containing Rust's `type_name::<F>()` |
| Shape | Three counts: rows, columns, total nonzeros |
| Column labels | `N` exponents per column, in original column order |
| Each row's origin | One tag byte (`0` reducer, `1` pair component), basis-index count, pair-index count (zero for reducers), then `N` multiplier exponents |
| Each row's entries | A nonzero-count count, then a column-index count and coefficient string per entry |
| Footer | Sixteen ASCII hex bytes, the existing canonical matrix digest |
| End | EOF; trailing bytes are refused |

Indices are zero-based. Empty rows retain their origin and a zero entry count.
Coefficients use the field's canonical `Display`/`FiniteField::from_str` round
trip, including extension-field representations and wide prime residues.

The reader checks version, field identity and arity before loading matrix data.
`ReadLimits` bounds rows, columns, total nonzeros and each string before allocating
the corresponding buffers. Defaults are 100,000 rows, 100,000 columns, 32,000,000
nonzeros and 4,096 bytes per string; the CLI tightens shape/count limits to the
selected corpus fingerprint. These are allocation-count limits, not a process
RSS ceiling or an elimination fill-in budget.

The reader rejects duplicate column labels, invalid row tags, out-of-range
indices, zero/duplicate/unsorted sparse entries, invalid or noncanonical field
text, inconsistent counts, truncation, digest mismatch and trailing data. The
digest detects accidental corruption and matches the corpus's existing
64-bit-truncated SHA-256 identifier; it is not authentication. An untrusted
origin is not proof of the structured reducer-block invariant. Validate against
the intended corpus fingerprint before structured replay, as the CLI does.

Field identity deliberately distinguishes moduli and representations. Rust type
names are not a stable cross-version ABI: a type rename can invalidate an old
cache even if its mathematical field is unchanged. Regenerate such a cache;
unknown archive versions are rejected rather than guessed. No files or large
binary fixtures are committed, and the existing corpus digests are unchanged.

## SMS export

`write_sms` exports prime-field coefficient matrices in the
[SMS integer/modular format](https://membres-ljk.imag.fr/Jean-Guillaume.Dumas/simc.html):
`rows columns M`, then sorted one-based `row column value` triples, ending with
`0 0 0`. Empty rows and columns are represented by the header dimensions.

SMS does **not** contain the modulus, monomial labels, origins or Zeebra digest.
Configure the receiving tool with the original prime (2,147,483,647 in the command
above); otherwise it can interpret the same integers in the wrong field. Wide
prime residues are written in full decimal form, but the receiving tool may have
its own width limit. Extension fields are refused before writing, since their
representation integers do not have modular integer arithmetic. Use the native
archive for extension-field replay.

## Validation and CI

```sh
cargo test --lib grobner::f4::macaulay::io
cargo test --example f4_matrix_files
cargo test --test documentation
```

The example has `test = true` in `Cargo.toml`, so the existing debug/release
Nextest CI jobs run its dispatch and real-capture/replay tests. Library tests
cover field representations, sparse invariants, read limits, malformed input,
output failures and elimination agreement. The large corpus remains opt-in.
