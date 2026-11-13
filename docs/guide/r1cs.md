# Checked R1CS import

`zeebra::r1cs` imports a narrow R1CS v1 profile over a caller-selected prime field.
It preserves original sparse rows, row IDs, wire-to-label mapping, public-interface roles,
declared private-input counts and optional Circom symbols before producing any polynomials. The
[design gate and evidence](../research/bounded-r1cs.md) record the public fixture round-trip,
independent reader and producer identities, exhaustive small-field checks, and bounded pilot.

## Import, expand, check

```rust
use zeebra::{
    fields::Bn254Fr,
    r1cs::{ImportLimits, R1cs, WireRole},
    FiniteField, One, Zero,
};

let bytes = include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/r1cs/multiplier.r1cs"));
let rows = R1cs::<Bn254Fr>::parse(bytes, &ImportLimits::default()).unwrap();
assert_eq!(rows.wire_role(1), Some(WireRole::PublicOutput));
let system = rows.expand::<3>().unwrap();
assert_eq!(system.variable_to_wire, vec![1, 2, 3]);

// The producer's original witness order is [one, product, a, b].
let wires = [Bn254Fr::one(), Bn254Fr::new(15), Bn254Fr::new(3), Bn254Fr::new(5)];
let original = rows.evaluate_assignment(&wires).unwrap();
let expanded: Vec<_> = system.polynomials.iter().map(|p| p.eval(&wires[1..])).collect();
assert_eq!(original, expanded);
assert!(original.iter().all(Zero::is_zero));
```

`evaluate_assignment` computes `(A·w)(B·w) − C·w` directly from the original sparse rows;
it does not invoke the converter or evaluate a polynomial. It returns one residual per
original row, so a nonzero value identifies a failed row. Assignment length must equal the
original wire count, and assignment wire zero must be one.

The expansion substitutes constant one for wire zero and maps original wire `i > 0` to
polynomial variable `i − 1`. `expand::<N>()` refuses if `N < wire_count − 1`; it does not
change Zeebra's const-generic arity. Choose exact capacity for dimension-sensitive solving:
extra coordinates are unconstrained padding, not additional witness wires. Capacity also
cannot exceed `max_wires − 1`, which bounds each monomial's storage.

Every original row receives a polynomial and retains its row ID, including tautologies that
expand to zero and impossible constant-only rows. `ExpansionStats` reports source sparse terms,
raw A-by-B products before cancellation, retained polynomial terms, and the largest row.
No solver is invoked by import, expansion, or assignment checking.

## Accepted profile and refusals

The parser requires magic `r1cs`, version one, and exactly one each of sections 1 (header),
2 (constraints), and 3 (wire-to-label map), in any order. Custom-gate and unknown sections
return `UnsupportedSection`. This deliberately narrower profile also refuses extension
sections that the broader format permits readers to ignore.

The requested field must have equal order and characteristic and a canonical modulus width
of 8, 16, 24, or 32 bytes. The modulus must match exactly; field reduction never repairs a
wrong modulus. Sparse factors must have strictly increasing, in-range wire IDs and nonzero
coefficients strictly below the modulus. Nonminimal field widths, duplicate sections, invalid
counts, duplicate/out-of-range labels, trailing bytes, and truncation fail explicitly.
The API returns no partial model or partial expansion on failure.

`wire_role` identifies the constant and public output/input prefix. `Header.private_inputs`
is the producer's declared count, which can include optimized-out signals. It does not identify
retained private-input wires: pinned Circom 2.2.3 `--O2` keeps that original count while deleting
inputs and renumbering later internal witnesses. Nonpublic wires therefore have
`UnclassifiedWitness` role when the declared private count is nonzero, and `Internal` role
when it is zero. Private declarations need not fit the retained nonpublic wire count. No role
is inferred from label numbers or symbol names; exact private-wire identity needs additional
producer metadata. Wire zero's canonical label must be zero. Labels do not permute variables.

Attach optional UTF-8 Circom `.sym` records with `with_symbols(text)`. Labels and qualified
names must be unique, and any label selected by the binary wire map must name that same wire.
Other labels may alias a wire or retain `-1` as an optimized-out signal without acquiring a
polynomial variable. Component IDs and names are retained. Symbol order is normalized by label.

`source_digest` hashes the exact input bytes. `canonical_digest` hashes the checked binary with
section order normalized to 1, 2, 3; original rows and maps remain ordered. Symbols are excluded
from that binary identity. `symbol_digest` separately binds a nonempty canonical symbol
sidecar to the model's canonical digest. `to_bytes` emits that canonical R1CS representation.

## Limits and runnable example

Default `ImportLimits` are 16 MiB per binary or symbol sidecar, 100 wires including constant
wire zero, 1,000 rows, 10,000 symbol records, 100,000 A-by-B products, 100,000 retained expanded
terms, and a 60-second cooperative deadline per parsing, symbol or expansion operation.
The API accepts an existing byte slice, so callers must also bound input allocation before
parsing; the example uses a limited read. Callers can supply smaller or explicitly larger
limits. Deadlines do not interrupt an
individual field operation, and structural counts are not process-memory bounds.
Use an external supervisor for a hard end-to-end wall or process-memory ceiling; the retained
pilot used 60 seconds and a stricter 512 MiB virtual-address-space ceiling per child.

The example compiles fields `7` and `bn254` and capacities `0,1,2,3,4,6,8,16,32,64,99`:

```sh
cargo run --release --no-default-features --example r1cs_import -- \
  tests/fixtures/r1cs/multiplier.r1cs --field bn254 --capacity 3 \
  --symbols tests/fixtures/r1cs/multiplier.sym --assignment 1,15,3,5
```

The JSON separates parse, expansion/model, original-row checking, polynomial checking, and
process-high-water observations. An unsupported capacity or malformed file produces a structured
refusal and a nonzero exit status. `--max-products N` demonstrates the expansion budget.
`solve_ns` and `recovery_ns` are null because those operations are outside this adapter.
Only the active assignment wires are copied into a padded polynomial point.

The Rust integration suite is offline; Circom, Node and the independent reader are required
only to regenerate the pinned fixture and research evidence. See the
[reproduction commands](../../research/r1cs-725/README.md).
