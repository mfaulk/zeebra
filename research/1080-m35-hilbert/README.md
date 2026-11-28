# #1080: M35 WP B, exact certified zero skipping

**Measured at:** `35aa01ab` (tag `measured/1080-harness`). Its `src/` is identical to Z0 `125658bb` (tag `measured/1162-z0`). It adds only harness changes to `m34_matrix`: `--hilbert` and the Goldilocks and 2⁶⁴ − 353 instantiations.

**Plan:** [`MILESTONE-FINITE-FIELD-COMPETITIVENESS.md`](../../docs/MILESTONE-FINITE-FIELD-COMPETITIVENESS.md) §7.2 and §9.2, Amendment 1. The predeclaration is on #1080.

B uses the existing `HilbertSelection::CertifiedZeros { slack }` and changes no engine code.

## Development slack sweep (dev mode; decides nothing)

`sweep.py` has three subcommands:
- `sweep.py catalog --qualify BIN --study BIN --out DIR` writes the development records. `mq-full-N-s0` is the frozen wide-corpus `mq-random-N`.
- `sweep.py manifest --binary BIN --commit SHA --inputs DIR` writes the job. It runs shipping F4 with `--hilbert off` and with `certified-zeros+{0,2,8,32}`, 3 repetitions, on the development regime rows and #1080's four adverse controls.
- `sweep.py extract --job-dir DIR` emits one line per attempt with the Hilbert counters.

Controls measured with the mechanism forced on are diagnostic only (plan §9.1). Held-out rows are generated only after the rule is frozen.

Results: pending (bench-job `f9874321f431`).
