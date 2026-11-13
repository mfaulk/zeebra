# Concurrent F4 pivot discovery (#728)

Source audit: Zeebra `e22b9b58`; the measurement instrument is committed separately
before running. [Protocol and reproduction](../../research/concurrent-pivots/README.md).
The post-prefix #713 census is reused, not relabelled as a new timing result.

## Reference mechanisms

| Reference and immutable revision | Publication and scheduling | Implication for Zeebra |
|---|---|---|
| [msolve `la_ff_common.c`](https://github.com/algebraic-solving/msolve/blob/c5a41f0a842c126d669676c041bd3fc4675cf7e7/src/neogb/la_ff_common.c), `c5a41f0a842c126d669676c041bd3fc4675cf7e7`, exact sparse routines | OpenMP dynamic row/group scheduling, worker-private `int64_t` dense storage, CAS installing a completed sparse pivot; losers resume reduction. The shared file invokes width-specific reduction/normalization callbacks. | Separate the scheduling/publication idea from grouped arithmetic and field width. Audit the final-reduction path's thread selection; do not extrapolate every OpenMP loop to every task. |
| [Groebner.jl threaded backend](https://github.com/sumiya11/Groebner.jl/blob/509ed7c38338608c25c9c86713ed7a57bb78f5ba/src/f4/linalg/backend_threaded.jl), `509ed7c38338608c25c9c86713ed7a57bb78f5ba` | Reservation changes sentinel 0 to 1; normalization, coefficient storage and support initialization precede release-publishing sentinel 2. Consumers acquire ready pivots. Rows are assigned to round-robin task chunks. | Reservation is not readiness. Its deterministic threaded path is independent of randomized row skipping. [Dispatch](https://github.com/sumiya11/Groebner.jl/blob/509ed7c38338608c25c9c86713ed7a57bb78f5ba/src/f4/linalg/linalg.jl) uses lower-row/task and column gates; these are upstream policy, not Zeebra crossover evidence. |
| [Monagan–Pearce, PASCO 2015, §2.2](https://www.cecm.sfu.ca/CAG/papers/RomanPasco2015.pdf) | Private dense work rows and atomic sparse-pivot installation; a failed claim requires further reduction. | Redundant work is possible; historical speedups do not predict present workloads or efficiency. |
| [Rust comparand](https://github.com/sdiehl/groebner/blob/c3e1d630fba9b2155a4c389d9022f13e0ba09218/src/f4/eliminate.rs), `c3e1d630fba9b2155a4c389d9022f13e0ba09218` | A column-indexed `OnceLock` table stores owned completed pivots, separate from borrowed known rows. Failed installation returns ownership to the losing row for reduction. | A safe standard-library publication mechanism avoids custom raw-pointer reclamation. Its [scheduler](https://github.com/sdiehl/groebner/blob/c3e1d630fba9b2155a4c389d9022f13e0ba09218/src/par.rs) and coefficient layout are separate choices. |

The GPL sources are algorithm references only. The initial instrument modifies
Zeebra's own serial observer and uses no imported elimination implementation.
No comparand source is vendored into the MIT library.

## Correctness and resource requirements for a possible prototype

Known reducer rows remain read-only. A private candidate accumulator starts as an
input row and changes only by subtracting multiples of published pivots and by
nonzero normalization. Hence every live residual remains in the input row span.
Publish a fully initialized monic sparse row only in the slot of its leading
column. A single-assignment slot gives distinct leading columns. On losing a
claim, keep the owned losing row, load it again, and eliminate with the winner:
its lead strictly advances or the row becomes zero. There are finitely many
columns, so each row terminates without waiting for an unpublished future pivot.

Every consumed input is represented by a published residual plus the pivots used
to reduce it, or reduces to zero. Both span inclusions follow; matching ranks alone
would not establish them. Winners can have unreduced tails. Freeze all winners
until every worker joins, then run the existing backward pass separately. Do not
mutate a pivot while a reader can still borrow it. This preserves the linalg RREF
contract and the F4 candidate-selection contract without making inherited reducers
an identity first. The rejected #50 decomposition remains rejected.

Prefer `OnceLock<SparseRow<F>>` with ordinary Rust borrows over an empty/reserved/
ready raw pointer protocol. Fully initialize and normalize before `set`; `get`
returns only initialized storage. A failed `set` returns ownership. Scoped joins
end every reader before extraction/destruction, so no ABA or reclamation protocol
is needed. Cancellation and worker panics must join everyone and discard the whole
partial result. Failure must leave no successful partial basis or lingering claim
state, and subsequent calls must work normally. `Send + Sync` belongs only on the
experimental entry, never on the public `FiniteField` trait.

Concurrent resource checks must precede growth. One simple conservative ledger
retains all original input entries, charges every published pivot, and reserves
up to two full row widths per active candidate (dense mathematical support plus
temporary sparse materialization). Replace the reservation with the winner's
actual entries only after publication. Count all simultaneous losers/reservations;
do not reuse the serial peak as a concurrent bound. A separate workspace-byte
limit covers worker dense capacities and publication/index arrays; process RSS
and input/output capacities remain separately reported. Checked arithmetic must
refuse overflow. This ledger may reject a serially affordable matrix; report that
restriction rather than silently raising the shipped budget.

The source design is independent of #269's output-necessity experiment and #592's
pool. Any timed prototype needs a measured dispatch floor, dynamic versus static
controls, explicit worker-local product/retry aggregation, and the full correctness
and adversarial scheduling tests described in #728. Serial thread-local counters
in a parent scope cannot observe worker work. No custom atomics or unsafe code are
necessary for publication; synchronization-library guarantees do not replace forced
race, panic, cancellation, reservation-refusal and reuse tests.
