# Adaptive parallel F4 forward elimination (#752)

**Status:** gates declared before measurement; results pending.

## Route

`F4Options::parallel_forward` dispatches a batch's reducer-block forward pass to
`linalg::concurrent` (#728's safe concurrent pivot discovery: immutable `OnceLock`
publication, private dense scratch, scoped joins). Candidate-only backward reduction (#749)
then finishes the candidates exactly as after the serial pass. The echelon rows differ from the
serial ones; pivot columns and fully reduced candidates do not, so the basis is identical.

`Send + Sync` is proved by each concrete field through `FiniteField::concurrent_elimination`,
not added to `FiniteField` or to any F4 signature. Extension fields return `None` and stay serial.
A dispatch whose reservation (published rows plus two full-width rows per worker) would cross
the live-entry budget, or whose workspace exceeds 64 MiB, falls back to the serial kernel on the
untouched matrix, so no computation serial admits is refused. A worker panic propagates; nothing
partial is returned.

## Predeclared gates

Declared at commit `8ccea616`, before any complete-task campaign:

1. **Named large-task gain:** at least 10% complete F4-call improvement over the shipping
   serial route on MQ10 at both small primes, non-overlapping five-run ranges.
2. **Small controls:** cyclic-5/6 and katsura-6/7 at both primes under the selected `Auto`
   setting regress no more than 5% in F4-call median against serial.
3. **Memory:** process peak RSS no more than 1.25x serial on every task.
4. **Held-out validation:** the gate is fitted on per-batch replays of mq-random-10/32003,
   katsura-9/32003 and cyclic-7/32003 only; katsura-8, cyclic-8, mq-planted-10 at
   2147483647, mq-planted-wide-10 at 2^64-353 and katsura-10/32003 are scored but not used
   to choose constants, and must not regress beyond gate 2's 5%.
5. **Exactness:** every attempt's basis digest equals the serial arm's for the same task.

If gates 1–5 pass, `Auto { max_workers: 0 }` becomes the default in `F4Options::recommended`;
otherwise the default stays `Serial` and the route remains opt-in, with the failing gate named.

### Design 1 verdict (`Auto { max_workers: 0 }`, binary from `46867c14`): rejected

Measured 2026-11-16 01:00 under one bench-lock window; gate 1 and gate 5 pass, **gates 2
and 3 fail**:

- Gate 2: cyclic-5 0.69 → 1.82 ms, katsura-6 0.94 → 1.47 ms, cyclic-6 4.20 → 5.66 ms,
  katsura-7 4.42 → 5.11 ms, with **zero batches dispatched**. The cost is per batch, not
  threading: the route called `std::thread::available_parallelism` (which reads cgroup files)
  and permuted the matrix reducers-first on every batch before the gate said serial.
- Gate 3: MQ10 peak RSS 37.28 → 48.96 MiB (1.31x) and 38.28 → 51.80 MiB (1.35x) at up to 62
  workers per batch.

### Design 2, declared at the commit that introduces it, before measurement

Changes: the gate reads lower rows and entries off the row kinds without permuting, returns
before asking for parallelism when a batch is below `MIN_LOWER_NONZEROS`, and caches the
parallelism once per process. The candidate default is `Auto { max_workers: 16 }`, because
`Forced { workers: 16 }` held MQ10 RSS to 1.19x/1.21x in design 1's scaling run.

Gates 1–5 apply unchanged to `Auto { max_workers: 16 }` in a fresh campaign. If they pass it
becomes the default; if they fail, the default stays `Serial`, the route ships opt-in and the
investigation stops at two designs as #752 requires.
