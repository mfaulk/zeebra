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
