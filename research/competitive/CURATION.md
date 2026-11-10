# Curation of the competitive history

`results/history.json` is append-only by contract, and that contract was broken once, on purpose.

When the cryptanalysis research moved out of this crate (#668), the 70 rows whose problems were
cipher systems were removed: 42 `poseidon-t2-*-planted` rows and 28 `anemoi64-cico-n*-fcico` rows.
Those rungs left the public corpus (`grobner::external::corpus::ladder`) at the same time, so the
board could no longer state their ideal equivalence across engines. That equivalence is the gate on
publishing a ratio.

The 450 rows remaining after that curation are unchanged, field for field, and in their original
order. No row was added, re-measured or edited. `COMPETITIVE.md` was regenerated from them with
`cargo run --release --example competitive -- --write`.

The complete 520-row history, including the removed rows, is `research/competitive/results/history.json`
at commit `9532a9a2a33fb4943120afdd2ccc2a99bda7eb65`:

```sh
git show 9532a9a2:research/competitive/results/history.json
```

Every row in that file, the removed ones included, still names the commit it was measured at.

PR #665 subsequently appended 100 upper-rung sweep attempts, measured at `19ff732c`,
bringing the retained history to 550 rows without restoring the 70 removed cipher rows.
