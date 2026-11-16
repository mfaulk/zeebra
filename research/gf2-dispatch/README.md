# Packed GF(2) dispatch: held-out sweep (#794)

Evidence for `docs/research/characteristic-two-linear-algebra.md` §7.3. Commits, core, lock tag
and load are in that document's header.

| File | What it is |
| --- | --- |
| `sweep.md` | `gf2_f4_dispatch sweep 5` at `810b29c3`: 299 batches, both routes' elimination stage, candidates asserted equal |
| `ab.tsv` | Raw two-binary solve times: `round`, `arm`, `instance`, `basis size`, `min ms over 3` |
| `gf2_ab.rs` | The A/B instrument, a standalone example copied into each tree's `examples/` |
| `ab.sh` | Interleaves the four binaries over 5 rounds with alternating order |
| `analyze.py`, `fit.py` | Score dispatch rules as time over the per-batch oracle |

Reproduce the rule scoring:

```bash
python3 -I research/gf2-dispatch/fit.py research/gf2-dispatch \
  docs/research/characteristic-two-linear-algebra.md research/gf2-dispatch/sweep.md
```

Reproduce the A/B: `git archive` each commit into its own directory under `/buildcache`, copy
`gf2_ab.rs` into its `examples/`, and build it with a private `CARGO_TARGET_DIR`
(`/buildcache/cargo-target/zeebra-794/ab-target-<arm>`, the paths `ab.sh` reads). Then run
`taskset -c 5 tools/benchlock.sh 794 bash research/gf2-dispatch/ab.sh <out.tsv>`.
