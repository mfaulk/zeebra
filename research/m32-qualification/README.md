# #941 M32-Q: Gate Q campaign for the adaptive graded path

Plan: [`docs/MILESTONE-ADAPTIVE-F4.md`](../../docs/MILESTONE-ADAPTIVE-F4.md) §6.2, §7.5, §8.2 (Gate Q), §8.3 (F2).
Findings: [`docs/research/m32-qualification.md`](../../docs/research/m32-qualification.md).

**Measured at:** head `f8ec0b4c` (tag `measured/941-head`; freeze F2 `f427e8d7` plus the
`GradedEngine` option), against the M31 reference entry point `c1d93389` (tag
`measured/927-base`; its `src/` is identical to `ce67df76`'s, which is not `8715c8ed`'s library: the
differences are research-feature code and one derive). The references were the groebner-rs driver `81dc5c4c` (M30-0's build) and Singular 4.4.1.
Sessions ran on 2026-11-20 under `tools/bench-reserve.sh` CCDs 1–2 (`bench-reserve run zb-941 8-23`).
Children were `taskset` from CPU 8, with `cpu-context` before and after each, `rss-guard` at 8 GiB,
and a 180 s solve cap (the `check` suite adds 600 s for certification). Lock records are in
[benchlock.log](benchlock.log) and consoles in [session.log](session.log). **Host:** Threadripper
PRO 5995WX.

## Files

| File | What |
|---|---|
| [campaign.py](campaign.py), [run.sh](run.sh) | suites `dev`, `small`, `held`, `check` on M31's child runner (`research/m31-baseline/campaign.py` `run_one`) |
| [summarize.py](summarize.py) → [tables.md](tables.md) | Gate Q tables: T3–T6 and T9 timing and memory, §9 digests and references, certification, thread high-water, wall budget, foreign load |
| [binaries.sha256](binaries.sha256) | the executables run |
| `dev.jsonl.gz` | T3, T4, T5, T6 on the development rows, n = 9 |
| `small.jsonl.gz` | rows under 50 ms by #934's method (21 calls per process, the cold one dropped), n = 31 |
| `held.jsonl.gz` | the held-out set, f4 and the option at 1/4/8/16 workers, n = 9, read once |
| `check.jsonl.gz` | one child per cell: both graded orders, the option at 1–16 workers, references, certification, 1 s wall budget |
| `diag-katsura9.jsonl.gz`, `diag-katsura9-f2.jsonl.gz` | diagnostics outside Gate Q (§2 of the findings): katsura-9 / 2⁶⁴−353 at 1 and 16 workers, n = 11 interleaved, head option vs head `f4_signature` entry vs M31 entry, then F2 entry (`f427e8d7`) vs head entry vs M31 entry. Head and F2 arms ran `--repeat 21`, M31 `--calls 20` (#958) |

## Reproduce

```sh
B=/buildcache/cargo-target/zeebra-941          # never under $HOME or /tmp
export RUSTC_WRAPPER="" CARGO_INCREMENTAL=0 TMPDIR=$B/tmp
for c in head:f8ec0b4c m31:c1d93389 f2:f427e8d7; do   # f2: diagnostics only
  mkdir -p $B/src/${c%%:*} && git archive ${c#*:} | tar -x -C $B/src/${c%%:*}
  (cd $B/src/${c%%:*} && CARGO_TARGET_DIR=$B/target-${c%%:*} \
     cargo build -j24 --release --locked --features research-sigf4 --example sig_f4_study)
  mkdir -p $B/bin/${c%%:*} && cp $B/target-${c%%:*}/release/examples/sig_f4_study $B/bin/${c%%:*}/
done
cp /path/to/groebner-rs-driver $B/bin/      # tools/external/provision-groebner-rs.sh; SHA-256 in binaries.sha256
setsid -w research/m32-qualification/run.sh OUT dev small    # then the re-check decision, posted on #941
setsid -w research/m32-qualification/run.sh OUT held check
for s in dev small held check; do gzip -n -c OUT/$s.jsonl > research/m32-qualification/$s.jsonl.gz; done
python3 research/m32-qualification/summarize.py research/m32-qualification/*.jsonl.gz \
  > research/m32-qualification/tables.md
```
