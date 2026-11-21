# #962 one-worker A/B: serial-cascade live budget

**Measured at:** head `61c874eb` (branch `fix/961-sigf4-grlex`, tag `measured/962-serial-live-budget`)
against `main` `31e334bd`, with two diagnostic variants of head built beside them. All ran on
2026-11-20/21 under `tools/bench-reserve.sh` CCDs 1–2, one worker pinned to CPU 8, inside
`benchlock` (`zb-962`), on a Threadripper PRO 5995WX with load 2–6. Executable SHA-256s are in
`binaries.sha256`.

Every arm runs `sig_f4_study --engine entry --workers 1`. The runner is m31-baseline's
`run_one` (cpu-context, rss-guard at 8 GiB, 1 s settle), and arms are interleaved and rotated
each rep. The two arms of a pair use the same harness source and the same protocol (#958):

- `dev.jsonl.gz` (`run.sh`, `run2.sh`): `research/m32-final/campaign.py --suite dev`, with
  in-tree `examples/sig_f4_study.rs` (identical in both trees). One solve per process, and the
  figure is process wall. n = 9, extended to 30 on the MQ10 and Katsura-11 rows and the
  `wide64/cyclic-7` control.
- `small.jsonl.gz` (`run2.sh`): katsura-9 under `--calls 20`, so the figure is the median warm
  call. Built from `research/m32-katsura9-gap/harness.rs` on both arms. n = 31.
- `variants.jsonl.gz` (`run3.sh`, `variants.py`): four arms in one session, all built from
  `harness.rs`. They are head, main, v2 (head with targets settled inside the loop) and v3 (head
  with main's `engine.rs`, `claim.rs` and `mod.rs`, so it carries #961's routing only). n = 21.
- `builds.jsonl.gz` (`run4.sh`, `builds.py`): both harness builds and both in-tree builds in one
  session, so one row compares two builds of the same main library. n = 21.

`summarize.py` gives paired head ÷ main ratios: the median of the per-rep ratios, with a 95%
bootstrap interval of the median.

| session | row | pair | n | ratio [95% CI] |
|---|---|---|---|---|
| dev | gf32003/mq-random-10 | head ÷ main (in-tree build) | 30 | 1.031 [1.018, 1.040] |
| dev | m31/mq-random-10 | head ÷ main (in-tree build) | 30 | 1.028 [1.010, 1.034] |
| dev | goldilocks/katsura-11 | head ÷ main | 30 | 0.996 [0.991, 1.001] |
| dev | wide64/katsura-11 | head ÷ main | 30 | 0.996 [0.993, 1.007] |
| dev | goldilocks/mq-random-11 | head ÷ main | 9 | 0.998 [0.989, 1.009] |
| dev | wide64/eco-12 | head ÷ main | 9 | 0.987 [0.971, 1.010] |
| dev | goldilocks/noon-7 | head ÷ main | 9 | 0.997 [0.987, 1.011] |
| dev | wide64/noon-8 | head ÷ main | 9 | 0.999 [0.974, 1.013] |
| dev | goldilocks/cyclic-7 (shipping route) | head ÷ main | 9 | 1.004 [0.991, 1.010] |
| dev | wide64/cyclic-7 (shipping route) | head ÷ main | 30 | 1.004 [0.996, 1.014] |
| small | wide64/katsura-9 | head ÷ main, `--calls 20` | 31 | 1.006 [1.004, 1.008] |
| variants | gf32003/mq-random-10 | head ÷ main (harness build) | 21 | 0.994 [0.985, 1.003] |
| variants | m31/mq-random-10 | head ÷ main (harness build) | 21 | 1.017 [1.010, 1.029] |
| variants | m31/mq-random-10 | v3 (main's engine) ÷ main | 21 | 1.016 [1.011, 1.025] |
| builds | gf32003/mq-random-10 | head ÷ main (in-tree build) | 21 | 1.034 [1.020, 1.043] |
| builds | gf32003/mq-random-10 | head ÷ main (harness build) | 21 | 1.018 [1.006, 1.025] |
| builds | gf32003/mq-random-10 | main (in-tree) ÷ main (harness), same library | 21 | **0.974** [0.961, 0.982] |

**Reading.** Of the dev rows, only MQ10 moves. There it moves with the build pair, not with the
engine code:

- Two builds of the same main library, differing only in example source, are 2.6% apart on
  gf32003/MQ10.
- v3 carries main's engine and is 1.016× main on m31/MQ10. That equals head's 1.017, so the
  residual there is not #962's charging.
- The harness pair reads 0.994 in one session and 1.018 in the next.

Even so, the in-tree pair reads 1.031 and 1.034 on gf32003/MQ10 in two sessions. That is above
the 1.03 bar.
