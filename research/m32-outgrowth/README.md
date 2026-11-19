# #936 signature-basis usage counts

`docs/research/m32-signature-basis-growth.md` reads these files. Each is one run of
`examples/sig_f4_study.rs`, built at `3d46b15f` with
`--features research-sigf4-usage` (binary sha256 prefix `6c8c489798fbb6d6`), and run under
`tools/benchlock.sh 936-usage`:

    taskset -c 2 sig_f4_study --field <field> --name <row> --engine sigf4 --workers 1

`statistics.usage` holds the counts and the syzygy-store replays. The counts are algebraic. The
timings come from an instrumented binary and are estimates only.
