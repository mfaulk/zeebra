# F4 resource regression input

`anemoi17-cico-n5-fcico.system` is the exact GF(65537), ten-variable polynomial input for #659's
reduced-row regression. It is data, with no cipher implementation or solution witness. Its
producer, source hashes, measurement protocol and completed reference basis digest are documented
in [the budget study](../../../../docs/research/f4-live-budget.md) and
[the exporter protocol](../../../../research/live-entry-budget/README.md).

The ignored unit test is run explicitly in CI's release job to keep the debug suite practical:

```sh
cargo nextest run --profile ci --cargo-profile ci-release --lib --run-ignored=only \
  -E 'test(=grobner::f4::tests::test_reduced_batches_complete_the_measured_live_budget_regression)'
```
