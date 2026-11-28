# #1240 evidence: id-backed signature-basis terms, laptop stage

Findings: [`docs/research/sigf4-id-terms.md`](../../docs/research/sigf4-id-terms.md).

Measured at `ffddf05c` on a macOS/arm64 laptop. The binary is `sig_f4_study`, built with
`--features research-sigf4` in the release profile with thin LTO and 16 codegen units (sha256 prefix
`d412482ada0ad60c`). One worker, unpinned.

- `fast.jsonl.gz`: 11 alternating pairs each of dense (14, 25), Katsura-11, MQ10, MQ11, Cyclic-7
  and Eco-12.
- `slow.jsonl.gz`: 5 pairs each of dense (16, 29) and (18, 36).
- `lane.jsonl.gz`: 5 pairs each of dense (14, 25) and (16, 29) with `--lane`.

Each line has `label`, `arm` (`off` is the default, `on` is `--id-terms`), `rep`, `max_rss` (bytes,
from `/usr/bin/time -l`) and `run`, which is `sig_f4_study`'s JSON row.

Reproduce, from a build of that commit:

```bash
BIN=target/release/examples/sig_f4_study bash research/1240-sigf4-id-terms/campaign.sh fast.jsonl 11 \
  "dq14-25|--field gf31 --generate --name mq-dense-14-s1 --m 25" \
  "katsura-11|--field m31 --generate --name katsura-11" \
  "mq10|--field gf32003 --name mq-random-10" "mq11|--field goldilocks --name mq-random-11" \
  "cyclic-7|--field wide64 --name cyclic-7" "eco-12|--field wide64 --name eco-12"
BIN=... bash research/1240-sigf4-id-terms/campaign.sh slow.jsonl 5 \
  "dq16-29|--field gf31 --generate --name mq-dense-16-s1 --m 29" \
  "dq18-36|--field gf31 --generate --name mq-dense-18-s1 --m 36"
python3 research/1240-sigf4-id-terms/summarize.py fast.jsonl.gz slow.jsonl.gz lane.jsonl.gz
python3 research/1240-sigf4-id-terms/stages.py fast.jsonl.gz slow.jsonl.gz lane.jsonl.gz
```
