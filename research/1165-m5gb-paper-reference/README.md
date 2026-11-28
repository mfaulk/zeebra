# #1165: the authors' M5GB on ordinary prime-field ideals

**Measured at:** `8cdcc5d9` (upstream and repair records) and `381de5a4` (probe and narrow records),
both on main `dca8a943`, later squashed into the commit that adds this directory (patch files
kept out of history; the harness is otherwise unchanged), macOS 15.7.3 arm64 (M4 Pro), Apple clang 17.0.0, unpinned,
one worker, 2026-11-27. Development figures only: they do not satisfy #1030's or M35's workstation
protocol. The analysis is [`docs/research/m5gb-paper-reference.md`](../../docs/research/m5gb-paper-reference.md).

| File | What |
|---|---|
| `manifest.json` | The cohort: every row's name, family, field, order, shape, source and a SHA-256 of its generator text. Caps: 60 s wall, 4 GiB RSS |
| `runs-upstream.jsonl` | The unmodified reference (build-only patches), every row |
| `runs-repair-interreduce.jsonl` | **A different reference**: upstream plus the zero-input repair. Controls and collision rows only; never pooled with upstream |
| `runs-hash-probe.jsonl` | Upstream plus key-collision counters (no behaviour change; its timings are not the reference's) |
| `runs-hash-narrow.jsonl` | Upstream with reducer-map keys cut to 4 bits, to show those maps do not check identity |
| `collisions-darwin-arm64.jsonl` | Colliding monomial pairs under this host's `rand()` (`hash_collision.py`) |
| `summarize.py` | The note's tables: `verdicts`, `fields`, `dense`, `probe` |

The first line of each `runs-*.jsonl` is the binary's `.build` sidecar (revisions, compiler, flags,
patches). Each later line is one row: the M5GB process status, wall, peak RSS (`wait4`), the
counters parsed from its stdout, the size of its raw output, the canonicalization's checks and cost,
the references that answered, and a verdict.

Verdicts are distinct and none is a mathematical answer except `verified`: `verified` (canonical
basis equal, polynomial for polynomial, to every reference that answered, and every output element
reduces to zero modulo it), `wrong`, `unverified` (no reference, or an output over the
canonicalizer's 10^6-term cap), and the run's own failure: `signal:SIGSEGV`, `exit:<n>`,
`wall-cap`, `rss-cap`.

## Reproduce

The provisioner needs the five patch files in `$M5GB_PATCH_DIR` (default
`~/.cache/zeebra-external/m5gb-paper/patches/`). They are derived from GPL-2.0-or-later code, so
they are not in this repository. `tools/external/m5gb-paper/patches.sha256` holds their digests, and
the note's §2 describes each one in enough detail to recreate it. A missing or mismatched patch
stops the provisioner with status 3.

```bash
tools/external/provision-m5gb-paper.sh                       # and: hash-probe, hash-narrow, repair-interreduce
cargo build --release --example m5gb_paper_reference
python3 -m venv /path/venv && /path/venv/bin/pip install sympy==1.13.3   # second reference, not a repo dependency
python3 tools/external/m5gb-paper/cohort.py manifest > research/1165-m5gb-paper-reference/manifest.json
python3 tools/external/m5gb-paper/cohort.py run --variant upstream --sympy-python /path/venv/bin/python \
    > research/1165-m5gb-paper-reference/runs-upstream.jsonl
python3 tools/external/m5gb-paper/cohort.py run --variant repair-interreduce --family control,hash-collision \
    --max-modulus 4294967291 --sympy-python /path/venv/bin/python > research/1165-m5gb-paper-reference/runs-repair-interreduce.jsonl
python3 tools/external/m5gb-paper/cohort.py run --variant hash-probe --max-modulus 4294967291 --wall-cap 300 \
    --sympy-python /path/venv/bin/python > research/1165-m5gb-paper-reference/runs-hash-probe.jsonl
python3 tools/external/m5gb-paper/cohort.py run --variant hash-narrow --family authors-toy,dense-mq,control \
    --max-modulus 101 --sympy-python /path/venv/bin/python > research/1165-m5gb-paper-reference/runs-hash-narrow.jsonl
python3 tools/external/m5gb-paper/test_m5gb_paper.py           # the adapter's unit tests
```

`CARGO_TARGET_DIR` must point at the build of the example. The authors' toys are read from the
fetched tree and never copied here. Dense rows are regenerated from `corpus::dense_mq_shaped` with
seeds 116501 and 116502, which no M35 row uses (`research/1162-m35-baseline/panel.json` uses
seed = n).
