#!/usr/bin/env bash
set -euo pipefail
campaign_dir=/buildcache/cargo-target/zeebra-m28-749/campaign
for adoption_phase in adoption adoption-work adoption-off; do
  python3 tools/external/selective-backward-study.py \
    --phase "$adoption_phase" --stock "$campaign_dir/stock" \
    --production "$campaign_dir/production" --binary "$campaign_dir/observed" \
    --baseline-commit 778e1dc94fbb963a9a1970dde526393ffbf5bdfe \
    --build-commit a9f86ec0 \
    --scratch "$campaign_dir/$adoption_phase" --output "$campaign_dir/$adoption_phase.json.gz"
  python3 - "$campaign_dir" <<'PY'
from pathlib import Path
import sys
size=sum(p.stat().st_size for p in Path(sys.argv[1]).rglob('*') if p.is_file())
if size>256*1024**2: raise SystemExit('declared 256-MiB output allowance crossed; stop without extending')
PY
done
