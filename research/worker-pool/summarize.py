#!/usr/bin/env python3
import csv
import gzip
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('study', ROOT / 'tools/external/worker-pool-study.py')
study = importlib.util.module_from_spec(spec)
spec.loader.exec_module(study)


def main():
    directory = Path(__file__).resolve().parent
    with gzip.open(directory / 'results.json.gz', 'rt') as stream:
        record = json.load(stream)
    summary = study.summarize(record)
    (directory / 'summary.json').write_text(json.dumps({'source': record['source'], 'binary_sha256': record['binary_sha256'], 'rows': summary}, indent=2) + '\n')
    with (directory / 'summary.csv').open('w') as stream:
        writer = csv.DictWriter(stream, fieldnames=['phase', 'backend', 'workers', 'case', 'median_ns', 'range_ns', 'speedup', 'efficiency', 'rss_bytes'])
        writer.writeheader()
        for row in summary:
            writer.writerow({k: row[k] for k in writer.fieldnames})
    print(f'validated {len(record["attempts"])} attempts; wrote {len(summary)} cells')


if __name__ == '__main__':
    main()
