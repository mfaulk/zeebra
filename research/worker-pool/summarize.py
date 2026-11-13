#!/usr/bin/env python3
import csv
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('study', ROOT / 'tools/external/worker-pool-study.py')
study = importlib.util.module_from_spec(spec)
spec.loader.exec_module(study)


def main():
    directory = Path(__file__).resolve().parent
    provenance = json.loads((directory / 'provenance.json').read_text())
    for name in ['results.json.gz', 'instrument.patch.gz', 'interrupted-checkpoint.gz', 'interrupted-checkpoint.log']:
        if hashlib.sha256((directory / name).read_bytes()).hexdigest() != provenance[name + '_sha256']:
            raise ValueError('archive digest mismatch: ' + name)
    if hashlib.sha256(gzip.decompress((directory / 'instrument.patch.gz').read_bytes())).hexdigest() != provenance['patch_sha256']:
        raise ValueError('source patch digest mismatch')
    if hashlib.sha256(gzip.decompress((directory / 'results.json.gz').read_bytes())).hexdigest() != provenance['decoded_results_sha256']:
        raise ValueError('decoded cohort digest mismatch')
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
