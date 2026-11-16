#!/usr/bin/env python3
"""Reduce the controllers' archives to the attempt fields the tables read, plus each archive's SHA-256.

    python3 research/m29-baseline/extract.py CAMPAIGN_DIR research/m29-baseline

The wide archives hold full input and basis text (19–67 MB each) and stay off-repository; the
extract keeps each attempt's identity, status, walls and a basis digest, and names the archive by
hash so a retained copy can be checked against it.
"""
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    src, dst = Path(sys.argv[1]), Path(sys.argv[2])
    spec = importlib.util.spec_from_file_location('scaling', ROOT / 'tools/external/comparand-scaling.py')
    scaling = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scaling)
    mq10 = []
    for path in sorted(src.glob('mq10-try*.json.gz')):
        cohort = scaling.load_cohort(path)
        mq10.append(dict(
            archive=path.name, sha256=sha(path), commit=cohort['commit'],
            binaries={k: {kk: v.get(kk) for kk in ('path', 'sha256', 'version')} for k, v in cohort['binaries'].items()},
            attempts=[{k: a.get(k) for k in ('field', 'name', 'engine', 'workers', 'repeat', 'status', 'process_wall_ns')}
                      for a in cohort['attempts']]))
    (dst / 'mq10-attempts.json').write_text(json.dumps(mq10, indent=1) + '\n')
    wide = []
    for path in sorted(src.glob('wide-*-pass*.json.gz')):
        cohort = json.loads(gzip.decompress(path.read_bytes()))
        attempts = []
        for a in cohort['attempts']:
            r = a.get('report') or {}
            basis = r.get('basis')
            attempts.append(dict(
                field=a['field'], name=a['name'], engine=a['engine'], status=r.get('status', a.get('stop')),
                solver_process_wall_ns=r.get('solver_process_wall_ns'),
                basis_text_sha256=hashlib.sha256('\n'.join(sorted(basis)).encode()).hexdigest()
                if isinstance(basis, list) else None))
        wide.append(dict(archive=path.name, sha256=sha(path), commit=cohort['commit'],
                         binaries=cohort['binaries'], load_start=cohort.get('load_start'), attempts=attempts))
    (dst / 'wide-attempts.json').write_text(json.dumps(wide, indent=1) + '\n')


if __name__ == '__main__':
    main()
