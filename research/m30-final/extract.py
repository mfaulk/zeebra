#!/usr/bin/env python3
"""#862: #834's `research/m29-baseline/extract.py`, plus each attempt's peak RSS.

    python3 research/m30-final/extract.py CAMPAIGN_DIR research/m30-final

Same fields and archive hashes as #834's extract, so `verdicts.py` reads the output unchanged. The
additions are `peak_rss_bytes`: the controller's observed process-tree peak (`wide-corpus.py`
`observed_tree_peak_bytes`, `comparand-scaling.py` `peak_rss_bytes` or its `/usr/bin/time` maximum).
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


def rss(attempt):
    for key in ('peak_rss_bytes', 'observed_tree_peak_bytes', 'max_rss_bytes'):
        if isinstance(attempt.get(key), int):
            return attempt[key]
    guarded = attempt.get('attempt') or attempt.get('guarded') or {}
    for key in ('peak_rss_bytes', 'observed_tree_peak_bytes', 'max_rss_bytes'):
        if isinstance(guarded.get(key), int):
            return guarded[key]
    return None


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
            attempts=[dict({k: a.get(k) for k in ('field', 'name', 'engine', 'workers', 'repeat', 'status',
                                                  'process_wall_ns')}, peak_rss_bytes=rss(a))
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
                solver_process_wall_ns=r.get('solver_process_wall_ns'), peak_rss_bytes=rss(a),
                basis_text_sha256=hashlib.sha256('\n'.join(sorted(basis)).encode()).hexdigest()
                if isinstance(basis, list) else None))
        wide.append(dict(archive=path.name, sha256=sha(path), commit=cohort['commit'],
                         binaries=cohort['binaries'], load_start=cohort.get('load_start'), attempts=attempts))
    (dst / 'wide-attempts.json').write_text(json.dumps(wide, indent=1) + '\n')


if __name__ == '__main__':
    main()
