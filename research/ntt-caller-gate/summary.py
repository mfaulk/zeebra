"""Forward-stage fractions bound eligible work; they are not transform-only timings."""
import hashlib
import json
from pathlib import Path
import statistics


def validate_profile(row):
    if not row['verified'] or row['total_ns'] <= 0:
        raise ValueError('completed, verified root required')
    if any(row[key] < 0 for key in ('forward_ns', 'subgroup_ns', 'descent_ns')):
        raise ValueError('negative stage time')
    if sum(row[key] for key in ('forward_ns', 'subgroup_ns', 'descent_ns')) > row['total_ns']:
        raise ValueError('stages exceed complete call')
    n = row['max_n']
    if n <= row['degree'] or n & (n - 1) or row['transforms'] != 72:
        raise ValueError('unexpected order-2 KoalaBear profile')


def read_profile(raw, degree):
    profiles = [json.loads(line[5:]) for line in raw.splitlines() if line.startswith('GATE ')]
    if len(profiles) != 1:
        raise ValueError('exactly one complete caller expected')
    row = profiles[0]
    validate_profile(row)
    if row['degree'] != degree:
        raise ValueError('wrong input degree')
    return row


def ceiling(share, workers):
    if not 0 <= share <= 1 or workers < 1:
        raise ValueError('invalid Amdahl parameters')
    return 1 / (1 - share + share / workers)


def main():
    root = Path(__file__).resolve().parent
    records = json.loads((root / 'records.json').read_text())
    manifest = json.loads((root / 'manifest.json').read_text())
    patch_digest = hashlib.sha256((root / 'probe.patch').read_bytes()).hexdigest()
    if patch_digest != manifest['sources']['research/ntt-caller-gate/probe.patch']:
        raise ValueError('reporting patch no longer matches measured binary source')
    identities = {case['case']: case for case in manifest['cases']}
    incomplete = any(case['coefficients'] != case['degree'] + 1
                     for case in identities.values())
    if len(identities) != 3 or incomplete:
        raise ValueError('missing or incomplete input identity')
    groups = {}
    identity_roots = {}
    for record in records:
        for name, digest in record['sha256'].items():
            if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
                raise ValueError(f'changed artifact: {name}')
        if record['returncode'] != 0:
            raise ValueError('failed/stopped attempt; inspect raw output before interpreting')
        raw = (root / record['stdout']).read_text()
        row = read_profile(raw, record['degree'])
        if row['degree'] != identities[record['case']]['degree']:
            raise ValueError('profile does not match input identity')
        if record['kind'] == 'identity':
            identity_roots[record['case']] = row['root']
            continue
        if row['root'] != identity_roots[record['case']]:
            raise ValueError('timing answer differs from bound input answer')
        groups.setdefault(record['case'], []).append((record, row))
    if set(groups) != set(identities):
        raise ValueError('missing timing cohort')
    lines = ['| caller | call s median [min, max] | forward % median | subgroup s median | descent s median | process wall s median | CPU s median | RSS KiB max |',
             '|---|---|---|---|---|---|---|---|']
    for case, cohort in sorted(groups.items()):
        if len(cohort) != 5 or {r['repeat'] for r, _ in cohort} != set(range(1, 6)):
            raise ValueError('five fresh-process repeats required')
        if len({row['root'] for _, row in cohort}) != 1:
            raise ValueError('fixed-seed answers differ')
        times = [row['total_ns'] / 1e9 for _, row in cohort]
        share = statistics.median(row['forward_ns'] / row['total_ns'] for _, row in cohort)
        def med(key):
            return statistics.median(row[key] / 1e9 for _, row in cohort)
        lines.append(f'| {case} | {statistics.median(times):.6f} [{min(times):.6f}, {max(times):.6f}] | '
                     f'{100*share:.2f} | {med("subgroup_ns"):.6f} | {med("descent_ns"):.6f} | '
                     f'{statistics.median(r["wall_s"] for r, _ in cohort):.4f} | '
                     f'{statistics.median(r["cpu_s"] for r, _ in cohort):.4f} | '
                     f'{max(r["rss_kib"] for r, _ in cohort)} |')
    print('\n'.join(lines))


if __name__ == '__main__':
    main()
