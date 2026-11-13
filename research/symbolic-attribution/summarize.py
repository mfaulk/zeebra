"""Refuse incomplete campaigns or a baseline that no longer recovers #737 counts."""
import csv
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ARMS = ('baseline', 'dedup', 'active', 'active-dedup', 'newest', 'sparse', 'input-order', 'input-order-dedup', 'input-order-active-dedup')


def records(path):
    with path.open() as stream:
        return list(csv.DictReader((line for line in stream if not line.startswith('#')), delimiter='\t'))


def main():
    metadata = json.loads(Path(__file__).with_name('metadata.json').read_text())
    for campaign in metadata['campaigns']:
        record = Path(__file__).with_name(campaign['file'])
        assert hashlib.sha256(record.read_bytes()).hexdigest() == campaign['record_sha256'], record
    rows = records(Path(__file__).with_name('replay.tsv'))
    assert len(rows) == 10 * len(ARMS), 'incomplete campaign'
    indexed = {(int(row['round']), row['arm']): row for row in rows}
    assert len(indexed) == 10 * len(ARMS), 'duplicate cells'
    old = records(ROOT / 'research/msolve-gap/zeebra-batches-32003.tsv')
    assert len(old) == 10
    for round_number, reference in enumerate(old, 1):
        base = indexed[round_number, 'baseline']
        for field, original in [('pairs', 'pairs'), ('basis', 'basis_before'), ('rows', 'rows'), ('cols', 'cols'), ('nnz', 'nnz')]:
            assert base[field] == reference[original], (round_number, field)
        for arm in ARMS:
            row = indexed[round_number, arm]
            assert row['pairs'] == base['pairs'] and row['basis'] == base['basis']
            assert all(int(value) >= 0 for key, value in row.items() if key != 'arm')
        unique = indexed[round_number, 'dedup']
        assert unique['cols'] == base['cols']
        assert int(base['rows']) - int(unique['rows']) == int(base['seeds']) - int(unique['seeds'])
    print('arm\trows\tcols\tnnz\tforward_apps\tforward_products')
    for arm in ARMS:
        values = [sum(int(indexed[r, arm][field]) for r in range(1, 11))
                  for field in ('rows', 'cols', 'nnz', 'forward_apps', 'forward_products')]
        print(arm, *values, sep='\t')
    sorted_path = Path(__file__).with_name('sorted.tsv')
    assert sorted_path.read_text().startswith('# sorted_input true; sorted mode asserts exact reduced-basis equality\n')
    sorted_rows = records(sorted_path)
    assert len(sorted_rows) == 20
    sorted_index = {(int(row['round']), row['arm']): row for row in sorted_rows}
    assert set(sorted_index) == {(r, a) for r in range(1, 11) for a in ('baseline', 'dedup')}
    for round_number in range(1, 11):
        base = sorted_index[round_number, 'baseline']
        unique = sorted_index[round_number, 'dedup']
        assert base['pairs'] == indexed[round_number, 'baseline']['pairs']
        assert base['cols'] == unique['cols']
        assert int(base['rows']) - int(unique['rows']) == int(base['seeds']) - int(unique['seeds'])
    for arm in ('baseline', 'dedup'):
        print('sorted-' + arm, *(sum(int(row[field]) for row in sorted_rows if row['arm'] == arm)
              for field in ('rows', 'cols', 'nnz', 'forward_apps', 'forward_products')), sep='\t')
    # The passive replay must recover the independently recorded #737 forward counts.
    assert sum(int(indexed[r, 'baseline']['forward_products']) for r in range(1, 11)) == 585166982
    assert sum(int(indexed[r, 'baseline']['forward_apps']) for r in range(1, 11)) == 7885325


if __name__ == '__main__':
    main()
