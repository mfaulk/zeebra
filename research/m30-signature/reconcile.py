"""#223's pair-row fraction beside C1's per-pair and per-product fractions, from the same runs.

    python3 research/m30-signature/reconcile.py research/m30-signature/census.jsonl.gz
"""
import gzip
import json
import sys


def row(r):
    s, w = r['statistics'], r['work']
    fp, bp = w['forward']['coefficient_products'], w['backward']['coefficient_products']
    zp = sum(b['zero_row_products'] for b in w['batches'])
    dep, rank = s['dependent_candidate_rows'], s['candidate_rank_contribution']
    pairs, added = s['pairs_reduced'], s['elements_added']
    return dict(target=r['target'], status=r['status'], basis_sha256=r['basis_sha256'],
                pairs_reduced=pairs, elements_added=added, zero_reductions=pairs - added,
                zero_reduction_fraction=(pairs - added) / pairs,
                pair_rows=dep + rank, pair_rows_adding_no_rank=dep, dependent_row_fraction=dep / (dep + rank),
                pair_rows_per_pair=(dep + rank) / pairs, zero_rows=s['zero_rows'],
                products=fp + bp, zero_row_products=zp, zero_row_product_fraction=zp / (fp + bp))


def main():
    with gzip.open(sys.argv[1], 'rt') as f:
        rows = [row(json.loads(line)) for line in f if line.strip()]
    for r in rows:
        print(json.dumps(r))


if __name__ == '__main__':
    main()
