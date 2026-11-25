#!/usr/bin/env python3
"""Descriptive tables beside the Gate H read: each arm's family-weighted aggregate cost (PAR-2,
penalized), its ratio to conventional F4 at 16 workers (P3, the shipping default's widest arm),
and the §8.2 small and frontier shares as the matrix measured them. None of this decides Gate H.

    summary.py > results/summary.md
"""
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import analyse  # noqa: E402
import campaign  # noqa: E402


def main():
    m = analyse.load()
    arms = tuple(campaign.CONFIGS)
    by_arm, vbs = analyse.problem_costs(m, arms)
    fams = m.families

    def agg(values):
        return math.exp(sum(sum(math.log(values[p]) for p in ps) / len(ps) for ps in fams.values()) / len(fams))

    base = agg({p: by_arm[p]['P3'] for p in by_arm})
    print('| Arm | aggregate cost, ms (PAR-2, penalized) | ÷ P3 |')
    print('|---|---:|---:|')
    for a in arms:
        v = agg({p: by_arm[p][a] for p in by_arm})
        print(f'| {a} | {v:.1f} | {v / base:.3f} |')
    v = agg(vbs)
    print(f'| VBS⁺ (W16) | {v:.1f} | {v / base:.3f} |')
    best = {rid: min(m.cell(rid, c) for c in arms) for rid in m.records}
    small = sum(1 for p, rids in m.problems.items() if all(best[r] < 300 for r in rids))
    frontier = sum(1 for p, rids in m.problems.items() if all(best[r] >= 2 * analyse.C_MS for r in rids))
    print()
    print(f'Development base problems: {len(m.problems)}; small (best arm < 300 ms on every field): {small} '
          f'({small / len(m.problems):.1%}); frontier (no arm completes within C on any field): {frontier} '
          f'({frontier / len(m.problems):.1%}).')


if __name__ == '__main__':
    main()
