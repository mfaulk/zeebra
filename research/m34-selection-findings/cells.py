#!/usr/bin/env python3
"""Development records where the engine or worker choice changes cost by at least 1.5x (#1015).

A descriptive re-read of the retained #1012 records through `analyse.py`'s own cell rule (median of
clean repetitions, J3 verification, PAR-2), so a penalized cell is the same cell Gate H penalized.
It adds no feature cost and decides nothing.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'm34-gate-h'))
import analyse  # noqa: E402

RATIO = 1.5
SHOWN = ('P1', 'P3', 'P4', 'P6', 'P7-w1', 'P8-w1', 'P8-w16')
PENALTY_MS = 2 * analyse.C_MS


def main():
    m = analyse.load()
    configs = analyse.CONTEXTS['W16']
    print('Cell cost in ms: median over clean repetitions of process wall, a repetition that is not a '
          'verified completion counted at 2C. **pen** = the cell median is the 2C penalty, not a time.\n')
    print(f"| family | record | {' | '.join(SHOWN)} | cheapest | P8-w1 ÷ cheapest | P4 ÷ cheapest |")
    print('|---|---|' + '---:|' * (len(SHOWN) + 3))
    shown = 0
    for rid in sorted(m.records, key=lambda r: (m.family_of[m.problem_of[r]], r)):
        cost = {c: m.cell(rid, c) for c in configs}
        best_cfg = min(cost, key=cost.get)
        best = cost[best_cfg]
        if best >= PENALTY_MS:
            continue  # no arm completes: the frontier record, listed below
        r8, r4 = cost['P8-w1'] / best, cost['P4'] / best
        if r8 < RATIO and r4 < RATIO:
            continue
        shown += 1
        cols = ' | '.join('**pen**' if cost[c] >= PENALTY_MS else f'{cost[c]:,.0f}' for c in SHOWN)
        fmt = lambda c, r: 'pen' if cost[c] >= PENALTY_MS else f'{r:.2f}'  # noqa: E731
        print(f"| `{m.family_of[m.problem_of[rid]]}` | `{rid}` | {cols} | {best_cfg} | "
              f"{fmt('P8-w1', r8)} | {fmt('P4', r4)} |")
    frontier = [r for r in m.records if all(m.cell(r, c) >= PENALTY_MS for c in configs)]
    print(f'\n{shown} of {len(m.records)} development records have P8-w1 or P4 penalized or at least '
          f'{RATIO}x the cheapest arm. Penalized on every arm (frontier): '
          + (', '.join(f'`{r}`' for r in sorted(frontier)) or 'none') + '.')


if __name__ == '__main__':
    main()
