#!/usr/bin/env python3
"""#1134: the cell table and the predeclared decision (README) from cells.jsonl, as Markdown.

  python3 research/1134-refusal-fallback/tables.py > research/1134-refusal-fallback/tables.md
"""
import json
import pathlib

HERE = pathlib.Path(__file__).resolve().parent


def ms(cell):
    return cell["call_ns"] / 1e6 if "call_ns" in cell else None


def outcome(cell):
    if cell is None:
        return "missing"
    if cell["status"] == "complete":
        return f"{ms(cell):,.0f} ms"
    error = (cell.get("error") or cell["status"]).split(" ")[0]
    return f"{cell['status']}: {error}"


def main():
    cells = {}
    for line in (HERE / "cells.jsonl").read_text().splitlines():
        c = json.loads(line)
        cells[(c["set"], c["id"], c["workers"], c["engine"])] = c
    rows = list(dict.fromkeys((s, i, w) for s, i, w, _ in cells))
    print("| set | record | w | adaptive (route) | fallback fired? | discarded attempt | fallback "
          "| sig alone | fallback ÷ sig | bases agree |")
    print("|---|---|---:|---|---|---|---|---|---:|---|")
    fired_oos = rescued_oos = 0
    for s, i, w in rows:
        a, f, g = (cells.get((s, i, w, e)) for e in ("adaptive", "fallback", "sig"))
        first = (f or {}).get("fallback_from")
        fired = bool(first)
        if s == "out-of-sample" and fired:
            fired_oos += 1
            if f["status"] == "complete" and a["status"] != "complete":
                rescued_oos += 1
        discarded = (f"{first['call_ns'] / 1e6:,.0f} ms, {first['error'].split(' ')[0]}"
                     if fired else "–")
        ratio = ("–" if not (f and g and f["status"] == g["status"] == "complete")
                 else f"{ms(f) / ms(g):.2f}")
        digests = {c.get("basis_sha256") for c in (a, f, g) if c and c["status"] == "complete"}
        agree = "–" if not digests else ("yes" if len(digests) == 1 else "**no**")
        route = (a or {}).get("route") or "–"
        print(f"| {s} | `{i}` | {w} | {outcome(a)} ({route}) | {'**yes**' if fired else 'no'} "
              f"| {discarded} | {outcome(f)} | {outcome(g)} | {ratio} | {agree} |")
    print(f"\nOut of sample: the rule fired in {fired_oos} cells and completed "
          f"{rescued_oos} that `adaptive` refused at the same worker count.")
    if fired_oos == 0:
        verdict = "no out-of-sample evidence"
    elif rescued_oos == 0:
        verdict = "rejected as written: it fired out of sample and never completed"
    else:
        verdict = "worth carrying into an M34-Q-style qualification"
    print(f"\n**Predeclared decision:** {verdict}.")


if __name__ == "__main__":
    main()
