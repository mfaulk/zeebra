#!/usr/bin/env python3
"""#1035: the comparison tables and the predeclared decision, as Markdown.

  python3 research/1035-sparse-toric/tables.py > research/1035-sparse-toric/tables.md

Size is rows × columns. Sparse rows are the rank at the witness degree (an F5-pruned matrix);
Zeebra's are conventional F4's largest matrix, `max_matrix_rows × max_matrix_columns`. The
advantage is Zeebra ÷ sparse: above 1, the sparse matrix is the smaller one.
"""
import json
import pathlib

HERE = pathlib.Path(__file__).resolve().parent


def lines(name):
    return [json.loads(l) for l in (HERE / name).read_text().splitlines() if l.strip()]


def area(rows, columns):
    return rows * columns


def fmt(x):
    return f"{x:.3g}" if x >= 1e6 else f"{x:,}"


def paper_table():
    f4 = {}
    for r in lines("f4.jsonl"):
        f4.setdefault((r["nx"], r["ny"], r["m"], r["dx"], r["perturb"]), []).append(r)
    print("## Reproduction: the paper's shapes (development)\n")
    print("Seeds 1–2. Where both seeds complete, the F4 extents are equal on every unperturbed shape, "
          "so one figure is shown; `—` marks a shape the example does not instantiate.\n")
    print("| table | n_x | n_y | m | sparse d_wit | sparse rank × columns | F4 largest | F4 step degree "
          "| advantage | control: sparse d_wit, columns | control: F4 |")
    print("|---|---:|---:|---:|---:|---|---|---:|---:|---|---|")
    advantages = []
    for p in json.loads((HERE / "paper.json").read_text()):
        key = (p["nx"], p["ny"], p["m"], p["dx"])
        s, c = p["sparse"], p["control"]
        sparse = area(s["rank_rows"], s["columns"])
        runs, controls = f4.get(key + (0,)), f4.get(key + (1,))

        def outcome(rs):
            if not rs:
                return "—", None
            done = [r for r in rs if r["status"] == "complete"]
            if len(done) < len(rs):
                return f"refused {len(rs) - len(done)}/{len(rs)} (`TooManyNonzeros`)", None
            big = max(rs, key=lambda r: area(r["max_matrix_rows"], r["max_matrix_columns"]))
            return (f"{big['max_matrix_rows']:,} × {big['max_matrix_columns']:,}",
                    area(big["max_matrix_rows"], big["max_matrix_columns"]))

        text, zeebra = outcome(runs)
        degree = max(r["max_pair_degree"] for r in runs) if runs else "—"
        adv = "—"
        if zeebra:
            advantages.append((p["table"], key, zeebra / sparse))
            adv = f"{zeebra / sparse:.2f}"
        ctext, _ = outcome(controls)
        print(f"| {p['table']} | {p['nx']} | {p['ny']} | {p['m']} | {s['witness_degree']} "
              f"| {s['rank_rows']:,} × {s['columns']:,} | {text} | {degree} | {adv} "
              f"| {c['witness_degree']}, {fmt(c['columns'])} | {ctext} |")
    values = sorted(a for _, _, a in advantages)
    print(f"\nAdvantage over {len(values)} completed shapes: min {values[0]:.2f}, median "
          f"{values[len(values) // 2]:.2f}, max {values[-1]:.2f}; "
          f"{sum(v >= 10 for v in values)} at ≥ 10×, {sum(v < 1 for v in values)} below 1×.\n")


def public_table():
    f4 = {r["name"].split("@")[0]: r for r in lines("public-f4.jsonl")}
    print("## Public panel: the eligible problems (development)\n")
    print("| problem | blocks (n_j, degree) | normalized volume | affine solutions | sparse d_wit "
          "| sparse rank × columns | F4 largest | advantage |")
    print("|---|---|---:|---:|---:|---|---|---:|")
    advantages = []
    for p in json.loads((HERE / "public.json").read_text()):
        blocks = ", ".join(f"({n}, {d})" for n, d in p["blocks"])
        if p["sparse"] is None:
            print(f"| `{p['id']}` | {blocks} | — | — | — | not counted: {p['note']} | — | — |")
            continue
        s, r = p["sparse"], f4[p["id"]]
        st = r["statistics"]
        zeebra = area(st["max_matrix_rows"], st["max_matrix_columns"])
        adv = zeebra / area(s["rank_rows"], s["columns"])
        advantages.append(adv)
        print(f"| `{p['id']}` | {blocks} | {fmt(s['normalized_volume'])} | {p['vdim']} "
              f"| {s['witness_degree']} | {fmt(s['rank_rows'])} × {fmt(s['columns'])} "
              f"| {st['max_matrix_rows']:,} × {st['max_matrix_columns']:,} | {adv:.2g} |")
    print()
    best = max(advantages)
    if best >= 10:
        verdict = "positive feasibility: file the prototype proposal"
    elif best < 3:
        verdict = "disproved: the advantage is under 3× on every eligible public problem"
    else:
        verdict = "defer"
    print(f"Largest advantage on an eligible public problem: {best:.2g}.\n")
    print(f"**Predeclared decision:** {verdict}.")


def main():
    paper_table()
    public_table()


if __name__ == "__main__":
    main()
