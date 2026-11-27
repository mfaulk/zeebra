# #1168 evidence: bounded ZDD normal forms

**Measured at:** `2eb16995`, macOS arm64 laptop, unpinned, release build with thin LTO and
codegen-units 16. These are development figures only. The note is
[`docs/research/boolean-zdd-normal-forms.md`](../../docs/research/boolean-zdd-normal-forms.md).

- `results.csv` has one row per family, size and order (natural, or scrambled 1–5). It records
  both routes' times as the median of 5 runs, and for the ZDD route the node, unique-table and
  cache counters and its heap estimate. For the ANF route it records peak terms and products.
  Statuses are `ok` or a typed refusal.
- `verdict.txt` is the example's stderr. It holds the mechanical evaluation of the predeclared
  criterion, then `/usr/bin/time -l` for the whole run.
- `tables.md` is `python3 research/1168-zdd/summarize.py > research/1168-zdd/tables.md`.

Regenerate with the command in the note's §9.
