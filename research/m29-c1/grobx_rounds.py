import gzip, json, re, sys
# Sum grobx's stock per-round report counters for one retained payload.
d = json.loads(gzip.open(sys.argv[1]).read())
raw = d["raw"]
report = raw.get("report") or ""
if not isinstance(report, str):
    report = json.dumps(report)
keys = ["rows", "given", "columns", "entries", "pivots", "zero", "zero-rows", "reductions", "subtracted", "added"]
rounds = []
for m in re.finditer(r"round number=(\d+) ([^\n\\]*)", report):
    kv = dict(re.findall(r"([\w-]+)=([^\s]+)", m.group(2)))
    rounds.append(kv)
print(d["field"], d["name"], "wall_ms", d["process_wall_ns"] / 1e6, "rss_MB", d["observed_tree_peak_bytes"] / 2**20)
print("rounds", len(rounds))
tot = {k: sum(int(r.get(k, 0)) for r in rounds) for k in keys}
print("totals", tot)
print("max rows", max(int(r["rows"]) for r in rounds), "max columns", max(int(r["columns"]) for r in rounds),
      "max entries", max(int(r["entries"]) for r in rounds))
print("bands", sorted({r.get("bands") for r in rounds}))
for line in re.findall(r"(rounds=\d+ reduced=[^\n\\]*)", report):
    print("summary:", line[:300])
for line in re.findall(r"(round=\d+ [^\n\\]*verdict=[^\n\\]*)", report)[-3:]:
    print("handover:", line[:200])
modes = re.findall(r"reduce=(\w+)", report)
print("reduce modes", {m: modes.count(m) for m in set(modes)})
for k in ("signature", "plain", "restart", "hand"):
    print(k, report.count(k))
if len(sys.argv) > 2:
    for r in rounds:
        print({k: r.get(k) for k in ["degree", "rows", "columns", "entries", "pivots", "zero-rows", "reductions", "subtracted", "bands"]})
