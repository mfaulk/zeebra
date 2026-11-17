import gzip, json, sys
# Keep grobx's stock report and attempt metadata; drop the basis text.
src, dst = sys.argv[1], sys.argv[2]
a = json.loads(gzip.open(src).read())
keep = {k: a[k] for k in ["field", "name", "engine", "digest", "controller_commit", "exit", "stop",
                          "process_wall_ns", "observed_tree_peak_bytes"]}
keep["raw"] = {"report": a["raw"]["report"]}
keep["source"] = "research/wide-corpus/campaign.json.gz grobx attempt; report only, basis dropped"
with gzip.open(dst, "wt") as f:
    f.write(json.dumps(keep))
