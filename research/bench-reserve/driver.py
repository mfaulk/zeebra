import json, subprocess, sys, time

REPO, BIN, ARM, REPS, OUT = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
SUBJECTS = [
    ("mq10-1w", "mq10-32003", 1, "8"),
    ("mq10-16w", "mq10-32003", 16, "8-23"),
    ("eco12-16w", "eco12-wide64", 16, "8-23"),
]


def ctx(cpus):
    r = subprocess.run(["bash", f"{REPO}/tools/cpu-context.sh", cpus], capture_output=True, text=True)
    return json.loads(r.stdout) if r.returncode == 0 else None


with open(OUT, "a") as out:
    for rep in range(REPS):
        order = SUBJECTS[rep % 3:] + SUBJECTS[:rep % 3]
        for name, target, w, cpus in order:
            before = ctx(cpus)
            t0 = time.perf_counter()
            r = subprocess.run(["taskset", "-c", cpus, BIN, "--target", target, "--workers", str(w)],
                               capture_output=True, text=True)
            wall = (time.perf_counter() - t0) * 1000
            after = ctx(cpus)
            d = json.loads(r.stdout) if r.returncode == 0 else {}
            out.write(json.dumps({
                "arm": ARM, "subject": name, "rep": rep, "wall_ms": round(wall, 2), "rc": r.returncode,
                "status": d.get("status"), "f4_ms": (d.get("f4_call_ns") or 0) / 1e6,
                "rss": d.get("peak_rss_bytes"), "basis": d.get("basis_sha256"),
                "before": before, "after": after,
            }) + "\n")
            out.flush()
