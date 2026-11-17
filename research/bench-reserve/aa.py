import json, subprocess, sys, time

# A/A pairs: the same binary run twice back to back on the reserved CPUs; the ratio's spread is
# what an interleaved A/B comparison inherits as noise.
BIN, ARM, PAIRS, OUT = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
SUBJECTS = [("mq10-1w", "mq10-32003", 1, "8"), ("eco12-16w", "eco12-wide64", 16, "8-23")]


def wall(target, w, cpus):
    t0 = time.perf_counter()
    subprocess.run(["taskset", "-c", cpus, BIN, "--target", target, "--workers", str(w)],
                   capture_output=True, check=True)
    return (time.perf_counter() - t0) * 1000


with open(OUT, "a") as out:
    for i in range(PAIRS):
        for name, target, w, cpus in SUBJECTS:
            a = wall(target, w, cpus)
            b = wall(target, w, cpus)
            out.write(json.dumps({"arm": ARM, "subject": name, "pair": i, "a": a, "b": b}) + "\n")
            out.flush()
