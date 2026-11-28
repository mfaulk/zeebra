#!/usr/bin/env python3
"""Zeebra's linear algebra against FFLAS-FFPACK, SpaSM, M4RI and FLINT on one matrix set (#1209).

    tools/external/linalg-comparands.py --zeebra <linalg_comparands binary> --work <dir> \\
        [--set laptop|bench] [--workers 1,4] [--reps 3] [--out results.tsv]

Three phases, each refusing to start until the previous one is clean:

1. **Export.** Corpus batches through `linalg_comparands export` (rows reducers first, the split in
   the sidecar) and synthetic dense and uniformly sparse matrices through `synthetic`.
2. **Verify.** Every arm runs once at one worker. Its rank and RREF digest (or product digest)
   must equal Zeebra's `f4` arm's (or `matrix` product's); SpaSM's column-permuted RREF is brought
   to canonical form by `linalg_comparands canon` first. Any disagreement exits 1, before any
   timing is taken.
3. **Time.** Every (matrix, arm, workers) cell runs `--reps` times as its own process, cells
   interleaved within each repetition. Only the library's own elimination or product is inside
   the timed region (tools/external/linalg-drivers/common.h).

Thread counts are passed to each tool's own control and OMP_NUM_THREADS; BLAS is held at one
thread. The script records no host conditions: a pinned run belongs inside tools/bench-job.sh.
Exit status: 0 clean, 1 a disagreement, 2 a tool failed.
"""
import argparse
import os
import statistics
import subprocess
import sys

P31 = 2147483647
BABYBEAR = 2013265921
P64 = 18446744073709551557

# Corpus labels exported for the read. All of the prime-field corpus is at 2^31 - 1, 2^64 - 59 or 2.
CORPUS = {
    "laptop": [
        "katsura-7/grevlex/m31/default",
        "cyclic-6/lex/m31/default",
        "mq-random-6/grevlex/p31x64/baseline",
        "katsura-7/grevlex/m31/baseline",
        "mq-random-10/grevlex/p31x64/default",
        "katsura-6/lex/p64/baseline",
        "cyclic-7/grevlex/gf2/default",
    ],
}
CORPUS["bench"] = CORPUS["laptop"]

# (kind, rows, cols, per_row, prime, seed)
SYNTHETIC = {
    "laptop": [("dense", n, n, 0, p, 1) for n in (500, 1000, 2000)
               for p in (32003, 65521, BABYBEAR, P31, P64)]
    + [("dense", n, n, 0, 2, 1) for n in (1000, 4000)]
    + [("sparse", n, n, 6, p, 2) for n in (2000, 4000) for p in (32003, P31)]
    + [("sparse", 4000, 4000, 6, 2, 2)],
    "bench": [("dense", n, n, 0, p, 1) for n in (1000, 2000, 4000, 8000)
              for p in (32003, 65521, BABYBEAR, P31, P64)]
    + [("dense", n, n, 0, 2, 1) for n in (4000, 16000)]
    + [("sparse", n, n, 6, p, 2) for n in (4000, 16000) for p in (32003, P31)]
    + [("sparse", 16000, 16000, 6, 2, 2)],
}

MUL = {
    "laptop": [(n, p) for n in (500, 1000, 2000) for p in (32003, 65521, BABYBEAR, P31, P64)]
    + [(n, 2) for n in (2000, 8000)],
    "bench": [(n, p) for n in (500, 1000, 2000, 4000, 8000)
              for p in (32003, 65521, BABYBEAR, P31, P64)]
    + [(n, 2) for n in (2000, 8000, 32000)],
}

# The dense comparands allocate rows x cols words; the general Matrix path is cubic and generic.
DENSE_CELL_CAP = 160_000_000
MATRIX_CELL_CAP = 1_100_000
MATRIX_MUL_CAP = 1000


def lane_prime(p):
    return p == 31 or p == 32003 or 46337 < p < 2**31


def rref_arms(prime, cells):
    """(tool, arm) pairs that apply to a matrix; tool `zeebra` takes an arm, a driver does not."""
    arms = [("zeebra", "f4")]
    if lane_prime(prime):
        arms.append(("zeebra", "lane"))
    if prime in (31, 32003):
        arms.append(("zeebra", "blocked"))
    if prime == 2:
        arms.append(("zeebra", "gf2"))
    if cells <= MATRIX_CELL_CAP:
        arms.append(("zeebra", "matrix"))
    if cells <= DENSE_CELL_CAP:
        arms.append(("flint", None))
        if prime < 2**31:
            arms.append(("fflas", None))
        if prime == 2:
            arms.append(("m4ri", None))
    if prime < 2**32 - 5:
        arms.append(("spasm", None))
    return arms


def mul_arms(n, prime):
    arms = [("flint", None)]
    if n <= MATRIX_MUL_CAP:
        arms.insert(0, ("zeebra", "matrix"))
    if prime < 2**26:
        arms.append(("zeebra", "blocked"))
    if prime < 2**31:
        arms.append(("fflas", None))
    if prime == 2:
        arms.append(("m4ri", None))
    return arms


def parallel(tool, arm):
    """Whether a cell has a multi-worker route at all."""
    if tool == "zeebra":
        return arm == "f4"
    return tool in ("flint", "fflas", "spasm")


class ToolFailure(Exception):
    pass


def run(command, threads, extra_env=None, protocol=True):
    env = dict(os.environ, OMP_NUM_THREADS=str(threads), OPENBLAS_NUM_THREADS="1")
    env.update(extra_env or {})
    done = subprocess.run(command, env=env, capture_output=True, text=True)
    if done.returncode != 0:
        raise ToolFailure(f"{' '.join(command)}: exit {done.returncode}: {done.stderr.strip()[-400:]}")
    if not protocol:
        return None
    records = []
    for line in done.stdout.splitlines():
        if line.startswith(("rref ", "mul ", "canon ")):
            records.append(dict(t.split("=", 1) for t in line.split()[1:]))
    if not records:
        raise ToolFailure(f"{' '.join(command)}: no protocol line")
    return records[-1]


def command(args, tool, arm, task, threads):
    if tool == "zeebra":
        if task[0] == "rref":
            return [args.zeebra, "rref", task[1], arm, str(threads), "1"]
        return [args.zeebra, "mul", str(task[1]), str(task[2]), "1", arm, "1"]
    driver = os.path.join(args.prefix, "bin", f"linalg-{tool}")
    if task[0] == "rref":
        return [driver, "rref", task[1] + ".sms", str(task[2]), str(threads), "1"]
    return [driver, "mul", str(task[1]), str(task[2]), "1", str(threads), "1"]


def read_meta(base):
    with open(base + ".meta") as f:
        return dict(line.strip().split("=", 1) for line in f if "=" in line)


def sms_shape(base):
    with open(base + ".sms") as f:
        rows, cols, _ = f.readline().split()
    return int(rows), int(cols)


def export(args):
    os.makedirs(args.work, exist_ok=True)
    bases = []
    for label in CORPUS[args.set]:
        base = os.path.join(args.work, label.replace("/", "_"))
        if not os.path.exists(base + ".meta"):
            run([args.zeebra, "export", label, base], 1, protocol=False)
        bases.append(base)
    for kind, rows, cols, per_row, prime, seed in SYNTHETIC[args.set]:
        base = os.path.join(args.work, f"{kind}-{rows}x{cols}-p{prime}")
        if not os.path.exists(base + ".meta"):
            run([args.zeebra, "synthetic", kind, str(rows), str(cols), str(per_row), str(prime),
                 str(seed), base], 1, protocol=False)
        bases.append(base)
    return bases


def verify(args, cells):
    """Runs each cell once at one worker; returns the cells, or exits 1 on a disagreement."""
    clean = True
    for task, arms in cells:
        reference = None
        for tool, arm in arms:
            record = run(command(args, tool, arm, task, 1), 1,
                         {"LINALG_DUMP": args.dump} if tool == "spasm" else None)
            if tool == "spasm" and record.get("canonical") == "0":
                canon = run([args.zeebra, "canon", args.dump, str(task[2]), str(task[3])], 1)
                record["digest"] = canon["digest"]
            got = (record.get("rank"), record["digest"])
            name = tool + (f"/{arm}" if arm else "")
            if reference is None:
                reference = (name, got)
            elif got != reference[1]:
                clean = False
                print(f"DISAGREE {describe(task)}: {name} {got} vs {reference[0]} {reference[1]}",
                      file=sys.stderr)
        print(f"verified {describe(task)}: {len(arms)} arms agree on {reference[1]}", file=sys.stderr)
    if not clean:
        sys.exit(1)


def describe(task):
    if task[0] == "rref":
        return f"rref {os.path.basename(task[1])}"
    return f"mul n={task[1]} p={task[2]}"


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--zeebra", required=True)
    parser.add_argument("--work", required=True)
    parser.add_argument("--prefix",
                        default=os.environ.get("ZEEBRA_EXT_PREFIX",
                                               os.path.expanduser("~/.local/opt/zeebra-ext")))
    parser.add_argument("--set", choices=sorted(CORPUS), default="laptop")
    parser.add_argument("--workers", default="1,4")
    parser.add_argument("--reps", type=int, default=3)
    parser.add_argument("--out", default="-")
    parser.add_argument("--only", default="", help="substring a matrix or mul task must contain")
    args = parser.parse_args()
    args.dump = os.path.join(args.work, "spasm-rref.sms")
    workers = [int(w) for w in args.workers.split(",")]

    try:
        cells = []
        for base in export(args):
            prime = int(read_meta(base)["prime"])
            rows, cols = sms_shape(base)
            cells.append((("rref", base, prime, rows, cols), rref_arms(prime, rows * cols)))
        for n, prime in MUL[args.set]:
            cells.append((("mul", n, prime), mul_arms(n, prime)))
        cells = [c for c in cells if args.only in describe(c[0])]
        verify(args, cells)

        timings = {}
        for _ in range(args.reps):
            for task, arms in cells:
                for tool, arm in arms:
                    for w in workers:
                        if w > 1 and not parallel(tool, arm):
                            continue
                        record = run(command(args, tool, arm, task, w), w)
                        timings.setdefault((describe(task), tool, arm or "", w), []).append(
                            float(record["seconds"]))
    except ToolFailure as failure:
        print(f"linalg-comparands: {failure}", file=sys.stderr)
        sys.exit(2)

    out = sys.stdout if args.out == "-" else open(args.out, "w")
    print("task\ttool\tarm\tworkers\tmedian_s\tmin_s\treps", file=out)
    for (task, tool, arm, w), values in timings.items():
        print(f"{task}\t{tool}\t{arm}\t{w}\t{statistics.median(values):.6f}\t{min(values):.6f}\t"
              f"{len(values)}", file=out)


if __name__ == "__main__":
    main()
