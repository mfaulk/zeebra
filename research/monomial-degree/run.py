import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--repetitions", type=int, default=31)
    args = parser.parse_args()
    if args.repetitions < 3:
        parser.error("at least three repetitions are required")
    for name in ("ZEEBRA_MACHINE", "ZEEBRA_AFFINITY"):
        if not os.environ.get(name):
            parser.error(f"{name} must be set")
    args.output.mkdir(parents=True, exist_ok=True)
    metadata = {
        "completed": False,
        "machine": os.environ["ZEEBRA_MACHINE"],
        "affinity": os.environ["ZEEBRA_AFFINITY"],
        "repetitions": args.repetitions,
        "binaries": {
            name: hashlib.sha256(path.read_bytes()).hexdigest()
            for name, path in (("before", args.before), ("after", args.after))
        },
    }
    metadata_path = args.output / "metadata.json"
    metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")
    fields = [
        "case", "repetition", "arm", "total_ms", "symbolic_ms", "construction_ms",
        "elimination_ms", "interreduction_ms", "peak_rss_bytes", "basis_sha256",
    ]
    with (args.output / "samples.csv").open("w", newline="") as output:
        writer = csv.DictWriter(output, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        for case in ("katsura-5-lex", "katsura-6-lex", "katsura-7-grlex", "katsura-7-grevlex"):
            expected = None
            for repetition in range(args.repetitions):
                arms = [("before", args.before), ("after", args.after)]
                if repetition % 2:
                    arms.reverse()
                for arm, binary in arms:
                    result = subprocess.run(
                        ["taskset", "-c", metadata["affinity"], str(binary.resolve()), case],
                        capture_output=True, check=True, timeout=120,
                    )
                    if expected is None:
                        expected = result.stdout
                    if not expected or result.stdout != expected:
                        raise RuntimeError(f"full basis mismatch: {case} {arm} {repetition}")
                    values = dict(re.findall(r"(\w+)=(?:Some\()?([0-9.]+)", result.stderr.decode()))
                    sample = {field: values[field] for field in fields[3:-1]}
                    writer.writerow(dict(
                        case=case, repetition=repetition, arm=arm,
                        basis_sha256=hashlib.sha256(result.stdout).hexdigest(), **sample,
                    ))
                    output.flush()
    metadata["completed"] = True
    metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")


if __name__ == "__main__":
    main()
