#!/usr/bin/env python3
"""Count reconstruction IR nodes in every benchmark's optimized export."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
from pathlib import Path
import subprocess
import tempfile


def measure(binary, source):
    vm = "sp1" if source.parts[1] == "SP1" else "openvm"
    with tempfile.TemporaryDirectory() as tmp:
        target = Path(tmp) / "optimized.json"
        subprocess.run(
            [str(binary), "opt-export", vm, str(source), str(target)],
            check=True, capture_output=True, text=True,
        )
        blocks = json.loads(target.read_text())["reconstruction"]["blocks"]
    assignments = sum(map(len, blocks))
    pending = [expr for block in blocks for _, expr in block]
    expressions = 0
    while pending:
        expr = pending.pop()
        expressions += 1
        tag, args = next(iter(expr.items()))
        if tag in ("add", "mul", "if_zero"):
            pending.extend(args)
        elif tag not in ("const", "var"):
            raise ValueError(f"Unknown reconstruction expression: {tag}")
    return dict(case=str(source), blocks=len(blocks), assignments=assignments,
                expressions=expressions, nodes=len(blocks) + assignments + expressions)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=Path(".lake/build/bin/apc-optimizer"))
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    sources = sorted(p for p in Path("Benchmarks").glob("*/*/*.json.gz")
                     if ".powdr_opt." not in p.name)
    results = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(measure, args.binary.resolve(), source) for source in sources]
        for future in as_completed(futures):
            result = future.result()
            results.append(result)
            print(f"{len(results)}/{len(sources)} {result['case']}: {result['nodes']} nodes", flush=True)
            args.output.write_text(json.dumps(sorted(results, key=lambda r: r["case"]), indent=2) + "\n")


if __name__ == "__main__":
    main()
