#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Collect the sha256 runtime history into `sha256-runtime.csv` from the CI benchmark comments.

Every merged PR carries one `<!-- runtime-bench-quick -->` sticky comment from CI; since #202 added
the sha256 stress case on its own runner, that comment has a sha256 section with a `runtime` row
reporting `main` and `this branch`. This walks the merged PRs in merge order and pulls that row.

`bench_run_at` is when CI last wrote the comment — the plot needs it to spot a run whose base was
overtaken by later merges (see `plot_sha256_runtime.py`).

Needs `gh` authenticated against the repo.

    Benchmarks/history/collect_sha256_runtime.py
"""
from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = "powdr-labs/apc-optimizer"
FIELDS = ["pr", "merged_at", "bench_run_at", "runtime_main_s", "runtime_branch_s", "delta", "title"]


def gh_json(*args: str):
    out = subprocess.run(["gh", *args], capture_output=True, text=True, check=True).stdout
    return json.loads(out)


def sha_runtime(body: str) -> tuple[float, float, str] | None:
    """The (main, branch, delta) of the sha256 section's `runtime` row, if the comment has one."""
    heads = [m.start() for m in re.finditer(r"^###\s", body, re.M)] + [len(body)]
    for i in range(len(heads) - 1):
        section = body[heads[i] : heads[i + 1]]
        if not re.search(r"sha", section.split("\n")[0], re.I):
            continue
        row = re.search(r"^\|\s*runtime\s*\|(.+?)\|(.+?)\|(.+?)\|", section, re.M)
        if not row:
            continue
        secs = [re.search(r"([\d.]+)\s*s", row.group(i)) for i in (1, 2)]
        if all(secs):
            return float(secs[0].group(1)), float(secs[1].group(1)), row.group(3).strip()
    return None


def collect() -> list[dict]:
    prs = gh_json("pr", "list", "--repo", REPO, "--state", "merged", "--limit", "400",
                  "--json", "number,mergedAt,title")
    prs.sort(key=lambda p: p["mergedAt"])
    rows = []
    for pr in prs:
        comments = gh_json("api", f"repos/{REPO}/issues/{pr['number']}/comments", "--paginate")
        for c in comments:
            body = c.get("body") or ""
            if not body.startswith("<!-- runtime-bench-quick"):
                continue
            found = sha_runtime(body)
            if not found:
                continue
            main_s, branch_s, delta = found
            rows.append(dict(pr=pr["number"], merged_at=pr["mergedAt"], bench_run_at=c["updated_at"],
                             runtime_main_s=main_s, runtime_branch_s=branch_s, delta=delta,
                             title=pr["title"]))
            break
        print(f"  #{pr['number']}{'' if rows and rows[-1]['pr'] == pr['number'] else ' (no sha256 runtime)'}")
    return rows


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--csv", type=Path, default=HERE / "sha256-runtime.csv")
    args = ap.parse_args()
    rows = collect()
    with args.csv.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        w.writeheader()
        w.writerows(rows)
    print(f"wrote {args.csv} ({len(rows)} PRs)")


if __name__ == "__main__":
    main()
