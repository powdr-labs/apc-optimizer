#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["matplotlib>=3.8"]
# ///
"""Plot the sha256 optimizer runtime per merged PR from `sha256-runtime.csv`.

One point per merged PR, in merge order: the wall time CI measured for that PR's own branch on the
dedicated sha256 runner (`runtime_branch_s`), i.e. the runtime main had once the PR landed.

A CI run can be overtaken — merged long after it ran, with faster PRs landing in between — and then
its number describes a main that never existed. Such a PR is dropped from the line (never silently:
it is printed and noted on the chart). The test needs both halves of the evidence: later PRs merged
after this one's bench run, *and* the `main` the run reported disagreeing with the runtime the
previous PR left behind by more than `--overtaken-tol`. Intervening merges alone are common and
harmless; runner noise alone is ±4%.

    Benchmarks/history/plot_sha256_runtime.py            # writes sha256-runtime.{svg,png}
    Benchmarks/history/plot_sha256_runtime.py --log --show
"""
from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
from pathlib import Path

import matplotlib
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter, LogLocator

HERE = Path(__file__).resolve().parent

SURFACE = "#fafaf8"
PANEL = "#f7f9f6"
GRID = "#e4e9e1"
INK = "#1a1a1a"
INK_MUTED = "#8b8b86"
SERIES = "#2f6fde"


def ts(s: str) -> datetime:
    return datetime.strptime(s, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)


def load(csv_path: Path) -> list[dict]:
    with csv_path.open(newline="") as fh:
        rows = list(csv.DictReader(fh))
    for r in rows:
        r["merged"], r["benched"] = ts(r["merged_at"]), ts(r["bench_run_at"])
        r["main_s"], r["branch_s"] = float(r["runtime_main_s"]), float(r["runtime_branch_s"])
    rows.sort(key=lambda r: r["merged"])
    return rows


def drop_overtaken(rows: list[dict], tol: float) -> tuple[list[dict], list[tuple[dict, int]]]:
    kept, dropped = [], []
    for i, r in enumerate(rows):
        overtaken_by = [o for o in rows if r["benched"] < o["merged"] < r["merged"]]
        base = kept[-1]["branch_s"] if kept else None
        if overtaken_by and base and abs(r["main_s"] - base) / base > tol:
            dropped.append((r, len(overtaken_by)))
            continue
        kept.append(r)
    return kept, dropped


def plot(rows: list[dict], dropped: list[tuple[dict, int]], out_prefix: Path, log: bool, show: bool) -> None:
    xs = list(range(len(rows)))
    ys = [r["branch_s"] for r in rows]

    matplotlib.rcParams["font.family"] = ["Helvetica Neue", "Helvetica", "Arial", "DejaVu Sans"]
    matplotlib.rcParams["svg.fonttype"] = "none"

    fig, ax = plt.subplots(figsize=(13.5, 5.6))
    fig.patch.set_facecolor(SURFACE)
    ax.set_facecolor(PANEL)
    fig.subplots_adjust(left=0.068, right=0.98, top=0.85, bottom=0.235)

    ax.set_axisbelow(True)
    ax.grid(axis="y", color=GRID, linewidth=0.9)
    for spine in ax.spines.values():
        spine.set_color(GRID)
        spine.set_linewidth(0.9)
    ax.tick_params(length=0, pad=8)

    ax.plot(xs, ys, color=SERIES, linewidth=2.2, marker="o", markersize=8,
            markerfacecolor=SERIES, markeredgecolor=PANEL, markeredgewidth=1.8, clip_on=False,
            zorder=3)

    lo, hi = min(ys), max(ys)
    if log:
        ax.set_yscale("log")
        ax.set_ylim(lo * 0.88, hi * 1.3)  # headroom keeps the first point's label clear of the subtitle
        ax.yaxis.set_major_locator(LogLocator(base=10, subs=(1.0, 2.0, 3.0, 5.0, 8.0)))
        ax.yaxis.set_minor_locator(LogLocator(base=10, subs=()))
    else:
        pad = (hi - lo) * 0.14
        ax.set_ylim(lo - pad, hi + pad)
        ax.set_yticks([t for t in range(200, 1400, 200) if lo - pad <= t <= hi + pad])
    ax.yaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{v:.0f}s"))
    ax.tick_params(axis="y", labelcolor=INK_MUTED, labelsize=11)
    ax.set_xlim(-0.45, len(rows) - 0.55)
    ax.set_ylabel("seconds", color=INK_MUTED, fontsize=11, labelpad=10)

    # Endpoints only — a number on every point would just be the table again.
    for i, dy in ((0, 16), (len(rows) - 1, 16)):
        ax.annotate(f"{ys[i]:.0f} s", (xs[i], ys[i]), textcoords="offset points",
                    xytext=(0, dy), ha="center", color=INK, fontsize=11, fontweight="bold")

    ax.set_xticks(xs)
    ax.set_xticklabels([f"#{r['pr']}" for r in rows], color=INK, fontsize=10.5, fontweight="bold")
    xaxis = ax.get_xaxis_transform()
    day = None
    for x, r in zip(xs, rows):
        if r["merged"].date() != day:  # only when the day turns over — 26 repeats of "Jul 27" is noise
            day = r["merged"].date()
            ax.text(x, -0.075, f"{r['merged']:%b} {r['merged'].day}", transform=xaxis, ha="center",
                    va="top", color=INK_MUTED, fontsize=9.5)
        ax.text(x, -0.135, f"{r['merged']:%H:%M}", transform=xaxis, ha="center", va="top",
                color=INK_MUTED, fontsize=9.5)

    ax.set_title("runtime — optimizer wall time (sha256, 1 basic block)", loc="left",
                 color=INK, fontsize=13.5, fontweight="bold", pad=26)
    ax.text(0.0, 1.028, "as measured by CI on the dedicated sha256 runner", transform=ax.transAxes,
            color=INK_MUTED, fontsize=10.5, ha="left", va="bottom")
    caption = "pull request · merge time UTC (chronological →)"
    if dropped:
        omitted = ", ".join(f"#{r['pr']} (bench run overtaken by {n} later merges)" for r, n in dropped)
        caption += f"    ·    omitted: {omitted}"
    fig.text(0.524, 0.045, caption, color=INK_MUTED, fontsize=10.5, ha="center")

    suffix = "-log" if log else ""
    for ext in ("svg", "png"):
        out = out_prefix.with_name(f"{out_prefix.name}{suffix}").with_suffix(f".{ext}")
        fig.savefig(out, format=ext, dpi=200, facecolor=SURFACE)
        print(f"wrote {out}")
    if show:
        plt.show()


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--csv", type=Path, default=HERE / "sha256-runtime.csv")
    ap.add_argument("--out-prefix", type=Path, default=HERE / "sha256-runtime")
    ap.add_argument("--overtaken-tol", type=float, default=0.10)
    ap.add_argument("--log", action="store_true", help="log y axis — even weight to every relative gain")
    ap.add_argument("--show", action="store_true")
    args = ap.parse_args()
    rows, dropped = drop_overtaken(load(args.csv), args.overtaken_tol)
    for r, n in dropped:
        print(f"dropped #{r['pr']}: benched {r['bench_run_at']}, merged {r['merged_at']}, "
              f"{n} PRs merged in between, reported main {r['main_s']:.1f} s")
    plot(rows, dropped, args.out_prefix, args.log, args.show)


if __name__ == "__main__":
    main()
