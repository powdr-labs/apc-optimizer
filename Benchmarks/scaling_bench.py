#!/usr/bin/env python3
"""Measure how the optimizer's runtime *scales* with circuit size, per pass.

`runtime_bench.py` measures wall time on fixed inputs. This measures the growth rate, which is a
different question: the optimizer can get uniformly faster while staying quadratic. To separate
"this pass is expensive" from "this pass is superlinear", we need inputs of the same *shape* at
several sizes.

The ladder is built by replication: rung `k` is `k` copies of one real APC with disjoint variables
(copy `c` renames every `<name>@<id>` to `<name>@<id + c*stride>`). Two properties make this the
right instrument:

  * A linear optimizer takes exactly `k x` the single-copy time, so the log-log slope of
    time-vs-`k` *is* the exponent -- no curve fitting against a guessed model.
  * The copies share nothing, so each copy's fixpoint runs exactly as it does alone. The cleanup
    iteration count therefore stays flat across rungs (it is reported; if it drifts, the rung is
    not comparable), which is what isolates per-pass cost from "bigger circuits need more rounds".

    Benchmarks/scaling_bench.py                        # default source APC, rungs 1,2,3,4,6,8
    Benchmarks/scaling_bench.py --rungs 1,2,4          # cheaper ladder
    Benchmarks/scaling_bench.py --source Benchmarks/OpenVM/keccak/apc_001_pckeccak.json.gz
    Benchmarks/scaling_bench.py --md scaling.md        # also write a markdown summary
    Benchmarks/scaling_bench.py --json out.json        # also dump raw results (for --compare)

To compare two runs (e.g. a PR head against main, both on the same machine -- exponents are more
robust than absolute times, but still measure both sides on one runner):

    Benchmarks/scaling_bench.py --compare base.json target.json --md scaling.md
"""
from __future__ import annotations

import argparse
import gzip
import json
import math
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]  # Benchmarks -> repo root
VM_DIR = {"openvm": "OpenVM", "sp1": "SP1"}
DEFAULT_SOURCE = "Benchmarks/OpenVM/openvm-eth/apc_005_pc0x32ab5c.json.gz"
DEFAULT_RUNGS = [1, 2, 3, 4, 6, 8]

# `apc-optimizer profile` output, shared with runtime_bench.py.
PROFILE_HEAD_RE = re.compile(r": (\d+) cleanup iterations, (\d+) ms total")
PROFILE_PASS_RE = re.compile(r"^\s+(\w+): (\d+) ms$", re.M)

# Times below this are dominated by noise and are excluded from the fit.
FIT_FLOOR_MS = 20


def parse_profile(out):
    m = PROFILE_HEAD_RE.search(out)
    if not m:
        return None
    passes = {name: int(ms) for name, ms in PROFILE_PASS_RE.findall(out)}
    return int(m.group(2)), int(m.group(1)), passes


def fmt_ms(ms):
    return f"{ms / 1000:.1f} s" if ms >= 10_000 else f"{ms} ms"


def fmt_exp(e):
    return "—" if e is None else f"{e:.2f}"


# --- input generation ------------------------------------------------------------------------

VAR_RE = re.compile(r"^(.*)@(\d+)$")


def shift_expr(e, off):
    """Rename every variable in a powdr expression tree, offsetting its `@<id>` by `off`.

    Mirrors `JsonParser.parseJsonExpr` positionally: a number is a constant, a string is a
    variable, a 3-element array is `[lhs, op, rhs]`, a 2-element array is `[op, operand]`.
    Operators are matched by position, never by value, so a variable named like an operator
    cannot be misread.
    """
    if isinstance(e, str):
        m = VAR_RE.match(e)
        if m is None:
            raise ValueError(
                f"variable {e!r} has no `@<id>` suffix, so copies could not be made disjoint")
        return f"{m.group(1)}@{int(m.group(2)) + off}"
    if isinstance(e, list):
        if len(e) == 3:
            return [shift_expr(e[0], off), e[1], shift_expr(e[2], off)]
        if len(e) == 2:
            return [e[0], shift_expr(e[1], off)]
        raise ValueError(f"expected a 2- or 3-element expression array, got {len(e)} elements")
    return e  # a JSON number: a constant


def max_var_id(machine):
    """The largest `@<id>` in the machine, so replicas can be offset past it."""
    top = -1

    def walk(e):
        nonlocal top
        if isinstance(e, str):
            m = VAR_RE.match(e)
            if m is not None:
                top = max(top, int(m.group(2)))
        elif isinstance(e, list):
            for x in (e[0], e[2]) if len(e) == 3 else e[1:]:
                walk(x)

    for c in machine["constraints"]:
        walk(c)
    for bi in machine["bus_interactions"]:
        walk(bi["mult"])
        for a in bi["args"]:
            walk(a)
    return top


def load_source(path):
    opener = gzip.open if path.name.endswith(".gz") else open
    with opener(path, "rt") as f:
        return json.load(f)


def build_rung(src, k, stride, out_path):
    """Write `k` disjoint copies of `src`'s machine to `out_path` (gzipped JSON).

    Only the keys `JsonParser.lean` reads are emitted: `machine.constraints`,
    `machine.bus_interactions`, `bus_map`, and `next_free_id`.
    """
    machine = src["machine"]
    constraints, interactions = [], []
    for c in range(k):
        off = c * stride
        constraints += [shift_expr(x, off) for x in machine["constraints"]]
        interactions += [{"id": bi["id"],
                          "mult": shift_expr(bi["mult"], off),
                          "args": [shift_expr(a, off) for a in bi["args"]]}
                         for bi in machine["bus_interactions"]]
    out = {"machine": {"constraints": constraints,
                       "bus_interactions": interactions,
                       "derived_columns": []},
           "bus_map": src["bus_map"],
           "next_free_id": k * stride}
    with gzip.open(out_path, "wt") as f:
        json.dump(out, f)
    return len(constraints), len(interactions)


# --- fitting ---------------------------------------------------------------------------------

def fit_exponent(rungs, values):
    """Least-squares log-log slope of `values` against `rungs`.

    `None` when fewer than three rungs clear `FIT_FLOOR_MS` -- a slope through two noisy points is
    not worth printing.
    """
    pts = [(k, v) for k, v in zip(rungs, values) if v >= FIT_FLOOR_MS]
    if len(pts) < 3:
        return None
    xs = [math.log(k) for k, _ in pts]
    ys = [math.log(v) for _, v in pts]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    sxx = sum((x - mx) ** 2 for x in xs)
    if sxx == 0:
        return None
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx


def vs_linear(rungs, values):
    """How much worse than linear the largest rung is, relative to the smallest usable one."""
    pts = [(k, v) for k, v in zip(rungs, values) if v >= FIT_FLOOR_MS]
    if len(pts) < 2:
        return None
    (k0, v0), (k1, v1) = pts[0], pts[-1]
    return (v1 / v0) / (k1 / k0)


# --- benchmarking ----------------------------------------------------------------------------

def bench(args):
    repo = args.repo.resolve()
    source = args.source if args.source.is_absolute() else repo / args.source
    if not source.exists():
        sys.exit(f"error: source APC {source} not found")

    binary = args.binary.resolve() if args.binary is not None else None
    os.chdir(repo)
    if binary is None:
        if not args.no_build:
            print("building apc-optimizer...", file=sys.stderr)
            subprocess.run(["lake", "build"], check=True)
        binary = repo / ".lake" / "build" / "bin" / "apc-optimizer"
    if not binary.exists():
        sys.exit(f"error: {binary} missing (build first, or pass --binary/--no-build correctly)")
    # The VM token is optional and defaults to openvm; omit it there so the command stays
    # compatible with binaries that predate the token (e.g. a latest-main baseline).
    vm_tok = [] if args.vm == "openvm" else [args.vm]

    src = load_source(source)
    stride = max_var_id(src["machine"]) + 1
    if stride <= 0:
        sys.exit(f"error: no `@<id>` variables in {source}; cannot build disjoint copies")

    total_ms, iters, sizes = {}, {}, {}
    pass_ms = {}  # pass name -> {rung -> ms}
    with tempfile.TemporaryDirectory(prefix="apc-scaling-") as tmp:
        for k in args.rungs:
            rung = Path(tmp) / f"rung{k:02d}.json.gz"
            ncs, nbis = build_rung(src, k, stride, rung)
            best = None
            for _ in range(args.repeat):
                out = subprocess.run([str(binary), "profile", *vm_tok, str(rung)],
                                     capture_output=True, text=True, check=True).stdout
                parsed = parse_profile(out)
                if parsed is None:
                    sys.exit(f"could not parse profile output for rung {k}:\n{out}")
                if best is None or parsed[0] < best[0]:
                    best = parsed
            total, its, passes = best
            total_ms[k], iters[k], sizes[k] = total, its, [ncs, nbis]
            for name, ms in passes.items():
                pass_ms.setdefault(name, {})[k] = ms
            print(f"[k={k}] {ncs} constraints, {nbis} interactions: "
                  f"{fmt_ms(total)}, {its} iterations", file=sys.stderr)
            rung.unlink()

    return {"source": str(source.relative_to(repo)) if source.is_relative_to(repo) else str(source),
            "rungs": list(args.rungs), "repeat": args.repeat, "stride": stride,
            "sizes": sizes, "total_ms": total_ms, "iters": iters, "pass_ms": pass_ms}


# --- reporting -------------------------------------------------------------------------------

def _rungs(data):
    """Rung keys as ints; JSON round-trips dict keys to strings."""
    return [int(k) for k in data["rungs"]]


def _series(m, rungs):
    return [m.get(str(k), m.get(k, 0)) for k in rungs]


def emit_md(data):
    rungs = _rungs(data)
    totals = _series(data["total_ms"], rungs)
    its = _series(data["iters"], rungs)

    lines = [f"### Runtime scaling — {data['source']}, {len(rungs)} rungs of disjoint replicas"
             + (f", best of {data['repeat']}" if data["repeat"] > 1 else ""), ""]
    lines.append("Rung `k` is `k` disjoint copies of the source APC, so a linear optimizer would "
                 "take exactly `k ×` the `k=1` time; the exponent is the log-log slope. "
                 "Iterations must stay flat for the rungs to be comparable.")
    lines.append("")
    lines.append("| k | constraints | interactions | total | vs. linear | iterations |")
    lines.append("|---|---|---|---|---|---|")
    base = totals[0] if totals else 0
    for k, t, it in zip(rungs, totals, its):
        ncs, nbis = _series(data["sizes"], [k])[0]
        rel = f"{(t / base) / (k / rungs[0]):.1f}×" if base else "—"
        lines.append(f"| {k} | {ncs} | {nbis} | {fmt_ms(t)} | {rel} | {it} |")
    lines.append("")
    lines.append(f"**Total exponent: {fmt_exp(fit_exponent(rungs, totals))}** "
                 f"(1.00 = linear).")
    lines.append("")
    lines.append("| pass | " + " | ".join(f"k={k}" for k in rungs) + " | exponent | vs. linear |")
    lines.append("|---" * (len(rungs) + 3) + "|")
    for name in sorted(data["pass_ms"], key=lambda n: -_series(data["pass_ms"][n], rungs)[-1]):
        series = _series(data["pass_ms"][name], rungs)
        if series[-1] < FIT_FLOOR_MS:
            continue
        rel = vs_linear(rungs, series)
        lines.append(f"| {name} | " + " | ".join(str(v) for v in series)
                     + f" | {fmt_exp(fit_exponent(rungs, series))} "
                     + f"| {'—' if rel is None else f'{rel:.1f}×'} |")
    lines.append("")
    lines.append(f"Passes under {FIT_FLOOR_MS} ms at the largest rung are omitted; an exponent "
                 f"needs three rungs above that floor.")
    return "\n".join(lines) + "\n"


def emit_compare_md(base, target):
    rungs = [k for k in _rungs(target) if k in _rungs(base)]
    if not rungs:
        return "No rungs in common between the two runs.\n"
    t_tot, b_tot = _series(target["total_ms"], rungs), _series(base["total_ms"], rungs)

    lines = [f"### Runtime scaling — {target['source']}, target vs baseline (same runner)", ""]
    lines.append("Exponent 1.00 = linear in circuit size. Δ = target / baseline; below 1× means "
                 "the target is faster.")
    lines.append("")
    lines.append("| | target | baseline |")
    lines.append("|---|---|---|")
    lines.append(f"| total exponent | **{fmt_exp(fit_exponent(rungs, t_tot))}** "
                 f"| {fmt_exp(fit_exponent(rungs, b_tot))} |")
    lines.append(f"| largest rung (k={rungs[-1]}) | {fmt_ms(t_tot[-1])} | {fmt_ms(b_tot[-1])} |")
    lines.append("")
    lines.append("| pass | target exp | baseline exp | target k=%d | baseline k=%d | Δ |"
                 % (rungs[-1], rungs[-1]))
    lines.append("|---|---|---|---|---|---|")
    names = set(base["pass_ms"]) | set(target["pass_ms"])
    for name in sorted(names, key=lambda n: -_series(target["pass_ms"].get(n, {}), rungs)[-1]):
        t = _series(target["pass_ms"].get(name, {}), rungs)
        b = _series(base["pass_ms"].get(name, {}), rungs)
        if max(t[-1], b[-1]) < FIT_FLOOR_MS:
            continue
        delta = "∞" if t[-1] and not b[-1] else ("—" if not t[-1] else f"{t[-1] / b[-1]:.2f}×")
        lines.append(f"| {name} | {fmt_exp(fit_exponent(rungs, t))} "
                     f"| {fmt_exp(fit_exponent(rungs, b))} | {t[-1]} | {b[-1]} | {delta} |")
    t_it, b_it = _series(target["iters"], rungs), _series(base["iters"], rungs)
    if t_it != b_it:
        lines.append("")
        lines.append(f"⚠ cleanup iterations differ: target {t_it} vs baseline {b_it} — the two "
                     f"sides did different amounts of work, so read the exponents with care.")
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--source", type=Path, default=Path(DEFAULT_SOURCE), metavar="APC.json[.gz]",
                    help=f"APC to replicate (default: {DEFAULT_SOURCE})")
    ap.add_argument("--rungs", default=",".join(map(str, DEFAULT_RUNGS)),
                    help=f"comma-separated copy counts (default: {','.join(map(str, DEFAULT_RUNGS))})")
    ap.add_argument("--vm", choices=sorted(VM_DIR), default="openvm",
                    help="VM whose fact-aware optimizer to use (default: openvm)")
    ap.add_argument("--repeat", type=int, default=1,
                    help="runs per rung; the fastest is kept (default: 1)")
    ap.add_argument("--no-build", action="store_true",
                    help="skip `lake build` (the binary must already exist)")
    ap.add_argument("--binary", type=Path, default=None, metavar="EXE",
                    help="bench this apc-optimizer executable instead of building the repo's; "
                         "implies no build")
    ap.add_argument("--repo", type=Path, default=REPO, metavar="DIR",
                    help="repository to build and bench (default: the one holding this script; "
                         "lets a saved copy of the script bench another checkout, e.g. a baseline)")
    ap.add_argument("--md", type=Path, default=None, metavar="OUT.md",
                    help="also write a markdown summary (for CI job summaries / PR comments)")
    ap.add_argument("--json", type=Path, default=None, metavar="OUT.json",
                    help="also dump the raw per-rung/per-pass results (input for --compare)")
    ap.add_argument("--compare", nargs=2, default=None, metavar=("BASE.json", "TARGET.json"),
                    help="don't bench; render a comparison of two --json dumps instead")
    args = ap.parse_args()

    if args.compare is not None:
        base, target = (json.loads(Path(p).read_text()) for p in args.compare)
        md = emit_compare_md(base, target)
        print(md, end="")
        if args.md is not None:
            args.md.write_text(md)
        return

    try:
        args.rungs = sorted({int(x) for x in args.rungs.split(",") if x.strip()})
    except ValueError:
        sys.exit(f"error: --rungs must be a comma-separated list of integers, got {args.rungs!r}")
    if not args.rungs or args.rungs[0] < 1:
        sys.exit("error: --rungs must contain positive integers")

    data = bench(args)
    md = emit_md(data)
    print(md, end="")
    if args.md is not None:
        args.md.write_text(md)
    if args.json is not None:
        args.json.write_text(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
