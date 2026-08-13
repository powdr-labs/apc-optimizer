#!/usr/bin/env python3
"""Benchmark the *runtime* of the optimizer over a benchmark set.

For each case, run:
  - `apc-optimizer run <case>`      -> wall time of the whole optimizer call (the "(N ms)" line)
  - `apc-optimizer profile <case>`  -> per-pass timing, cumulative across all fixpoint iterations

and aggregate: total/mean/median optimizer time, the slowest cases, and where the time goes
per pass across the whole set. Cases run *serially* so timings don't fight for cores.

Where available, each case is also run once under the platform's CPU counters (`perf stat` on
Linux, `/usr/bin/time -l` on macOS) to report cycles, instructions and IPC. That is what separates
the two kinds of speedup: fewer *instructions* means less work (an algorithmic win), while flat
instructions at fewer *cycles* means less stalling (a memory/layout win, invisible to per-pass
timing because it taxes every pass alike). `--compare` classifies the change on that basis.

This measures runtime only; effectiveness is benchmark.py's job.

    Benchmarks/runtime_bench.py                 # all openvm-eth cases
    Benchmarks/runtime_bench.py sp1:rsp         # any set, as a <vm>:<set> token
    Benchmarks/runtime_bench.py --vm sp1        # same, via the flag (default set for the VM)
    Benchmarks/runtime_bench.py --n 20          # top 20 by cost rank
    Benchmarks/runtime_bench.py --repeat 3      # best-of-3 per case (less noise)
    Benchmarks/runtime_bench.py --md bench.md   # also write a markdown summary
    Benchmarks/runtime_bench.py --json out.json # also dump raw results (for --compare)

To compare two runs (e.g. a PR head against main, both benched on the same machine — timings
from different machines don't compare), dump each with --json and then:

    Benchmarks/runtime_bench.py --compare base.json target.json --md bench.md
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]  # Benchmarks -> repo root
# VM -> its benchmark directory under Benchmarks/ and its default (main) set.
VM_DIR = {"openvm": "OpenVM", "sp1": "SP1"}
DEFAULT_BENCHMARK = {"openvm": "openvm-eth", "sp1": "rsp"}



def available_sets(repo):
    """Every benchmark set in the corpus, as `<vm>:<set>` tokens."""
    out = []
    for vm, d in VM_DIR.items():
        root = repo / "Benchmarks" / d
        if root.is_dir():
            out += [f"{vm}:{p.name}" for p in sorted(root.iterdir())
                    if p.is_dir() and any(p.glob("apc_*_pc*.json.gz"))]
    return out


def resolve_set(repo, benchmark, vm):
    """Resolve the set selector to `(vm, set, directory)`.

    The selector is either a bare set name (interpreted under `vm`, which defaults to openvm) or a
    `<vm>:<set>` token — the form `lean_action_ci.yml` uses — so every set in the corpus is
    reachable through a single argument, e.g. through a workflow's `benchmark` input.
    """
    if benchmark and ":" in benchmark:
        tok_vm, _, tok_set = benchmark.partition(":")
        if tok_vm not in VM_DIR:
            sys.exit(f"error: unknown VM {tok_vm!r} in {benchmark!r} "
                     f"(known: {', '.join(sorted(VM_DIR))})")
        if vm is not None and vm != tok_vm:
            sys.exit(f"error: --vm {vm} contradicts {benchmark!r}")
        vm, benchmark = tok_vm, tok_set or DEFAULT_BENCHMARK[tok_vm]
    else:
        vm = vm or "openvm"
        benchmark = benchmark or DEFAULT_BENCHMARK[vm]
    bench_dir = repo / "Benchmarks" / VM_DIR[vm] / benchmark
    if not bench_dir.is_dir():
        sys.exit(f"error: no benchmark set {vm}:{benchmark} under {bench_dir.parent} "
                 f"(available: {', '.join(available_sets(repo)) or 'none found'})")
    return vm, benchmark, bench_dir


# `apc-optimizer run` total, e.g. "  (339 ms)".
RUN_MS_RE = re.compile(r"^\s*\((\d+) ms\)\s*$", re.M)
# `apc-optimizer profile` header, e.g. "profile <file>: 3 cleanup iterations, 311 ms total".
PROFILE_HEAD_RE = re.compile(r": (\d+) cleanup iterations, (\d+) ms total")
# `apc-optimizer profile` per-pass line, e.g. "  domainBatch: 258 ms".
PROFILE_PASS_RE = re.compile(r"^\s+(\w+): (\d+) ms$", re.M)


# CPU counters, read from whichever tool the platform has. Both report the whole process, so
# parse/IO is included -- fine for classifying a change (the ratios move together), not for
# attributing absolute counts to the optimizer.
PERF_EVENTS = "cycles,instructions"
# `/usr/bin/time -l`, e.g. "         26387451617  instructions retired".
TIME_L_RE = re.compile(r"^\s*(\d+)\s+(instructions retired|cycles elapsed|"
                       r"maximum resident set size)\s*$", re.M)
TIME_L_KEY = {"instructions retired": "instructions", "cycles elapsed": "cycles",
              "maximum resident set size": "max_rss"}


def counter_backend():
    """The available CPU-counter tool, or None (counters are then simply omitted)."""
    if sys.platform.startswith("linux") and shutil.which("perf"):
        return "perf"
    if sys.platform == "darwin" and Path("/usr/bin/time").exists():
        return "time-l"
    return None


def read_counters(cmd, backend):
    """{cycles, instructions, max_rss?} for one run of `cmd`, or None if the tool refused (perf is
    commonly blocked by perf_event_paranoid in containers)."""
    if backend == "perf":
        p = subprocess.run(["perf", "stat", "-x,", "-e", PERF_EVENTS, "--", *cmd],
                           capture_output=True, text=True)
        vals = {}
        for line in p.stderr.splitlines():
            f = line.split(",")
            if len(f) >= 3:
                try:
                    vals[f[2]] = int(float(f[0]))
                except ValueError:
                    pass  # "<not counted>" / "<not supported>" / header noise
        got = {k: vals[k] for k in ("cycles", "instructions") if k in vals}
        return got if len(got) == 2 else None
    if backend == "time-l":
        p = subprocess.run(["/usr/bin/time", "-l", *cmd], capture_output=True, text=True)
        got = {TIME_L_KEY[name]: int(v) for v, name in TIME_L_RE.findall(p.stderr)}
        return got if "cycles" in got and "instructions" in got else None
    return None


def ipc(c):
    return c["instructions"] / c["cycles"] if c and c.get("cycles") else None


def sum_counters(per_case):
    """Sum cycles/instructions over cases; max the peak RSS (it is a peak, not a total)."""
    cs = [c for c in per_case.values() if c]
    if not cs:
        return None
    out = {k: sum(c[k] for c in cs) for k in ("cycles", "instructions")}
    rss = [c["max_rss"] for c in cs if "max_rss" in c]
    if rss:
        out["max_rss"] = max(rss)
    return out


def classify(base, target):
    """One line saying whether a change moved work or stalls -- the diagnosis that per-pass timing
    cannot give. Thresholds are deliberately loose; counters carry a few % of run-to-run noise."""
    b, t = sum_counters(base), sum_counters(target)
    if not b or not t:
        return None
    di = t["instructions"] / b["instructions"]
    dc = t["cycles"] / b["cycles"]
    if abs(di - 1) < 0.02 and dc < 0.98:
        kind = ("**memory-bound win**: instructions are flat, so the same work now stalls less "
                "(layout/locality, not algorithm)")
    elif abs(di - 1) < 0.02 and dc > 1.02:
        kind = ("**memory-bound regression**: instructions are flat but cycles rose -- the same "
                "work stalls more")
    elif di < 0.98:
        kind = "**algorithmic win**: fewer instructions retired (less work)"
    elif di > 1.02 and dc < 0.98:
        kind = ("**net win despite more work**: instructions rose but cycles fell -- typically "
                "trading a cheap traversal for better locality")
    elif di > 1.02:
        kind = "**more work**: instructions retired rose"
    else:
        kind = "no significant change in either counter"
    return (f"Counters (whole process, summed): Δ instructions {di:.2f}×, Δ cycles {dc:.2f}×, "
            f"IPC {ipc(b):.2f} → {ipc(t):.2f} — {kind}.")


def best_of(cmd, repeat, parse):
    """Run `cmd` `repeat` times, parse each output, return the result with the smallest key.
    Taking the minimum discards scheduling noise (the optimizer is deterministic)."""
    best = None
    for _ in range(repeat):
        out = subprocess.run(cmd, capture_output=True, text=True, check=True).stdout
        parsed = parse(out)
        if parsed is None:
            raise ValueError(f"could not parse output of {' '.join(map(str, cmd))}:\n{out}")
        if best is None or parsed[0] < best[0]:
            best = parsed
    return best


def parse_run(out):
    m = RUN_MS_RE.search(out)
    return (int(m.group(1)),) if m else None


def parse_profile(out):
    m = PROFILE_HEAD_RE.search(out)
    if not m:
        return None
    passes = {name: int(ms) for name, ms in PROFILE_PASS_RE.findall(out)}
    return int(m.group(2)), int(m.group(1)), passes


def fmt_ms(ms):
    return f"{ms / 1000:.1f} s" if ms >= 10_000 else f"{ms} ms"


def fmt_ratio(target, base):
    """target / base, so < 1× means the target got faster. When both sides are tiny the ratio
    is scheduling noise, not signal — render it as —."""
    if max(target, base) < 50:
        return "—"
    if base == 0:
        return "∞"
    return f"{target / base:.2f}×"


def bench(args):
    """Run the benchmark, returning {benchmark, repeat, run_ms, pass_ms, iters}."""
    repo = args.repo.resolve()
    vm, benchmark, bench_dir = resolve_set(repo, args.benchmark, args.vm)
    # The VM token is optional and defaults to openvm; omit it for openvm so the commands stay
    # compatible with older binaries (e.g. a latest-main baseline) that predate the token.
    vm_tok = [] if vm == "openvm" else [vm]

    binary = args.binary.resolve() if args.binary is not None else None
    os.chdir(repo)
    if binary is None:
        if not args.no_build:
            print("building apc-optimizer...", file=sys.stderr)
            subprocess.run(["lake", "build"], check=True)
        binary = repo / ".lake" / "build" / "bin" / "apc-optimizer"
    if not binary.exists():
        sys.exit(f"error: {binary} missing (build first, or pass --binary/--no-build correctly)")

    cases = sorted(f for f in bench_dir.glob("apc_*_pc*.json.gz")
                   if not f.name.endswith(".powdr_opt.json.gz"))
    if not cases:
        sys.exit(f"no benchmark cases in {bench_dir}")
    if args.n is not None:
        cases = cases[: args.n]

    backend = None if args.no_counters else counter_backend()
    run_ms = {}          # case name -> optimizer call wall time (ms)
    pass_ms = {}         # pass name -> cumulative ms across all cases
    iters = {}           # case name -> cleanup iterations
    counters = {}        # case name -> {cycles, instructions, max_rss?}
    for i, case in enumerate(cases):
        (total,) = best_of([str(binary), "run", *vm_tok, str(case)], args.repeat, parse_run)
        _, its, passes = best_of([str(binary), "profile", *vm_tok, str(case)],
                                 args.repeat, parse_profile)
        if backend:
            c = read_counters([str(binary), "run", *vm_tok, str(case)], backend)
            if c is None:
                print(f"note: {backend} reported no counters; continuing without them",
                      file=sys.stderr)
                backend = None
            else:
                counters[case.name] = c
        run_ms[case.name] = total
        iters[case.name] = its
        for name, ms in passes.items():
            pass_ms[name] = pass_ms.get(name, 0) + ms
        print(f"[{i + 1}/{len(cases)}] {case.name}: {fmt_ms(total)}, {its} iterations",
              file=sys.stderr)
    return {"benchmark": benchmark, "vm": vm, "repeat": args.repeat,
            "run_ms": run_ms, "pass_ms": pass_ms, "iters": iters,
            "counters": counters, "counter_backend": backend}


def summary_stats(run_ms):
    times = sorted(run_ms.values())
    return sum(times), sum(times) // len(times), int(statistics.median(times)), times[-1]


def set_label(data):
    """The set's display name, VM-qualified unless it is the default VM (`benchmark.py` names the
    VM the same way, so OpenVM `keccak` and SP1 `keccak` never read alike)."""
    vm = data.get("vm", "openvm")
    return data["benchmark"] if vm == "openvm" else f"{vm}:{data['benchmark']}"


def emit_md(data):
    """Markdown summary of one benchmark run."""
    run_ms, pass_ms, iters = data["run_ms"], data["pass_ms"], data["iters"]
    total, mean, median, worst = summary_stats(run_ms)
    pass_total = sum(pass_ms.values())
    passes = sorted(pass_ms.items(), key=lambda kv: -kv[1])

    lines = []
    lines.append(f"### Optimizer runtime — {set_label(data)}, {len(run_ms)} cases"
                 + (f", best of {data['repeat']}" if data["repeat"] > 1 else ""))
    lines.append("")
    lines.append("| total | mean | median | max |")
    lines.append("|---|---|---|---|")
    lines.append(f"| {fmt_ms(total)} | {fmt_ms(mean)} | {fmt_ms(median)} | {fmt_ms(worst)} |")
    lines.append("")
    lines.append("<details><summary>Slowest cases (whole optimizer call)</summary>")
    lines.append("")
    lines.append("| case | time |")
    lines.append("|---|---|")
    for name, ms in sorted(run_ms.items(), key=lambda kv: -kv[1])[:10]:
        lines.append(f"| {name} | {fmt_ms(ms)} |")
    lines.append("")
    lines.append("</details>")
    lines.append("")
    lines.append(f"Per-pass time, cumulative over all cases and fixpoint iterations "
                 f"({fmt_ms(pass_total)} attributed):")
    lines.append("")
    lines.append("| pass | time | share |")
    lines.append("|---|---|---|")
    for name, ms in passes:
        if ms == 0:
            continue
        share = 100 * ms / pass_total if pass_total else 0
        lines.append(f"| {name} | {fmt_ms(ms)} | {share:.1f}% |")
    zero = [name for name, ms in passes if ms == 0]
    if zero:
        lines.append(f"| {', '.join(zero)} | 0 ms | — |")
    lines.append("")
    lines.append(f"Cleanup iterations per case: "
                 f"min {min(iters.values())}, median {int(statistics.median(iters.values()))}, "
                 f"max {max(iters.values())}.")
    tot = sum_counters(data.get("counters", {}))
    if tot:
        lines.append("")
        lines.append(f"CPU counters (whole process, summed over cases, via "
                     f"{data.get('counter_backend')}): "
                     f"{tot['instructions'] / 1e9:.2f} G instructions, "
                     f"{tot['cycles'] / 1e9:.2f} G cycles, IPC {ipc(tot):.2f}"
                     + (f", peak RSS {tot['max_rss'] / 1e6:.0f} MB" if "max_rss" in tot else ""))
    return "\n".join(lines) + "\n"


def emit_compare_md(base, target):
    """Markdown comparison of two runs (columns: target, baseline, target/baseline ratio)."""
    common = sorted(set(base["run_ms"]) & set(target["run_ms"]))
    dropped = (set(base["run_ms"]) | set(target["run_ms"])) - set(common)
    b_run = {k: base["run_ms"][k] for k in common}
    t_run = {k: target["run_ms"][k] for k in common}
    bt, bmean, bmed, bmax = summary_stats(b_run)
    tt, tmean, tmed, tmax = summary_stats(t_run)

    lines = []
    lines.append(f"### Optimizer runtime — {set_label(target)}, {len(common)} cases, "
                 f"target vs baseline (same runner)"
                 + (f", best of {target['repeat']}" if target["repeat"] > 1 else ""))
    lines.append("")
    lines.append("Δ = target / baseline; below 1× means the target is faster.")
    lines.append("")
    verdict = classify(base.get("counters", {}), target.get("counters", {}))
    if verdict:
        lines.append(verdict)
        lines.append("")
    lines.append("| | target | baseline | Δ |")
    lines.append("|---|---|---|---|")
    for label, t, b in (("total", tt, bt), ("mean", tmean, bmean),
                        ("median", tmed, bmed), ("max", tmax, bmax)):
        lines.append(f"| {label} | {fmt_ms(t)} | {fmt_ms(b)} | {fmt_ratio(t, b)} |")
    lines.append("")
    lines.append("<details><summary>Slowest cases (whole optimizer call, by target time)</summary>")
    lines.append("")
    lines.append("| case | target | baseline | Δ |")
    lines.append("|---|---|---|---|")
    for name, ms in sorted(t_run.items(), key=lambda kv: -kv[1])[:10]:
        lines.append(f"| {name} | {fmt_ms(ms)} | {fmt_ms(b_run[name])} "
                     f"| {fmt_ratio(ms, b_run[name])} |")
    lines.append("")
    lines.append("</details>")
    lines.append("")
    lines.append("Per-pass time, cumulative over all cases and fixpoint iterations:")
    lines.append("")
    lines.append("| pass | target | baseline | Δ |")
    lines.append("|---|---|---|---|")
    all_passes = {**base["pass_ms"], **target["pass_ms"]}
    for name in sorted(all_passes, key=lambda n: -target["pass_ms"].get(n, 0)):
        t, b = target["pass_ms"].get(name, 0), base["pass_ms"].get(name, 0)
        if t == 0 and b == 0:
            continue
        lines.append(f"| {name} | {fmt_ms(t)} | {fmt_ms(b)} | {fmt_ratio(t, b)} |")
    if dropped:
        lines.append("")
        lines.append(f"Cases present on only one side (not compared): "
                     f"{', '.join(sorted(dropped))}.")
    return "\n".join(lines) + "\n"


def emit_detail_compare_md(base, target):
    """The collapsed runtime-detail tables (slowest cases, then per-stage), main = baseline vs
    this branch = target, for embedding under the effectiveness table. Δ = this branch / main."""
    common = sorted(set(base["run_ms"]) & set(target["run_ms"]))
    b_run, t_run = base["run_ms"], target["run_ms"]
    lines = []
    verdict = classify(base.get("counters", {}), target.get("counters", {}))
    if verdict:
        lines += [verdict, ""]
    lines += ["<details><summary>Slowest cases (out of top 10)</summary>", "",
              "| case | main | this branch | Δ |", "|---|---|---|---|"]
    for name in sorted(common, key=lambda n: -t_run[n])[:10]:
        lines.append(f"| {name} | {fmt_ms(b_run[name])} | {fmt_ms(t_run[name])} "
                     f"| {fmt_ratio(t_run[name], b_run[name])} |")
    lines += ["", "</details>", "<details><summary>Per-stage runtime breakdown (out of top 10)</summary>", "",
              "| pass | main | this branch | Δ |", "|---|---|---|---|"]
    all_passes = {**base["pass_ms"], **target["pass_ms"]}
    for name in sorted(all_passes, key=lambda n: -target["pass_ms"].get(n, 0)):
        t, b = target["pass_ms"].get(name, 0), base["pass_ms"].get(name, 0)
        if t == 0 and b == 0:
            continue
        lines.append(f"| {name} | {fmt_ms(b)} | {fmt_ms(t)} | {fmt_ratio(t, b)} |")
    lines += ["", "</details>"]
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("benchmark", nargs="?", default=None,
                    help="benchmark set: a subdirectory of Benchmarks/<VM>/, or a <vm>:<set> "
                         "token naming both (e.g. sp1:rsp) -- a subdirectory of Benchmarks/<VM>/ "
                         "(default: openvm-eth for openvm, rsp for sp1)")
    ap.add_argument("--vm", choices=sorted(VM_DIR), default=None,
                    help="VM whose benchmark set and fact-aware optimizer to use "
                         "(default: openvm, or the VM named by a <vm>:<set> benchmark token)")
    ap.add_argument("--n", type=int, default=None, metavar="N",
                    help="only the top N cases by cost rank (default: all)")
    ap.add_argument("--repeat", type=int, default=1,
                    help="runs per case; the fastest is kept (default: 1)")
    ap.add_argument("--no-counters", action="store_true",
                    help="skip the CPU-counter run per case (perf / /usr/bin/time -l); counters "
                         "are used automatically when the platform provides them")
    ap.add_argument("--no-build", action="store_true",
                    help="skip `lake build` (the binary must already exist)")
    ap.add_argument("--binary", type=Path, default=None, metavar="EXE",
                    help="bench this apc-optimizer executable instead of building the repo's "
                         "(e.g. a prebuilt CI artifact); implies no build")
    ap.add_argument("--repo", type=Path, default=REPO, metavar="DIR",
                    help="repository to build and bench (default: the one holding this script; "
                         "lets a saved copy of the script bench another checkout, e.g. a baseline)")
    ap.add_argument("--md", type=Path, default=None, metavar="OUT.md",
                    help="also write a markdown summary (for CI job summaries / PR comments)")
    ap.add_argument("--json", type=Path, default=None, metavar="OUT.json",
                    help="also dump the raw per-case/per-pass results (input for --compare)")
    ap.add_argument("--compare", nargs=2, default=None, metavar=("BASE.json", "TARGET.json"),
                    help="don't bench; render a comparison of two --json dumps instead")
    ap.add_argument("--details", action="store_true",
                    help="with --compare, emit only the collapsed detail tables "
                         "(slowest cases + per-stage, main vs this branch)")
    args = ap.parse_args()

    if args.compare is not None:
        base, target = (json.loads(Path(p).read_text()) for p in args.compare)
        md = emit_detail_compare_md(base, target) if args.details else emit_compare_md(base, target)
    else:
        data = bench(args)
        if args.json is not None:
            args.json.write_text(json.dumps(data))
            print(f"wrote {args.json}", file=sys.stderr)
        md = emit_md(data)

    print()
    print(md)
    if args.md is not None:
        args.md.write_text(md)
        print(f"wrote {args.md}", file=sys.stderr)


if __name__ == "__main__":
    main()
