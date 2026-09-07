#!/usr/bin/env python3
"""Emit a powdr APC dump as a Lean `Circuit babyBear` literal.

Usage: emit-apc-lean.py [--namespace NS] <name> <dump.json> [<name> <dump.json> ...] > Out.lean

Writes one `Stages.lean` for `ApcOptimizer/VmSpec/Audit/Apcs/<Apc>/`, whose namespace
`--namespace` names (default `ApcOptimizer.OpenVM`; the audited APCs use
`ApcOptimizer.OpenVM.<Apc>` and call the stages `unopt`, `opt`, `gated`). Run powdr's
APC-builder tests with `APC_EXPORT_PATH=<dir> APC_EXPORT_LEVEL=3` to get every stage.

The dumps are the `APC_EXPORT_PATH` JSON files powdr writes; the same format
`ApcOptimizer/Implementation/JsonParser.lean` reads at runtime.
"""
import json
import sys

P = 2013265921


def var(raw: str) -> str:
    base, _, pid = raw.partition("@")
    if pid.isdigit():
        return '⟨"%s", some %s⟩' % (base, pid)
    return '⟨"%s", none⟩' % raw


def expr(e) -> str:
    if isinstance(e, int):
        return ".const %d" % (e % P)
    if isinstance(e, str):
        return ".var %s" % var(e)
    if isinstance(e, list) and len(e) == 2 and e[0] == "-":
        return ".mul (.const %d) (%s)" % (P - 1, expr(e[1]))
    a, op, b = e
    if op == "+":
        return ".add (%s) (%s)" % (expr(a), expr(b))
    if op == "-":
        return ".add (%s) (.mul (.const %d) (%s))" % (expr(a), P - 1, expr(b))
    if op == "*":
        return ".mul (%s) (%s)" % (expr(a), expr(b))
    raise ValueError("unknown operator %r" % op)


def emit(name: str, path: str) -> None:
    dump = json.load(open(path))
    # Intermediate-stage dumps are the bare machine; `_000_unopt` and the final
    # one wrap it alongside `block`/`bus_map` (see `apc-dumps/README.md`).
    machine = dump.get("machine", dump)
    src = path.rsplit("/", 1)[-1]
    print("/-- `%s`, emitted verbatim from `%s`" % (name, src))
    print("    by `Scripts/emit-apc-lean.py`: %d algebraic constraints, %d bus interactions. -/"
          % (len(machine["constraints"]), len(machine["bus_interactions"])))
    print("def %s : Circuit babyBear where" % name)
    print("  algebraicConstraints :=")
    print("    [ " + "\n    , ".join(expr(c) for c in machine["constraints"]) + " ]")
    print("  busInteractions :=")
    rows = []
    for bi in machine["bus_interactions"]:
        args = "[" + ", ".join(expr(a) for a in bi["args"]) + "]"
        rows.append("{ busId := %d, multiplicity := %s,\n        payload := %s }"
                    % (bi["id"], expr(bi["mult"]), args))
    print("    [ " + "\n    , ".join(rows) + " ]")
    print()


def emit_asg(name: str, path: str) -> None:
    """Emit a `ChipAssignment babyBear` as a match on the powdr variable id."""
    asg = json.load(open(path))
    rows = sorted((int(k.split("@")[1]), k.split("@")[0], v % P)
                  for k, v in asg.items() if v % P != 0)
    print("/-- A concrete assignment, keyed by powdr variable id; every id not listed takes `0`. -/")
    print("def %s : ChipAssignment babyBear := fun v =>" % name)
    print("  match v.powdrId? with")
    for pid, nm, val in rows:
        print("  | some %-4d => %-12d -- %s" % (pid, val, nm))
    print("  | _ => 0")
    print()


def main() -> None:
    args = sys.argv[1:]
    ns = "ApcOptimizer.OpenVM"
    if args[:1] == ["--namespace"]:
        ns, args = args[1], args[2:]
    if len(args) < 2 or len(args) % 2:
        sys.exit(__doc__)
    print("import ApcOptimizer.VmSpec.OpenVm")
    print()
    print("set_option autoImplicit false")
    print("set_option maxHeartbeats 1000000")
    print()
    print("/-! One APC at several points of powdr's pipeline, emitted from the stage dumps --")
    print("    see `Audit/Legality/All.lean`. -/")
    print()
    print("namespace %s" % ns)
    print()
    for i in range(0, len(args), 2):
        if args[i].startswith("asg:"):
            emit_asg(args[i][4:], args[i + 1])
        else:
            emit(args[i], args[i + 1])
    print("end %s" % ns)


main()
