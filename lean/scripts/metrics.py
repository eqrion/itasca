#!/usr/bin/env python3
"""Proof-health metrics for the itasca Lean tree. Needs no build.

  python3 scripts/metrics.py                 print metrics as JSON
  python3 scripts/metrics.py --write FILE    write metrics JSON to FILE
  python3 scripts/metrics.py --check FILE    fail if a ratcheted metric is worse than in FILE
  python3 scripts/metrics.py --top           print the most-unfolded extracted functions

Run from the `lean/` directory. See PROOF_ENGINEERING.md for what each metric means.
"""
import collections
import json
import os
import re
import statistics
import sys

ROOTS = ("Itasca", "SpecExt")
GENERATED = os.path.join("Itasca", "Generated")
RUST_AREAS = {
    "compiler": ["../src/runtime/compiler"],
    "interp": ["../src/runtime/interp"],
    "store": ["../src/runtime/store.rs", "../src/runtime/store"],
    "validator": ["../src/code.rs", "../src/module.rs", "../src/stream.rs", "../src/reader.rs",
                  "../src/signature.rs", "../src/types.rs", "../src/limits.rs", "../src/error.rs"],
}
LEAN_AREAS = {
    "compiler": ["Itasca/Runtime/Compiler"],
    "interp": ["Itasca/Runtime/Interp"],
    "store": ["Itasca/Runtime/Store"],
    "validator": ["Itasca/Binary", "Itasca/Handler", "Itasca/Visitor", "Itasca/Wasm1", "Itasca/Wasm2",
                  "Itasca/Profile", "Itasca/Module", "Itasca/Stream", "Itasca/Contracts.lean"],
}
# Metrics that must never get worse. Lower is better for all of them.
RATCHET = ["heartbeat_overrides", "recdepth_overrides", "theorems_with_15_or_more_binders",
           "extra_unfold_files", "bare_simp", "sorry", "layer_violations", "modules_under_50_lines"]

IMPORT = re.compile(r"^(?:public )?import (?:all )?([\w.«»]+)", re.M)
THEOREM = re.compile(r"^(?:private |protected )?(?:theorem|lemma) ([\w.«»']+)(.*?)(?::=|\n\s*\|)", re.M | re.S)
BINDER = re.compile(r"[({]\s*[\w\s']+:")
TOKEN = re.compile(r"[\w.«»]+")
UNFOLD_SITE = re.compile(r"\bunfold ([^\n]*)|\b(?:simp|simp only|simpa|simpa only|rw|rewrite|delta|simp_all|dsimp|dsimp only)\s*\[([^\]]*)\]")


def lean_files():
    for top in ROOTS:
        for d, _, fs in os.walk(top):
            for f in fs:
                if f.endswith(".lean"):
                    yield os.path.join(d, f)


def count_lines(paths, suffix):
    total = 0
    for p in paths:
        if os.path.isfile(p):
            total += open(p).read().count("\n")
        for d, _, fs in os.walk(p):
            for f in fs:
                if f.endswith(suffix):
                    total += open(os.path.join(d, f)).read().count("\n")
    return total


def layer_violations(imports):
    """The import rules documented in lean/README.md. Returns a list of (module, import, rule)."""
    def layer(m):
        p = m.split(".")
        return p[1] if p[0] == "Itasca" and len(p) > 1 else p[0]
    bad = []
    for m, ims in imports.items():
        lm = layer(m)
        for i in ims:
            li = layer(i)
            if not (i.startswith("Itasca") or i.startswith("SpecExt")):
                continue
            if lm not in ("Runtime", "Main", "Results", "Examples", "Itasca", "SpecExt") and li in ("Runtime", "SpecExt"):
                bad.append((m, i, "validator proofs must not import Runtime or SpecExt"))
            if lm in ("Support", "Spec", "Binary") and li not in ("Generated", "Support", "Spec", "Binary"):
                bad.append((m, i, "Support/Spec/Binary import only the foundation"))
            if lm == "Handler" and li not in ("Generated", "Support", "Spec", "Binary", "Handler", "Visitor"):
                bad.append((m, i, "Handler adds only Visitor"))
            if li in ("Results", "Main") and lm not in ("Main", "Examples", "Itasca", "Results"):
                bad.append((m, i, "only Main and Examples import Results"))
            if lm == "Runtime" and ".Generated.Funs" in i and m != "Itasca.Runtime.Equations":
                bad.append((m, i, "Runtime reaches generated functions only through Runtime.Equations"))
            if m.startswith("Itasca.Runtime.Compiler.") and i.startswith("Itasca.Runtime.Compiler."):
                s, t = m.split(".")[3], i.split(".")[3]
                if (s == "Local" and t in ("Body", "Module")) or (s == "Body" and t == "Module"):
                    bad.append((m, i, "Compiler stages are Local -> Body -> Module"))
    return bad


def compute():
    src, generated = {}, {}
    for p in lean_files():
        (generated if p.startswith(GENERATED) else src)[p] = open(p).read()
    module = lambda p: p[:-5].replace(os.sep, ".")
    all_modules = {module(p) for p in list(src) + list(generated)}
    imports = {module(p): [i for i in IMPORT.findall(s) if i in all_modules]
               for p, s in list(src.items()) + list(generated.items())}

    sizes = sorted(s.count("\n") for s in src.values())
    text = "\n".join(src.values())
    binders = [len(BINDER.findall(m.group(2))) for s in src.values() for m in THEOREM.finditer(s)]

    funs = generated.get(os.path.join(GENERATED, "Funs.lean"), "")
    extracted = set(re.findall(r"^(?:@\[[^\]]*\]\s*)*(?:noncomputable )?def ([\w.«»]+)", funs, re.M))
    unfold_files = collections.defaultdict(set)
    for p, s in src.items():
        for m in UNFOLD_SITE.finditer(s):
            for t in TOKEN.findall(m.group(1) or m.group(2) or ""):
                t = t[len("Itasca."):] if t.startswith("Itasca.") else t
                if t in extracted:
                    unfold_files[t].add(p)

    depth = {}
    sys.setrecursionlimit(100000)
    def import_depth(m):
        if m not in depth:
            depth[m] = 1 + max((import_depth(i) for i in imports[m]), default=0)
        return depth[m]

    lean_area = {a: count_lines(ps, ".lean") for a, ps in LEAN_AREAS.items()}
    rust_area = {a: count_lines(ps, ".rs") for a, ps in RUST_AREAS.items()}
    violations = layer_violations(imports)
    metrics = {
        "modules": len(src),
        "handwritten_lines": sum(sizes),
        "median_module_lines": statistics.median(sizes),
        "modules_under_50_lines": sum(1 for n in sizes if n < 50),
        "modules_over_1500_lines": sum(1 for n in sizes if n > 1500),
        "max_import_depth": max(import_depth(m) for m in imports),
        "theorems": len(binders),
        "theorems_with_15_or_more_binders": sum(1 for b in binders if b >= 15),
        "max_theorem_binders": max(binders, default=0),
        "heartbeat_overrides": len(re.findall(r"set_option (?:synthInstance\.)?maxHeartbeats", text)),
        "recdepth_overrides": len(re.findall(r"set_option maxRecDepth", text)),
        "bare_simp": len(re.findall(r"\bsimp(?:_all)?\b(?! only)(?!a)", text)),
        "all_goals": len(re.findall(r"\ball_goals\b", text)),
        "sorry": len(re.findall(r"\bsorry\b", text)),
        "extracted_functions_unfolded": len(unfold_files),
        "extracted_functions_unfolded_in_3_or_more_files": sum(1 for fs in unfold_files.values() if len(fs) >= 3),
        "extra_unfold_files": sum(len(fs) - 1 for fs in unfold_files.values()),
        "max_unfold_files": max((len(fs) for fs in unfold_files.values()), default=0),
        "layer_violations": len(violations),
        "lean_lines_per_rust_line": {a: round(lean_area[a] / rust_area[a], 1) for a in LEAN_AREAS if rust_area[a]},
        "lean_lines_by_area": lean_area,
        "rust_lines_by_area": rust_area,
    }
    return metrics, unfold_files, violations


def main():
    metrics, unfold_files, violations = compute()
    args = sys.argv[1:]
    if args[:1] == ["--top"]:
        for name, files in sorted(unfold_files.items(), key=lambda kv: -len(kv[1]))[:40]:
            print(f"{len(files):4d} files  {name}")
        return 0
    if args[:1] == ["--violations"]:
        for m, i, rule in violations:
            print(f"{m} imports {i}: {rule}")
        return 1 if violations else 0
    if args[:1] == ["--write"]:
        with open(args[1], "w") as out:
            json.dump(metrics, out, indent=2, sort_keys=True)
            out.write("\n")
        return 0
    if args[:1] == ["--check"]:
        baseline = json.load(open(args[1]))
        worse = [(k, baseline[k], metrics[k]) for k in RATCHET if k in baseline and metrics[k] > baseline[k]]
        for k, old, new in worse:
            print(f"metric got worse: {k} was {old}, now {new}")
        better = [k for k in RATCHET if k in baseline and metrics[k] < baseline[k]]
        if better and not worse:
            print("improved: " + ", ".join(better) + f". Update the baseline with --write {args[1]}.")
        return 1 if worse else 0
    print(json.dumps(metrics, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
