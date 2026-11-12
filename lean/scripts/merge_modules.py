#!/usr/bin/env python3
"""Consolidate small Lean modules without lengthening the build's critical path.

  python3 scripts/merge_modules.py plan [--cap LINES] > merge-plan.json
  python3 scripts/merge_modules.py apply merge-plan.json --dir Itasca/Runtime/Spec
  python3 scripts/merge_modules.py apply merge-plan.json --group Itasca.Runtime.Spec.Counted

Run from the `lean/` directory.

`plan` groups modules that live in the same directory. A module joins a group only if the result
stays under the line cap, creates no import cycle, shares no `private` declaration name with the
group, and does not lengthen the estimated critical path of the build. Each group is named after
its last member in import order, so the merged file keeps an existing path.

`apply` rewrites one directory or one group: it concatenates the members in import order, each in
its own `section`, unions their imports, deletes the other member files, and rewrites every
`import` of a deleted module across the tree. It never touches generated files, `Results/`,
`Examples/`, `Main`, the contract files, or `Runtime/Equations`.
"""
import collections
import json
import os
import re
import sys

ROOTS = ("Itasca", "SpecExt")
IMPORT = re.compile(r"^(?:public )?import (?:all )?([\w.«»]+)[ \t]*$", re.M)
PRIVATE = re.compile(r"^\s*private\s+(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|structure|inductive)\s+([\w.«»']+)", re.M)
FROZEN_EXACT = {"Itasca", "Itasca.Main", "Itasca.Contracts", "Itasca.Runtime.Contracts", "Itasca.Runtime.Equations"}
# Measured elaboration seconds for the two modules that dominate the start of the build.
FIXED_COST = {"Itasca.Generated.Funs": 108.0, "Itasca.Runtime.Equations": 55.0}


def frozen(module):
    return (".Generated." in module or module.startswith("Itasca.Examples") or
            module.startswith("Itasca.Results") or module in FROZEN_EXACT)


def load():
    paths = {}
    for top in ROOTS:
        for d, _, fs in os.walk(top):
            for f in fs:
                if f.endswith(".lean"):
                    p = os.path.join(d, f)
                    paths[p[:-5].replace(os.sep, ".")] = p
    if os.path.exists("Itasca.lean"):
        paths["Itasca"] = "Itasca.lean"
    src = {m: open(p).read() for m, p in paths.items()}
    imports = {m: [i for i in IMPORT.findall(s) if i in paths] for m, s in src.items()}
    return paths, src, imports


def topological(paths, imports):
    order, seen = [], set()
    sys.setrecursionlimit(100000)
    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for i in sorted(imports[m]):
            visit(i)
        order.append(m)
    for m in sorted(paths):
        visit(m)
    return order


def plan(cap):
    paths, src, imports = load()
    lines = {m: s.count("\n") for m, s in src.items()}
    privates = {m: set(PRIVATE.findall(s)) for m, s in src.items()}
    order = topological(paths, imports)
    group = {m: m for m in paths}
    members = {m: [m] for m in paths}
    size = dict(lines)
    graph = {m: set(imports[m]) for m in paths}

    def cost(g, sizes):
        return FIXED_COST.get(g, 2.5 + 1.2 * sizes[g] / 100.0)

    def critical_path(g, sizes):
        memo = {}
        def walk(x):
            if x not in memo:
                memo[x] = cost(x, sizes) + max((walk(y) for y in g[x]), default=0.0)
            return memo[x]
        return max(walk(x) for x in g)

    def contract(g, sizes, keep, drop):
        g2 = {k: set(v) for k, v in g.items()}
        g2[keep] |= g2.pop(drop)
        g2[keep] -= {keep, drop}
        for k, v in g2.items():
            if drop in v:
                v.discard(drop)
                if k != keep:
                    v.add(keep)
        s2 = dict(sizes)
        s2[keep] += s2.pop(drop)
        return g2, s2

    def cyclic(g, start):
        stack, seen = list(g[start]), set()
        while stack:
            x = stack.pop()
            if x == start:
                return True
            if x not in seen:
                seen.add(x)
                stack.extend(g[x])
        return False

    best = critical_path(graph, size)
    by_dir = collections.defaultdict(list)
    for m in order:
        if not frozen(m):
            by_dir[os.path.dirname(paths[m])].append(m)
    for d in sorted(by_dir):
        chunks = []
        for m in by_dir[d]:
            placed = False
            for cur in chunks[::-1][:4]:
                if size[cur] + lines[m] > cap:
                    continue
                if privates[m] & set().union(*(privates[x] for x in members[cur])):
                    continue
                g2, s2 = contract(graph, size, cur, group[m])
                if cyclic(g2, cur):
                    continue
                path = critical_path(g2, s2)
                if path > best + 1e-9:
                    continue
                best = path
                old = group[m]
                for x in members[old]:
                    group[x] = cur
                members[cur] += members.pop(old)
                graph, size = g2, s2
                placed = True
                break
            if not placed:
                chunks.append(group[m])
    position = {m: i for i, m in enumerate(order)}
    groups = []
    for ms in members.values():
        if len(ms) > 1:
            ms = sorted(ms, key=position.get)
            groups.append({"target": ms[-1], "members": ms, "lines": sum(lines[x] for x in ms)})
    groups.sort(key=lambda g: g["target"])
    merged = sum(len(g["members"]) - 1 for g in groups)
    return {"cap": cap, "modules_before": len(paths), "modules_after": len(paths) - merged,
            "estimated_critical_path_seconds": round(best, 1), "groups": groups}


def split_imports(text):
    """Return (import lines, rest of file). Imports are the leading import/blank lines."""
    lines = text.split("\n")
    i = 0
    while i < len(lines) and (lines[i].strip() == "" or IMPORT.match(lines[i])):
        i += 1
    return [l for l in lines[:i] if l.strip()], "\n".join(lines[i:])


def apply(plan_file, only_dir=None, only_group=None):
    paths, src, _ = load()
    groups = json.load(open(plan_file))["groups"]
    chosen = []
    for g in groups:
        target_path = paths.get(g["target"])
        if target_path is None or any(m not in paths for m in g["members"]):
            continue  # already applied or the tree changed
        if only_group and g["target"] != only_group:
            continue
        if only_dir and os.path.dirname(target_path) != only_dir.rstrip("/"):
            continue
        chosen.append(g)
    if not chosen:
        print("nothing to apply")
        return 1
    rename = {m: g["target"] for g in chosen for m in g["members"]}
    for g in chosen:
        inside = set(g["members"])
        imports, sections = [], []
        for m in g["members"]:
            lines, body = split_imports(src[m])
            for line in lines:
                name = IMPORT.match(line).group(1)
                if name in inside:
                    continue
                line = f"import {rename.get(name, name)}"
                if line not in imports:
                    imports.append(line)
            sections.append(f"/-! ## {m.split('.')[-1]} -/\n\nsection\n\n{body.strip()}\n\nend\n")
        names = ", ".join(m.split(".")[-1] for m in g["members"])
        header = f"/-!\nSections, each formerly its own module: {names}.\n-/\n"
        with open(paths[g["target"]], "w") as out:
            out.write("\n".join(imports) + "\n\n" + header + "\n" + "\n".join(sections))
        for m in g["members"][:-1]:
            os.remove(paths[m])
        print(f"merged {len(g['members'])} modules into {g['target']}")
    merged_targets = {g["target"] for g in chosen}
    for m, p in paths.items():
        if m in rename and m not in merged_targets:
            continue  # deleted
        if m in merged_targets:
            continue  # already written with rewritten imports
        text = src[m]
        lines, body = split_imports(text)
        new, changed = [], False
        for line in lines:
            name = IMPORT.match(line).group(1)
            if name in rename and rename[name] != name:
                line, changed = line.replace(name, rename[name]), True
            if line not in new:
                new.append(line)
            else:
                changed = True
        if changed:
            with open(p, "w") as out:
                out.write("\n".join(new) + "\n" + ("\n" if not body.startswith("\n") else "") + body)
    return 0


def main():
    args = sys.argv[1:]
    if args[:1] == ["plan"]:
        cap = int(args[args.index("--cap") + 1]) if "--cap" in args else 1000
        json.dump(plan(cap), sys.stdout, indent=1)
        sys.stdout.write("\n")
        return 0
    if args[:1] == ["apply"]:
        only_dir = args[args.index("--dir") + 1] if "--dir" in args else None
        only_group = args[args.index("--group") + 1] if "--group" in args else None
        if not (only_dir or only_group):
            print("apply needs --dir DIRECTORY or --group TARGET_MODULE")
            return 2
        return apply(args[1], only_dir, only_group)
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main())
