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
TACTIC_LIST = re.compile(r"\b(?:simp_all|simpa|simp|rw|rewrite|dsimp)\b")
HEAD_NAME = re.compile(r"[\w.«»]+(?:\.[\w.«»]+)*")


def _mask_comments_and_strings(source):
    """Blank comments and literals while preserving offsets and newlines."""
    out = list(source)
    i = 0
    block_depth = 0
    while i < len(source):
        if block_depth:
            if source.startswith("/-", i):
                out[i:i + 2] = "  "
                block_depth += 1
                i += 2
            elif source.startswith("-/", i):
                out[i:i + 2] = "  "
                block_depth -= 1
                i += 2
            else:
                if source[i] != "\n":
                    out[i] = " "
                i += 1
            continue
        if source.startswith("--", i):
            while i < len(source) and source[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if source.startswith("/-", i):
            out[i:i + 2] = "  "
            block_depth = 1
            i += 2
            continue
        if source[i] == '"':
            out[i] = " "
            i += 1
            while i < len(source):
                if source[i] == "\\" and i + 1 < len(source):
                    if source[i + 1] != "\n":
                        out[i + 1] = " "
                    out[i] = " "
                    i += 2
                elif source[i] == '"':
                    out[i] = " "
                    i += 1
                    break
                else:
                    if source[i] != "\n":
                        out[i] = " "
                    i += 1
            continue
        # Mask Lean character literals but leave primed identifiers (x').
        if source[i] == "'" and i + 1 < len(source):
            end = i + 2 if source[i + 1] != "\\" else i + 3
            if end < len(source) and source[end] == "'":
                for j in range(i, end + 1):
                    if source[j] != "\n":
                        out[j] = " "
                i = end + 1
                continue
        i += 1
    return "".join(out)


def _matching_square(source, start):
    """Return the closing bracket for a list, respecting nested delimiters."""
    pairs = {"[": "]", "(": ")", "{": "}"}
    stack = []
    for i in range(start, len(source)):
        char = source[i]
        if char in pairs:
            stack.append(pairs[char])
        elif char in pairs.values():
            if not stack or stack[-1] != char:
                return None
            stack.pop()
            if not stack:
                return i
    return None


def _split_top_level(items):
    """Split comma-separated list items without splitting nested terms."""
    pairs = {"[": "]", "(": ")", "{": "}"}
    stack = []
    start = 0
    result = []
    for i, char in enumerate(items):
        if char in pairs:
            stack.append(pairs[char])
        elif char in pairs.values():
            if stack and stack[-1] == char:
                stack.pop()
        elif char == "," and not stack:
            result.append(items[start:i])
            start = i + 1
    result.append(items[start:])
    return result


def _skip_tactic_option(source, pos):
    """Skip supported parenthesized simp/dsimp configuration arguments."""
    if pos >= len(source) or source[pos] != "(":
        return pos
    close = _matching_square(source, pos)
    if close is None:
        return pos
    contents = source[pos + 1:close].lstrip()
    if re.match(r"(?:config|discharger)\s*:=", contents):
        return close + 1
    return pos


def _list_item_head(item):
    item = item.strip()
    # A negative simp modifier removes this rule; it is not a use of the def.
    if item.startswith("-"):
        return None
    while item[:1] in ("←", "→", "+"):
        item = item[1:].lstrip()
    # Parentheses can group a bare rewrite lemma; unwrap only a whole-item group.
    while item.startswith("(") and item.endswith(")"):
        close = _matching_square(item, 0)
        if close != len(item) - 1:
            break
        item = item[1:-1].strip()
        if item.startswith("-"):
            return None
        while item[:1] in ("←", "→", "+"):
            item = item[1:].lstrip()
    match = HEAD_NAME.match(item)
    return match.group(0) if match else None


def _is_delta_tactic(source, pos):
    """Accept delta only at a tactic boundary, not as a term identifier."""
    line_start = source.rfind("\n", 0, pos) + 1
    prefix = source[line_start:pos].strip()
    if not prefix:
        return True
    if prefix in ("by", "·", "all_goals", "try", "first |", "focus"):
        return True
    if re.fullmatch(r"case\s+[\w.«»]+\s*=>", prefix):
        return True
    if prefix.endswith("<;>") or prefix.endswith(";"):
        return True
    if prefix.endswith("first |") or prefix.endswith("all_goals") or prefix.endswith("try"):
        return True
    return False


def explicit_tactic_items(source):
    """Yield (tactic, heads) for actual explicit simp/rw lists and unfold lists.

    For bracket tactics, only each top-level item's head is a definition target;
    names in that item's arguments are not. `unfold` takes a whitespace list,
    so all identifiers before `at` are targets.
    """
    code = _mask_comments_and_strings(source)
    events = []
    for match in TACTIC_LIST.finditer(code):
        tactic = match.group(0)
        pos = match.end()
        while True:
            while pos < len(code) and code[pos].isspace():
                pos += 1
            after_option = _skip_tactic_option(code, pos)
            if after_option != pos:
                pos = after_option
                continue
            only = re.match(r"only\b", code[pos:])
            if only:
                pos += only.end()
                continue
            break
        if pos >= len(code) or code[pos] != "[":
            continue
        end = _matching_square(code, pos)
        if end is None:
            continue
        heads = tuple(head for item in _split_top_level(code[pos + 1:end])
                      if (head := _list_item_head(item)) is not None)
        events.append((match.start(), tactic, heads))
    for match in re.finditer(r"\b(?:unfold|delta)\b", code):
        line_start = code.rfind("\n", 0, match.start()) + 1
        keyword_column = match.start() - line_start
        line_end = code.find("\n", match.end())
        if line_end < 0:
            line_end = len(code)
        parts = [code[match.end():line_end]]
        cursor = line_end
        while cursor < len(code):
            next_start = cursor + 1
            next_end = code.find("\n", next_start)
            if next_end < 0:
                next_end = len(code)
            line = code[next_start:next_end]
            stripped = line.lstrip(" \t")
            indent = len(line) - len(stripped)
            if not stripped or indent <= keyword_column:
                break
            if re.match(r"(?:simp_all|simpa|simp|rw|rewrite|dsimp|unfold|delta|exact|apply|rfl|cases|split|constructor|intro|have|let|rcases|obtain|refine|omega|aesop|assumption|subst|change|try|first|all_goals)\b", stripped):
                break
            # Continuation lines may contain only additional names/modifiers;
            # this prevents an indented following tactic from joining the list.
            if not re.fullmatch(r"(?:[←→+\-]\s*)?[\w.«»]+(?:\.[\w.«»]+)*(?:\s*,?\s*(?:[←→+\-]\s*)?[\w.«»]+(?:\.[\w.«»]+)*)*\s*", stripped):
                break
            parts.append(stripped)
            cursor = next_end
        clause = " ".join(parts)
        clause = re.split(r"\bat\b|<;>|;", clause, maxsplit=1)[0].strip()
        name_list = re.compile(r"[\w.«»]+(?:\.[\w.«»]+)*(?:(?:\s*,\s*|\s+)[\w.«»]+(?:\.[\w.«»]+)*)*")
        heads = tuple(HEAD_NAME.findall(clause)) if name_list.fullmatch(clause) else ()
        if heads:
            events.append((match.start(), match.group(0), heads))
    for _, tactic, heads in sorted(events):
        yield tactic, heads


def extracted_definitions(funs):
    """Collect generated Lean definition names, including wrapped headers."""
    return set(re.findall(r"^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?def\s+([\w.«»]+)", funs, re.M))


def extracted_tactic_definitions(source, extracted):
    """Yield extracted definitions explicitly used as tactic-list heads."""
    for _, heads in explicit_tactic_items(source):
        for name in heads:
            name = name[len("Itasca."):] if name.startswith("Itasca.") else name
            if name in extracted:
                yield name


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


def import_path(imports, start, target):
    """Return a shortest import chain, or None when target is unreachable."""
    pending = collections.deque([start])
    previous = {start: None}
    while pending:
        current = pending.popleft()
        if current == target:
            path = []
            while current is not None:
                path.append(current)
                current = previous[current]
            return list(reversed(path))
        for dependency in imports.get(current, ()):
            if dependency not in previous:
                previous[dependency] = current
                pending.append(dependency)
    return None


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
            if lm == "Runtime" and ".Generated.Funs" in i and i not in {
                    "Itasca.Generated.FunsValidator", "Itasca.Generated.FunsRuntimeCommon",
                    "Itasca.Generated.FunsCompiler", "Itasca.Generated.FunsStore",
                    "Itasca.Generated.FunsInterp", "Itasca.Generated.FunsInstantiate"}:
                bad.append((m, i, "Runtime imports generated function partitions, not the umbrella or external models"))
            if m.startswith("Itasca.Runtime.Compiler.") and i.startswith("Itasca.Runtime.Compiler."):
                s, t = m.split(".")[3], i.split(".")[3]
                if (s == "Local" and t in ("Body", "Module")) or (s == "Body" and t == "Module"):
                    bad.append((m, i, "Compiler stages are Local -> Body -> Module"))
    protected = ("Itasca.Binary.", "Itasca.Handler.", "Itasca.Visitor.",
                 "Itasca.Wasm2.", "Itasca.Profile.", "Itasca.Module.",
                 "Itasca.Stream.", "Itasca.Runtime.Compiler.")
    for module in imports:
        if any(module == prefix[:-1] or module.startswith(prefix) for prefix in protected):
            path = import_path(imports, module, "Itasca.Generated.FunsInterp")
            if path:
                bad.append((module, path[-1],
                            "validator/compiler must not transitively import interpreter functions: "
                            + " -> ".join(path)))
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

    funs = "\n".join(text for path, text in generated.items()
                     if re.fullmatch(r"Funs(?:Validator|RuntimeCommon|Compiler|Store|Interp|Instantiate)?\.lean",
                                     os.path.basename(path)))
    extracted = extracted_definitions(funs)
    unfold_files = collections.defaultdict(set)
    for p, s in src.items():
        for t in extracted_tactic_definitions(s, extracted):
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
