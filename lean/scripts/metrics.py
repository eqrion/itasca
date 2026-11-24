#!/usr/bin/env python3
"""Proof-health metrics for the itasca Lean tree. Needs no build.

  python3 scripts/metrics.py                 print metrics as JSON
  python3 scripts/metrics.py --write FILE    write metrics JSON to FILE
  python3 scripts/metrics.py --check FILE    fail if a ratcheted metric is worse than in FILE
  python3 scripts/metrics.py --top           print the most-unfolded extracted functions

Run from the `lean/` directory. See PROOF_ENGINEERING.md for what each metric means.
"""
import collections
import csv
import json
import os
import re
import statistics
import sys

from architecture import (layer_violations,
                          mask_comments_and_strings as _mask_comments_and_strings,
                          source_graph)

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
    "validator": ["Itasca/Binary", "Itasca/Handler", "Itasca/Visitor", "Itasca/Body",
                  "Itasca/CodeEntry", "Itasca/Module", "Itasca/Stream"],
}
# Metrics that must never get worse. Lower is better for all of them.
RATCHET = ["heartbeat_overrides", "recdepth_overrides", "theorems_with_15_or_more_binders",
           "extra_unfold_files", "bare_simp", "sorry", "layer_violations",
           "modules_under_50_lines"]

SHORT_MODULE_LEDGER = os.path.join("metrics", "short-module-ledger.json")
MIGRATION_MANIFEST = os.path.join("metrics", "interface-migration-manifest.tsv")
THEOREM = re.compile(r"^(?:private |protected )?(?:theorem|lemma) ([\w.«»']+)(.*?)(?::=|\n\s*\|)", re.M | re.S)
BINDER = re.compile(r"[({]\s*[\w\s']+:")
TOKEN = re.compile(r"[\w.«»]+")
TACTIC_LIST = re.compile(r"\b(?:simp_all|simpa|simp|rw|rewrite|dsimp)\b")
HEAD_NAME = re.compile(r"[\w.«»]+(?:\.[\w.«»]+)*")


# Import parsing and source masking live in architecture.py.


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


def short_module_exemptions(src, sizes, ledger_path=SHORT_MODULE_LEDGER,
                            manifest_path=MIGRATION_MANIFEST):
    """Load exact, justified structural exceptions to the short-module ratchet."""
    if not os.path.exists(ledger_path):
        return [], [f"missing structural short-module ledger: {ledger_path}"]
    try:
        with open(ledger_path) as ledger:
            data = json.load(ledger)
    except (OSError, json.JSONDecodeError) as error:
        return [], [f"invalid structural short-module ledger: {error}"]
    if not isinstance(data, list):
        return [], ["structural short-module ledger must be a JSON array"]
    manifest_paths = set()
    if os.path.exists(manifest_path):
        try:
            with open(manifest_path, newline="") as manifest_file:
                rows = csv.DictReader(manifest_file, delimiter="\t")
                if not {"source_module", "destination_module"}.issubset(rows.fieldnames or ()):
                    errors = ["migration manifest must include source_module and destination_module columns"]
                else:
                    errors = []
                    for row in rows:
                        for field in ("source_module", "destination_module", "current_source_module"):
                            module_name = row.get(field, "")
                            if module_name:
                                manifest_paths.add(module_name.replace(".", os.sep) + ".lean")
        except (OSError, csv.Error) as error:
            errors = [f"invalid interface migration manifest: {error}"]
    else:
        errors = []
    # Manifest provenance enforcement is staged until the migration manifest
    # is committed. An empty ledger needs no provenance; once entries exist,
    # every path must be enumerated in that manifest.
    paths, exemptions = set(), set()
    short_paths = {p for p, source in src.items() if source.count("\n") < 50}
    for entry in data:
        if (not isinstance(entry, dict) or set(entry) != {"path", "reason"}
                or not isinstance(entry.get("path"), str)
                or not isinstance(entry.get("reason"), str) or not entry["reason"].strip()):
            errors.append("each ledger entry must have exactly path and nonempty reason")
            continue
        path = entry["path"]
        if path in paths:
            errors.append(f"duplicate structural short-module ledger path: {path}")
        paths.add(path)
        eligible = True
        if path not in src:
            errors.append(f"structural short-module ledger path is not a handwritten module: {path}")
            eligible = False
        elif path not in short_paths:
            errors.append(f"structural short-module ledger path is not under 50 lines: {path}")
            eligible = False
        elif data and path not in manifest_paths:
            errors.append(f"structural short-module ledger path is absent from migration manifest: {path}")
            eligible = False
        if any(ch in path for ch in "*?[]"):
            errors.append(f"structural short-module ledger requires exact paths, not patterns: {path}")
            eligible = False
        if eligible:
            exemptions.add(path)
    return sorted(exemptions), errors


def ratchet_values(key, metrics, baseline):
    """Return baseline/current values, retaining compatibility with old baselines."""
    if key == "modules_under_50_lines":
        adjusted = "modules_under_50_lines_after_structural_exemptions"
        return baseline.get(adjusted, baseline.get(key)), metrics[adjusted]
    return baseline.get(key), metrics[key]


def interface_line_accounting(src, migrations):
    """Report relocated lines separately, retaining their original module/area."""
    # A semantic reading unit can contain several historical proof areas. Named
    # sections keep attribution exact without counting the whole merged file in
    # every area. Imports, overview text and section headings are shared overhead.
    section_rows = collections.defaultdict(lambda: collections.defaultdict(list))
    ordinary_rows = []
    for row in migrations:
        section = row.get("destination_section", "")
        if section:
            section_rows[row["destination_module"]][section].append(row)
        else:
            ordinary_rows.append(row)
    if section_rows:
        expanded = dict(src)
        for module, sections in section_rows.items():
            if any(row.get("destination_module") == module for row in ordinary_rows):
                raise ValueError(f"mixed whole-module and section origins: {module}")
            path = module.replace(".", os.sep) + ".lean"
            if path not in expanded:
                raise ValueError(f"missing sectioned Interface module: {module}")
            lines = expanded.pop(path).splitlines(keepends=True)
            covered = set()
            for section, rows in sections.items():
                starts = [i for i, line in enumerate(lines) if line.strip() == f"section {section}"]
                ends = [i for i, line in enumerate(lines) if line.strip() == f"end {section}"]
                if len(starts) != 1 or len(ends) != 1 or starts[0] >= ends[0]:
                    raise ValueError(f"invalid Interface section: {module}.{section}")
                span = set(range(starts[0], ends[0] + 1))
                if covered & span:
                    raise ValueError(f"overlapping Interface section: {module}.{section}")
                covered.update(span)
                virtual = module + "." + section
                expanded[virtual.replace(".", os.sep) + ".lean"] = "".join(lines[i] for i in sorted(span))
                ordinary_rows.extend(dict(row, destination_module=virtual, destination_section="") for row in rows)
            shared = module + ".SharedOverview"
            expanded[shared.replace(".", os.sep) + ".lean"] = "".join(line for i, line in enumerate(lines) if i not in covered)
            ordinary_rows.append({"source_module": "", "destination_module": shared})
        return interface_line_accounting(expanded, ordinary_rows)
    origins = collections.defaultdict(set)
    for row in migrations:
        destination = row.get("destination_module", "")
        if destination:
            origins[destination.replace(".", os.sep) + ".lean"].add(
                row.get("source_module") or "_entrypoints")
    def origin_areas(owner):
        old_path = owner.replace(".", os.sep) + ".lean"
        for previous, current in (("Wasm1", "Body"), ("Wasm2", "Body"),
                                  ("Profile", "CodeEntry")):
            old_path = old_path.replace(f"Itasca/{previous}/", f"Itasca/{current}/")
        return tuple(area for area, paths in LEAN_AREAS.items()
                     if any(old_path == prefix or old_path.startswith(prefix + os.sep)
                            for prefix in paths))

    def unmeasured_subject(owner):
        # Integration, Representation and SourceMachine have no Rust line-ratio
        # area. They can still consolidate definitions within their own subject.
        parts = owner.split(".")
        return tuple(parts[:3] if parts[:2] == ["Itasca", "Runtime"] else parts[:2])

    by_origin = collections.Counter()
    by_area = collections.Counter()
    for path, source in src.items():
        if not (path.startswith("Itasca/Results/Definitions/") or path == "Itasca/Results/Definitions.lean"):
            continue
        owners = origins.get(path, {"_unregistered"})
        areas = {origin_areas(owner) for owner in owners}
        # Explicit consolidation rows retain every historical source label.
        # Count their shared file once; cross-area attribution is ambiguous.
        if len(owners) > 1 and (len(areas) != 1 or
                (not next(iter(areas)) and
                 len({unmeasured_subject(owner) for owner in owners}) != 1)):
            raise ValueError(f"ambiguous Interface origin for {path}: {sorted(owners)}")
        label = " + ".join(sorted(owners))
        lines = source.count("\n")
        by_origin[label] += lines
        for area in next(iter(areas)):
            by_area[area] += lines
    return dict(sorted(by_origin.items())), dict(sorted(by_area.items()))


def compute():
    src, generated = {}, {}
    for p in lean_files():
        (generated if p.startswith(GENERATED) else src)[p] = open(p).read()
    imports = source_graph(".")

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
    with open(MIGRATION_MANIFEST, newline="") as migration_file:
        migration_rows = list(csv.DictReader(migration_file, delimiter="\t"))
    interface_origin, interface_area = interface_line_accounting(src, migration_rows)
    rust_area = {a: count_lines(ps, ".rs") for a, ps in RUST_AREAS.items()}
    violations = layer_violations(imports)
    exemptions, ledger_errors = short_module_exemptions(src, sizes)
    violations.extend(("metrics/short-module-ledger.json", "", error) for error in ledger_errors)
    metrics = {
        "modules": len(src),
        "handwritten_lines": sum(sizes),
        "median_module_lines": statistics.median(sizes),
        "modules_under_50_lines": sum(1 for n in sizes if n < 50),
        "modules_under_50_lines_after_structural_exemptions":
            sum(1 for n in sizes if n < 50) - len(exemptions),
        "structural_short_module_exemptions": exemptions,
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
        "interface_lines": sum(interface_origin.values()),
        "interface_lines_by_origin_module": interface_origin,
        "interface_lines_by_origin_area": interface_area,
        "lean_lines_by_area_with_interface_origin": {
            area: lines + interface_area.get(area, 0) for area, lines in lean_area.items()},
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
        worse = []
        for key in RATCHET:
            old, current = ratchet_values(key, metrics, baseline)
            if old is not None and current > old:
                worse.append((key, old, current))
        for k, old, new in worse:
            print(f"metric got worse: {k} was {old}, now {new}")
        better = []
        for key in RATCHET:
            old, current = ratchet_values(key, metrics, baseline)
            if old is not None and current < old:
                better.append(key)
        if better and not worse:
            print("improved: " + ", ".join(better) + f". Update the baseline with --write {args[1]}.")
        return 1 if worse else 0
    print(json.dumps(metrics, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
