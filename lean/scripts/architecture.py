#!/usr/bin/env python3
"""Lean import graph and architecture policy checks. Needs no build.

Run from the ``lean/`` directory with ``python3 scripts/architecture.py``.
"""
import argparse
import collections
import os
import re

GENERATED_PARTITIONS = {
    "Itasca.Generated.FunsValidator", "Itasca.Generated.FunsRuntimeCommon",
    "Itasca.Generated.FunsCompiler", "Itasca.Generated.FunsStore",
    "Itasca.Generated.FunsInterp", "Itasca.Generated.FunsInstantiate",
}
VALIDATOR_FORBIDDEN_PARTITIONS = GENERATED_PARTITIONS - {"Itasca.Generated.FunsValidator"}
VALIDATOR_MODULE_PREFIXES = tuple("Itasca." + name for name in (
    "Binary", "Handler", "Visitor", "Body", "CodeEntry", "Module", "Stream"))
VALIDATOR_DEFINITION_MODULES = {
    "Itasca.Results.Definitions.Foundations", "Itasca.Results.Definitions.Binary",
    "Itasca.Results.Definitions.Visitor", "Itasca.Results.Definitions.Observations",
    "Itasca.Results.Definitions.Validation", "Itasca.Results.Definitions.Streaming",
}
DEFINITION_FOUNDATION_PREFIXES = (
    "Itasca.Results.Definitions", "Itasca.Generated", "Itasca.SpecTecGenerated",
    "Itasca.SpecTecSupport", "SpecExt", "SpecTec", "SpecTecGenerated",
    "SpecTecSupport", "Lean", "Aeneas", "Mathlib", "ExtendedDeriveDecEq",
)


def mask_comments_and_strings(source):
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
        if source[i] == "«":
            end = source.find("»", i + 1)
            i = len(source) if end < 0 else end + 1
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
                    out[i:i + 2] = "  "
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
        if (source[i] == "'" and i + 1 < len(source)
                and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'»"))):
            end = i + 2 if source[i + 1] != "\\" else i + 3
            if end < len(source) and source[end] == "'":
                for j in range(i, end + 1):
                    if source[j] != "\n":
                        out[j] = " "
                i = end + 1
                continue
        i += 1
    return "".join(out)


# Lean 4.31 header modifiers: optional public, optional meta, import, optional all.
IMPORT_HEAD = re.compile(r"^[ \t]*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?", re.M)
COMPONENT = r"(?:«[^»]+»|[\w']+)"
MODULE_NAME = re.compile(COMPONENT + r"(?:\." + COMPONENT + r")*")
COMPONENT_NAME = re.compile(COMPONENT)


def quoted_component(component):
    return component if re.fullmatch(r"[\w']+", component) else '«' + component + '»'


def canonical_module(name):
    components = COMPONENT_NAME.findall(name)
    return '.'.join(quoted_component(part[1:-1] if part.startswith('«') else part)
                    for part in components)


def parse_imports(source):
    """Read header imports, including modifiers, quoted identifiers and whitespace.

    Extra module tokens on one line are included conservatively. Comments and
    literals cannot introduce edges; equivalent quoted names share a graph key.
    """
    code = mask_comments_and_strings(source)
    imports = []
    for head in IMPORT_HEAD.finditer(code):
        position = head.end()
        while match := MODULE_NAME.match(code, position):
            imports.append(canonical_module(match.group()))
            position = match.end()
            while position < len(code) and code[position] in ' \t':
                position += 1
    return imports


def lean_files(root="."):
    for top in ("Itasca", "SpecExt"):
        base = os.path.join(root, top)
        for directory, _, files in os.walk(base):
            for filename in files:
                if filename.endswith(".lean"):
                    yield os.path.join(directory, filename)


def module_name(path, root="."):
    return ".".join(quoted_component(part) for part in
                    os.path.relpath(path, root)[:-5].split(os.sep))


def source_graph(root="."):
    """Build the graph from Lean source only; no proof-health scans are done."""
    sources = {}
    for path in lean_files(root):
        with open(path) as source_file:
            sources[module_name(path, root)] = source_file.read()
    return {module: [name for name in parse_imports(source) if name in sources]
            for module, source in sources.items()}



def missing_project_imports(root="."):
    """Reject deleted owners even when an obsolete cached olean still exists."""
    errors = []
    for path in lean_files(root):
        with open(path) as stream:
            imports = parse_imports(stream.read())
        for name in imports:
            parts = COMPONENT_NAME.findall(name)
            if parts[0] not in ("Itasca", "SpecExt"):
                continue
            components = [part[1:-1] if part.startswith("«") else part for part in parts]
            target = os.path.join(root, *components) + ".lean"
            if not os.path.isfile(target):
                errors.append(f"{module_name(path, root)} imports missing source module {name}")
    return errors


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
    """Return (module, import, rule) violations for the established layer policy."""
    def layer(m):
        if m == "Itasca.Results.Definitions" or m.startswith("Itasca.Results.Definitions."):
            return "Definitions"
        p = m.split(".")
        return p[1] if p[0] == "Itasca" and len(p) > 1 else p[0]
    bad = []
    reachability = {}

    def path_from(start, target):
        if start not in reachability:
            pending = collections.deque([start])
            previous = {start: None}
            while pending:
                current = pending.popleft()
                for dependency in imports.get(current, ()):
                    if dependency not in previous:
                        previous[dependency] = current
                        pending.append(dependency)
            paths = {}
            for node in previous:
                chain, current = [], node
                while current is not None:
                    chain.append(current)
                    current = previous[current]
                paths[node] = list(reversed(chain))
            reachability[start] = paths
        return reachability[start].get(target)

    def narrow_definition(module):
        return module.startswith("Itasca.Results.Definitions.")

    def compiler_stage(module):
        for prefix in ("Itasca.Runtime.Compiler.",
                       "Itasca.Results.Definitions.Compiler."):
            if module.startswith(prefix):
                return module[len(prefix):].split(".")[0]
        return None

    for m, ims in imports.items():
        lm = layer(m)
        for i in ims:
            li = layer(i)
            if not (i.startswith("Itasca") or i.startswith("SpecExt")):
                continue
            if lm not in ("Runtime", "Main", "Results", "Examples", "Itasca", "SpecExt", "Definitions") and li in ("Runtime", "SpecExt"):
                bad.append((m, i, "validator proofs must not import Runtime or SpecExt"))
            if lm in ("Support", "Spec", "Binary") and li not in ("Generated", "Support", "Spec", "Binary") and not narrow_definition(i):
                bad.append((m, i, "Support/Spec/Binary import only the foundation"))
            if lm == "Handler" and li not in ("Generated", "Support", "Spec", "Binary", "Handler", "Visitor") and not narrow_definition(i):
                bad.append((m, i, "Handler adds only Visitor"))
            if li in ("Results", "Main") and lm not in ("Main", "Examples", "Itasca", "Results"):
                bad.append((m, i, "only Main and Examples import public theorem modules"))
            if lm == "Runtime" and i.startswith("Itasca.Generated.Funs") and i not in GENERATED_PARTITIONS:
                bad.append((m, i, "Runtime imports generated function partitions, not the umbrella or external models"))
            if compiler_stage(m) and compiler_stage(i):
                s, t = compiler_stage(m), compiler_stage(i)
                if (s == "Local" and t in ("Body", "Module")) or (s == "Body" and t == "Module"):
                    bad.append((m, i, "Compiler stages are Local -> Body -> Module"))
    protected = ("Itasca.Binary.", "Itasca.Handler.", "Itasca.Visitor.",
                 "Itasca.Body.", "Itasca.CodeEntry.", "Itasca.Module.",
                 "Itasca.Stream.", "Itasca.Runtime.Compiler.",
                 "Itasca.Results.Definitions.Compiler.")
    for module in imports:
        if any(module == prefix[:-1] or module.startswith(prefix) for prefix in protected):
            path = path_from(module, "Itasca.Generated.FunsInterp")
            if path:
                bad.append((module, path[-1],
                            "validator/compiler must not transitively import interpreter functions: "
                            + " -> ".join(path)))
    for module in imports:
        umbrella_path = path_from(module, "Itasca.Generated.Funs")
        if umbrella_path and module != "Itasca.Generated.Funs":
            bad.append((module, umbrella_path[-1],
                        "use narrow generated function partitions, not the Funs umbrella"))
        if module != "Itasca.Results.Definitions" and not module.startswith("Itasca.Results.Definitions."):
            continue
        for dependency in imports:
            if any(dependency == prefix or dependency.startswith(prefix + ".")
                   for prefix in DEFINITION_FOUNDATION_PREFIXES):
                continue
            path = path_from(module, dependency)
            if path:
                bad.append((module, dependency,
                            "Definition transitive import is outside public definitions and approved foundations: "
                            + " -> ".join(path)))
    for module in imports:
        if module == "Itasca.Results.Definitions" or not module.startswith("Itasca."):
            continue
        if module.startswith(("Itasca.Main", "Itasca.Examples")):
            continue
        path = path_from(module, "Itasca.Results.Definitions")
        if path:
            bad.append((module, path[-1], "only Main and Examples may import the definitions umbrella"))
    def theorem_module(module):
        return module.startswith("Itasca.Results.") and not (
            module == "Itasca.Results.Definitions" or module.startswith("Itasca.Results.Definitions."))

    for module in imports:
        is_result = theorem_module(module)
        for dependency in imports:
            if not (theorem_module(dependency) or dependency == "Itasca.Main"):
                continue
            path = path_from(module, dependency)
            if not path:
                continue
            if module.startswith("Itasca.") and not (theorem_module(module) or
                    module.startswith(("Itasca.Main", "Itasca.Examples"))):
                bad.append((module, path[-1], "Definitions and implementation modules must not import theorem modules or Main"))
            elif is_result and dependency != module:
                bad.append((module, path[-1], "Theorem modules must not import another theorem module"))
    validator_roots = [m for m in imports if m.startswith(VALIDATOR_MODULE_PREFIXES)]
    validator_roots += [m for m in imports if m in VALIDATOR_DEFINITION_MODULES]
    validator_roots += [m for m in imports if m.startswith((
        "Itasca.Support", "Itasca.Spec"))]
    forbidden_modules = [name for name in imports
                         if name in VALIDATOR_FORBIDDEN_PARTITIONS
                         or name == "SpecExt" or name.startswith("SpecExt.")]
    for module in validator_roots:
        for forbidden in forbidden_modules:
            path = path_from(module, forbidden)
            if path:
                bad.append((module, path[-1],
                            "validator surface must not transitively import runtime partitions or SpecExt: "
                            + " -> ".join(path)))
    return bad


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=".", help="Lean source root (default: current directory)")
    args = parser.parse_args()
    missing = missing_project_imports(args.root)
    for error in missing:
        print(error)
    violations = layer_violations(source_graph(args.root))
    for module, imported, rule in violations:
        print(f"{module} imports {imported}: {rule}")
    return 1 if violations or missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
