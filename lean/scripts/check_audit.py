#!/usr/bin/env python3
"""Check audit coverage and import layers for each independently audited library.

Each Audit imports exactly its library's sink modules. Pass --write to refresh
those imports, or --root to check a single library. The complete builtin policy
rejects opaque placeholders; earlier stage modes remain for regression tests.
"""
import argparse
from pathlib import Path
import sys

from lean_source import Token, header_imports, tokens

ROOT = Path(__file__).resolve().parents[1]
LIBRARIES = ("Itasca", "SpecExt")
# All builtin bodies now have definitions. This does not mark their runtime
# simulation proofs complete. The checked-in policy prevents opaque regressions.
BUILTIN_STAGE = "complete"

VALIDATOR_LAYERS = {
    "Support": {"Support", "Generated"},
    "Spec": {"Spec", "Support", "Generated"},
    "Binary": {"Binary", "Spec", "Support", "Generated"},
    "Handler": {"Handler", "Binary", "Spec", "Support", "Generated", "Visitor"},
    "Contracts": {"Module", "Profile", "Binary", "Spec", "Support", "Generated"},
    "Main": {"Contracts", "Results", "Itasca.Runtime.Contracts"},
}
# Headline results sit at the top: only the entry module and examples import them.
RESULT_IMPORTERS = {"Main", "Examples"}
# Examples use the results exactly as their library's `Main` exports them. Each
# exception names an example of a supporting result that is not a headline theorem.
EXAMPLE_IMPORTS = {
    ("Itasca.Examples.Module.CustomTrace", "Itasca.Module.Custom.Trace"),
}
# Headline results about the runtime. They and `Main` are the only validator-side
# modules that import the runtime or the specification extensions.
RUNTIME_RESULTS = {"Itasca.Results.Compile", "Itasca.Results.Instantiate", "Itasca.Results.Invoke"}
# Runtime layers, under `Itasca.Runtime`. Representation owns shared certificates; no
# compiler, interpreter or store construction proof can enter through that foundation.
RUNTIME_LAYERS = {
    "Spec": {"Itasca.Runtime.Spec", "SpecExt", "Itasca.Spec", "Itasca.Support"},
    "SourceMachine": {"Itasca.Runtime.SourceMachine", "Itasca.Runtime.Spec", "SpecExt", "Itasca.Spec"},
    "Equations": {"Itasca.Generated", "Aeneas"},
    "Platform": {"Itasca.Runtime.Platform", "Itasca.Runtime.Equations", "Itasca.Generated", "Itasca.Runtime.Spec", "SpecExt"},
    "Representation": {"Itasca.Runtime.Representation", "Itasca.Runtime.Equations", "Itasca.Runtime.Platform",
                       "Itasca.Runtime.Spec", "Itasca.Runtime.SourceMachine", "SpecExt.Builtins", "Itasca"},
    "Compiler": {"Itasca.Runtime.Compiler", "Itasca.Runtime.Representation", "Itasca.Runtime.Equations", "Itasca.Runtime.Platform",
             "Itasca.Runtime.SourceMachine", "Itasca.Runtime.Spec", "SpecExt.Builtins", "Itasca"},
    "Interp": {"Itasca.Runtime.Interp", "Itasca.Runtime.Representation", "Itasca.Runtime.Equations",
               "Itasca.Runtime.Platform", "Itasca.Runtime.SourceMachine", "Itasca.Runtime.Compiler", "Itasca.Runtime.Spec",
               "SpecExt.Builtins", "Itasca.Support", "Itasca.Generated"},
    "Store": {"Itasca.Runtime.Store", "Itasca.Runtime.Representation", "Itasca.Runtime.Equations",
              "Itasca.Runtime.Platform", "Itasca.Runtime.Spec", "Itasca.Runtime.Interp", "Itasca.Runtime.Compiler",
              "Itasca.Generated"},
    "Integration": {"Itasca.Runtime", "Itasca", "SpecExt", "Aeneas"},
    # Contracts stay below the constructions that assume them. The one API
    # invariant dependency is admitted exactly in check_runtime_layer, not as
    # a prefix that would also admit constructions placed below that path.
    "Contracts": {"Itasca.Runtime.Platform", "Itasca.Runtime.Equations", "Itasca.Generated", "Itasca.Runtime.Spec",
                  "Itasca.Runtime.Representation", "Itasca.Runtime.Store", "Itasca.Runtime.Interp.Relations", "SpecExt"},
}
# Integration stages can use local proofs, but never flow back into them.
COMPILER_STAGES = {"Local": 0, "Body": 1, "Module": 2}
FOUNDATIONS = {"Init", "Lean", "Std", "Batteries", "Mathlib"}
SPEC_MODULES = {"wasm2.0", "Wasm2Prefix", "Wasm2Builtins"}


def under(name: str, prefix: str) -> bool:
    return name == prefix or name.startswith(prefix + ".")


def template(name: str) -> bool:
    return name.rsplit(".", 1)[-1] in {"FunsExternal_Template", "TypesExternal_Template"}


def load(root: Path, library: str = "Itasca") -> dict[str, list[str]]:
    return {
        ".".join(path.relative_to(root).with_suffix("").parts): header_imports(path.read_text())
        for path in (root / library).rglob("*.lean")
    }


def sinks(modules: dict[str, list[str]], library: str = "Itasca") -> list[str]:
    audit = library + ".Audit"
    imported = {i for name, imports in modules.items() if name != audit for i in imports}
    return sorted(m for m in modules if m not in imported and m != audit and not template(m))


def check_acyclic(modules: dict[str, list[str]]) -> None:
    """Reject cycles even when an audit sink reaches them.

    Use an explicit DFS stack so checking a long proof chain does not depend on
    Python's recursion limit. External modules belong to their own libraries.
    """
    finished: set[str] = set()
    for start in sorted(modules):
        if start in finished:
            continue
        active = {start}
        path = [start]
        stack = [iter(modules[start])]
        while stack:
            child = next(stack[-1], None)
            if child is None:
                finished.add(path[-1])
                active.remove(path.pop())
                stack.pop()
            elif child in active:
                cycle = path[path.index(child):] + [child]
                raise ValueError("Import cycle: " + " -> ".join(cycle))
            elif child in modules and child not in finished:
                active.add(child)
                path.append(child)
                stack.append(iter(modules[child]))


def write_audit(root: Path, modules: dict[str, list[str]], library: str = "Itasca") -> None:
    path = root / library / "Audit.lean"
    lines = path.read_text().split("\n")
    others = [l for l in lines if l.startswith("import ") and not l.startswith(f"import {library}.")]
    body = [l for l in lines if not l.startswith("import ")]
    while body and body[0] == "":
        body.pop(0)
    path.write_text("\n".join([f"import {m}" for m in sinks(modules, library)] + others + [""] + body))


def check_layer(name: str, imported: str, library: str) -> None:
    if name == library + ".Audit":
        return
    layer = name.split(".")[1]
    if library == "Itasca":
        # The runtime builds on the validator's headline results.
        result = imported == "Itasca.Main" or under(imported, "Itasca.Results")
        validator_result = result and imported != "Itasca.Main" and imported not in RUNTIME_RESULTS
        if result and layer not in RESULT_IMPORTERS and not (layer == "Runtime" and validator_result):
            raise ValueError(f"{name} imports {imported}; only Main and Examples import the headline results")
        if (layer == "Examples" and under(imported, library) and imported != "Itasca.Main"
                and not under(imported, "Itasca.Examples") and (name, imported) not in EXAMPLE_IMPORTS):
            raise ValueError(f"{name} imports {imported}; examples import only Itasca.Main")
        if layer == "Runtime":
            check_runtime_layer(name, imported)
            return
        if (layer not in RESULT_IMPORTERS and name not in RUNTIME_RESULTS
                and any(under(imported, other) for other in ("Itasca.Runtime", "SpecExt"))):
            raise ValueError(f"{name} imports {imported}; validator imports must stay independent")
        if layer in VALIDATOR_LAYERS and under(imported, "Itasca"):
            if imported.split(".")[1] not in VALIDATOR_LAYERS[layer] and imported not in VALIDATOR_LAYERS[layer]:
                raise ValueError(f"{name} imports {imported}, above the {layer}/ layer")
        return
    if layer == "Builtins":
        allowed = {"SpecExt.Builtins", "Wasm2Prefix", "Lean", "Batteries", "Mathlib"}
    elif layer in {"Host", "Wasm1"}:
        allowed = FOUNDATIONS | {"wasm2.0", "SpecExt.Builtins"}
    else:
        raise ValueError(f"{name} has no declared SpecExt import layer")
    if not any(under(imported, prefix) for prefix in allowed):
        raise ValueError(f"{name} imports {imported}, outside the {library}.{layer} layer")


def check_runtime_layer(name: str, imported: str) -> None:
    layer = name.split(".")[2]
    if layer not in RUNTIME_LAYERS:
        raise ValueError(f"{name} has no declared Itasca.Runtime import layer")
    allowed = RUNTIME_LAYERS[layer] | FOUNDATIONS
    if layer == "Contracts" and imported == "Itasca.Runtime.Integration.Api.ExecutableInv":
        return
    if layer in {"Spec", "Integration"}:
        allowed = allowed | SPEC_MODULES
    if layer == "Compiler" and under(imported, "Itasca.Runtime.Compiler"):
        source_stage = name.split(".")[3]
        target_stage = imported.split(".")[3]
        if source_stage not in COMPILER_STAGES or target_stage not in COMPILER_STAGES:
            raise ValueError(f"{name} or {imported} has no declared compiler stage")
        if COMPILER_STAGES[target_stage] > COMPILER_STAGES[source_stage]:
            raise ValueError(f"{name} imports {imported}, above its compiler stage")
    for owner, final in (("Interp", "Invocation"), ("Store", "Instantiation")):
        if layer == owner and under(imported, f"Itasca.Runtime.{owner}.{final}"):
            if not under(name, f"Itasca.Runtime.{owner}.{final}"):
                raise ValueError(f"{name} imports {imported}, above its integration stage")
    if imported == "Itasca.Generated.Funs" and name != "Itasca.Runtime.Equations":
        raise ValueError(f"{name} imports {imported}; import Itasca.Runtime.Equations, which shares the runtime's equation lemmas")
    # Reuse canonical source typing, environment caches, and the abstract
    # module-binding extension theorem without opening their entire hierarchies.
    if name == "Itasca.Runtime.Spec.SegmentCopySlice" and imported == "Aeneas.Data.List.List":
        return
    if layer == "Store" and imported in {
        "Itasca.Module.Const.Syntax", "Itasca.Module.Elab.SegmentSyntax",
        "Itasca.Module.Env.Basic", "Itasca.Module.Elab.Metadata",
        "Itasca.Runtime.SourceMachine.ModuleBindingsExtension", "Itasca.Runtime.SourceMachine.StoreTyping",
        "Aeneas.Data.List.List", "SpecExt.Wasm1",
    }:
        return
    # A validator prefix such as `Itasca` never admits the runtime itself.
    runtime = under(imported, "Itasca.Runtime")
    if not any(under(imported, prefix) and (under(prefix, "Itasca.Runtime") or not runtime) for prefix in allowed):
        raise ValueError(f"{name} imports {imported}, outside the Itasca.Runtime.{layer} layer")


def check_builtins(root: Path, stage: str = BUILTIN_STAGE) -> None:
    if stage not in {"placeholders", "lanes", "complete"}:
        raise ValueError(f"Unknown builtin audit stage: {stage}")
    if stage == "placeholders":
        return
    paths = list((root / "SpecExt" / "Builtins").rglob("*.lean"))
    umbrella = root / "SpecExt" / "Builtins.lean"
    if umbrella.exists():
        paths.append(umbrella)
    for path in paths:
        stream = list(tokens(path.read_text()))
        for i, tok in enumerate(stream):
            if tok == Token("ident", "opaque"):
                name = stream[i + 1].value if i + 1 < len(stream) else "<missing>"
                if stage == "lanes" and name in {"lanes_", "inv_lanes_"}:
                    continue
                raise ValueError(f"{path.relative_to(root)} contains opaque builtin {name} ({stage} stage)")
    if stage == "complete":
        check_builtin_inventory(root)


def check_builtin_inventory(root: Path) -> None:
    signatures = root / "SpecTec" / "Wasm2Builtins.lean"
    # Small audit-layer fixtures need not contain a generated specification.
    if not signatures.exists():
        return
    stream = list(tokens(signatures.read_text()))
    expected = [stream[i + 3].value for i in range(len(stream) - 3)
                if stream[i:i + 3] == [Token("symbol", ":"), Token("symbol", "="), Token("symbol", "@")]
                and stream[i + 3].kind == "ident"]
    if not expected or len(expected) != len(set(expected)):
        raise ValueError("Generated builtin signatures must name distinct builtin symbols")
    path = root / "SpecExt" / "Builtins" / "Inventory.lean"
    stream = list(tokens(path.read_text()))
    start = next((i + 2 for i in range(len(stream) - 1)
                  if stream[i:i + 2] == [Token("ident", "def"), Token("ident", "inventory")]), None)
    if start is None:
        raise ValueError("Missing builtin review inventory definition")
    end = next((i for i in range(start, len(stream)) if stream[i] == Token("ident", "theorem")), len(stream))
    reviewed = [stream[i + 2].value for i in range(start, end - 2)
                if stream[i:i + 2] == [Token("symbol", "`"), Token("symbol", "`")]
                and stream[i + 2].kind == "ident"]
    if len(reviewed) != len(set(reviewed)):
        raise ValueError("Duplicate builtin review inventory symbol")
    missing, extra = set(expected) - set(reviewed), set(reviewed) - set(expected)
    if missing or extra:
        raise ValueError("Builtin review inventory differs from generated signatures: "
                         f"missing {sorted(missing)}, extra {sorted(extra)}")


def check(root: Path, library: str = "Itasca") -> None:
    modules = load(root, library)
    audit = library + ".Audit"
    if audit not in modules:
        raise ValueError(f"Missing audit module {audit}")
    for name, imports in sorted(modules.items()):
        if template(name):
            continue
        for imported in imports:
            if template(imported):
                raise ValueError(f"{name} imports the generated external-model template")
            owner = imported.split(".")[0]
            if owner in LIBRARIES and not (root / Path(*imported.split("."))).with_suffix(".lean").is_file():
                raise ValueError(f"{name} imports missing module {imported}")
            if imported.endswith(".Audit"):
                raise ValueError(f"{name} imports audit entry point {imported}")
            check_layer(name, imported, library)
    audited = [i for i in modules[audit] if under(i, library)]
    if audited != sinks(modules, library):
        raise ValueError(f"{audit} must import exactly the sink modules; run `just audit-imports`")
    seen, pending = set(), [audit]
    while pending:
        name = pending.pop()
        if name in seen or name not in modules:
            continue
        seen.add(name)
        pending.extend(modules[name])
    omitted = {m for m in modules if not template(m)} - seen
    if omitted:
        raise ValueError(f"Modules outside {audit}: " + ", ".join(sorted(omitted)))
    check_acyclic(modules)
    if library == "SpecExt":
        check_builtins(root)
    print(f"{library} audit import coverage: {len(seen)} modules; layers import downward")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="refresh audit sink imports")
    parser.add_argument("--root", choices=LIBRARIES, action="append", dest="libraries")
    args = parser.parse_args()
    for library in args.libraries or LIBRARIES:
        if args.write:
            write_audit(ROOT, load(ROOT, library), library)
        check(ROOT, library)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        sys.exit(str(error))
