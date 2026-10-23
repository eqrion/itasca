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
LIBRARIES = ("Itasca", "SpecExt", "Exec")
# All builtin bodies now have definitions. This does not mark their runtime
# simulation proofs complete. The checked-in policy prevents opaque regressions.
BUILTIN_STAGE = "complete"

VALIDATOR_LAYERS = {
    "Support": {"Support", "Generated"},
    "Spec": {"Spec", "Support", "Generated"},
    "Binary": {"Binary", "Spec", "Support", "Generated"},
    "Handler": {"Handler", "Binary", "Spec", "Support", "Generated", "Visitor"},
    "Contracts": {"Module", "Profile", "Binary", "Spec", "Support", "Generated"},
    "Main": {"Contracts", "Results"},
}
# Headline results sit at the top: only the entry module and examples import them.
RESULT_IMPORTERS = {"Main", "Examples"}
# Examples use the results exactly as their library's `Main` exports them. Each
# exception names an example of a supporting result that is not a headline theorem.
EXAMPLE_IMPORTS = {
    ("Itasca.Examples.Module.CustomTrace", "Itasca.Module.Custom.Trace"),
    ("Exec.Examples.Host.AllocationCallbackExamples", "Exec.Store.Api.HostAvailability"),
}
# Representation owns shared certificates; no compiler, interpreter or store
# construction proof can enter through that foundation.
EXEC_LAYERS = {
    "Spec": {"Exec.Spec", "SpecExt", "Itasca.Spec", "Itasca.Support"},
    "Abs": {"Exec.Abs", "Exec.Spec", "SpecExt", "Itasca.Spec"},
    "Generated": {"Exec.Generated", "Aeneas"},
    "Platform": {"Exec.Platform", "Exec.Generated", "Exec.Spec", "SpecExt"},
    "Representation": {"Exec.Representation", "Exec.Generated", "Exec.Platform", "Exec.Spec", "Exec.Abs", "SpecExt.Builtins", "Itasca"},
    "Code": {"Exec.Code", "Exec.Representation", "Exec.Generated", "Exec.Platform", "Exec.Abs", "Exec.Spec", "SpecExt.Builtins", "Itasca"},
    "Interp": {"Exec.Interp", "Exec.Representation", "Exec.Generated", "Exec.Platform", "Exec.Abs", "Exec.Code", "Exec.Spec", "SpecExt.Builtins", "Itasca.Support"},
    "Store": {"Exec.Store", "Exec.Representation", "Exec.Generated", "Exec.Platform", "Exec.Spec", "Exec.Interp", "Exec.Code"},
    "Theorems": {"Exec", "SpecExt", "Itasca", "Aeneas"},
    # Contracts stay below the constructions that assume them. The API invariant
    # and checked host reply are named until Theorems/Api leaves the Theorems layer.
    "Contracts": {"Exec.Platform", "Exec.Generated", "Exec.Spec", "Exec.Representation", "Exec.Store",
                  "Exec.Interp.Relations", "Exec.Theorems.Api.ExecutableInv",
                  "Exec.Theorems.Host.Chosen.HostChoiceMatching", "SpecExt"},
    "Results": {"Exec", "SpecExt", "Itasca", "Aeneas"},
    "Main": {"Exec.Contracts", "Exec.Results"},
    "Examples": {"Exec", "SpecExt", "Itasca", "Aeneas"},
}
# Integration stages can use local proofs, but never flow back into them.
COMPILER_STAGES = {"Local": 0, "Body": 1, "Module": 2}
# Basic checked programs cannot acquire reentrant or combined-driver contracts
# through their implementation dependencies.
HOST_STAGES = {"Callbacks": 0, "Chosen": 1, "Reentrant": 2, "Open": 3}
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
    if library in {"Itasca", "Exec"}:
        main = library + ".Main"
        if (imported == main or under(imported, library + ".Results")) and layer not in RESULT_IMPORTERS:
            raise ValueError(f"{name} imports {imported}; only Main and Examples import the headline results")
        if (layer == "Examples" and under(imported, library) and imported != main
                and not under(imported, library + ".Examples") and (name, imported) not in EXAMPLE_IMPORTS):
            raise ValueError(f"{name} imports {imported}; examples import only {main}")
    if library == "Itasca":
        if any(under(imported, other) for other in ("Exec", "SpecExt")):
            raise ValueError(f"{name} imports {imported}; validator imports must stay independent")
        if layer in VALIDATOR_LAYERS and under(imported, "Itasca"):
            if imported.split(".")[1] not in VALIDATOR_LAYERS[layer]:
                raise ValueError(f"{name} imports {imported}, above the {layer}/ layer")
        return
    if library == "SpecExt":
        if layer == "Builtins":
            allowed = {"SpecExt.Builtins", "Wasm2Prefix", "Lean", "Batteries", "Mathlib"}
        elif layer in {"Host", "Wasm1"}:
            allowed = FOUNDATIONS | {"wasm2.0", "SpecExt.Builtins"}
        else:
            raise ValueError(f"{name} has no declared SpecExt import layer")
    else:
        if layer not in EXEC_LAYERS:
            raise ValueError(f"{name} has no declared Exec import layer")
        allowed = EXEC_LAYERS[layer] | FOUNDATIONS
        if layer in {"Spec", "Theorems", "Results", "Examples"}:
            allowed = allowed | SPEC_MODULES
        if name in {"Exec.Generated.FunsExternal", "Exec.Generated.TypesExternal"}:
            allowed = allowed | {"Itasca.Generated"}
    if library == "Exec" and layer == "Code" and under(imported, "Exec.Code"):
        source_stage = name.split(".")[2]
        target_stage = imported.split(".")[2]
        if source_stage not in COMPILER_STAGES or target_stage not in COMPILER_STAGES:
            raise ValueError(f"{name} or {imported} has no declared compiler stage")
        if COMPILER_STAGES[target_stage] > COMPILER_STAGES[source_stage]:
            raise ValueError(f"{name} imports {imported}, above its compiler stage")
    if library == "Exec" and under(name, "Exec.Theorems.Host") and under(imported, "Exec.Theorems.Host"):
        source_parts, target_parts = name.split("."), imported.split(".")
        source_stage = HOST_STAGES.get(source_parts[3]) if len(source_parts) > 4 else None
        target_stage = HOST_STAGES.get(target_parts[3]) if len(target_parts) > 4 else None
        if source_stage is not None and target_stage is not None and target_stage > source_stage:
            raise ValueError(f"{name} imports {imported}, above its host composition stage")
    for owner, final in (("Interp", "Invocation"), ("Store", "Instantiation")):
        if library == "Exec" and layer == owner and under(imported, f"Exec.{owner}.{final}"):
            if not under(name, f"Exec.{owner}.{final}"):
                raise ValueError(f"{name} imports {imported}, above its integration stage")
    if library == "Exec" and imported == "Exec.Generated.Funs" and layer != "Generated":
        raise ValueError(f"{name} imports {imported}; import Exec.Generated.Equations, which shares the runtime's equation lemmas")
    if library == "Exec" and under(imported, "Itasca.Generated"):
        if name not in {"Exec.Generated.FunsExternal", "Exec.Generated.TypesExternal"}:
            raise ValueError(f"{name} imports {imported}, outside the Exec.{layer} layer; only external adapters may directly reuse validator generated declarations")
    # Reuse canonical source typing, environment caches, and the abstract
    # module-binding extension theorem without opening their entire hierarchies.
    if name == "Exec.Spec.SegmentCopySlice" and imported == "Aeneas.Data.List.List":
        return
    if library == "Exec" and layer == "Store" and imported in {
        "Itasca.Module.Const.Syntax", "Itasca.Module.Elab.SegmentSyntax",
        "Itasca.Module.Env.Basic", "Itasca.Module.Elab.Metadata",
        "Exec.Abs.ModuleBindingsExtension", "Exec.Abs.StoreTyping",
        "Aeneas.Data.List.List", "SpecExt.Wasm1",
    }:
        return
    if not any(under(imported, prefix) for prefix in allowed):
        raise ValueError(f"{name} imports {imported}, outside the {library}.{layer} layer")


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
