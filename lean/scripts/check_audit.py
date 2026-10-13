#!/usr/bin/env python3
"""Check that every Itasca module is audited and that proof layers import downward.

`Itasca.Audit` must import exactly the sink modules of the import graph, which
makes every other module reachable. Pass `--write` to regenerate those imports.
"""
from pathlib import Path
import sys

from lean_source import header_imports

ROOT = Path(__file__).resolve().parents[1]
AUDIT = "Itasca.Audit"
TEMPLATE = "Itasca.Generated.FunsExternal_Template"

# Lower layers must stay readable without the validator proofs above them.
LAYERS = {
    "Support": {"Support", "Generated"},
    "Spec": {"Spec", "Support", "Generated"},
    "Binary": {"Binary", "Spec", "Support", "Generated"},
    "Handler": {"Handler", "Binary", "Spec", "Support", "Generated", "Visitor"},
}


def load(root: Path) -> dict[str, list[str]]:
    modules = {}
    for path in (root / "Itasca").rglob("*.lean"):
        name = ".".join(path.relative_to(root).with_suffix("").parts)
        modules[name] = header_imports(path.read_text())
    return modules


def sinks(modules: dict[str, list[str]]) -> list[str]:
    imported = {i for name, imports in modules.items() if name != AUDIT for i in imports}
    return sorted(m for m in modules if m not in imported and m not in (AUDIT, TEMPLATE))


def write_audit(root: Path, modules: dict[str, list[str]]) -> None:
    path = root / "Itasca" / "Audit.lean"
    lines = path.read_text().split("\n")
    others = [l for l in lines if l.startswith("import ") and not l.startswith("import Itasca.")]
    body = [l for l in lines if not l.startswith("import ")]
    while body and body[0] == "":
        body.pop(0)
    path.write_text("\n".join([f"import {m}" for m in sinks(modules)] + others + [""] + body))


def check(root: Path) -> None:
    modules = load(root)
    for name, imports in sorted(modules.items()):
        layer = name.split(".")[1]
        for i in imports:
            if i == TEMPLATE:
                raise ValueError(f"{name} imports the generated external-model template")
            if i.startswith("Itasca.") and i not in modules:
                raise ValueError(f"{name} imports missing module {i}")
            if layer in LAYERS and i.startswith("Itasca.") and i.split(".")[1] not in LAYERS[layer]:
                raise ValueError(f"{name} imports {i}, above the {layer}/ layer")
    audited = [i for i in modules[AUDIT] if i.startswith("Itasca.")]
    if audited != sinks(modules):
        raise ValueError("Itasca.Audit must import exactly the sink modules; run `just audit-imports`")
    seen, pending = set(), [AUDIT]
    while pending:
        name = pending.pop()
        if name in seen or name not in modules:
            continue
        seen.add(name)
        pending.extend(modules[name])
    omitted = set(modules) - seen - {TEMPLATE}
    if omitted:
        raise ValueError("Modules outside Itasca.Audit: " + ", ".join(sorted(omitted)))
    print(f"Audit import coverage: {len(seen)} modules; layers import downward")


if __name__ == "__main__":
    try:
        if sys.argv[1:] == ["--write"]:
            write_audit(ROOT, load(ROOT))
        check(ROOT)
    except ValueError as error:
        sys.exit(str(error))
