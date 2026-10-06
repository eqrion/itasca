#!/usr/bin/env python3
"""Fail if an Itasca source module is omitted from the transitive axiom audit."""
from pathlib import Path
import sys

from lean_source import header_imports

ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = "Itasca.Generated.FunsExternal_Template"


def check(root: Path) -> None:
    modules = {
        ".".join(path.relative_to(root).with_suffix("").parts): path
        for path in (root / "Itasca").rglob("*.lean")
    }
    seen = set()
    pending = ["Itasca.Audit"]
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        if name == TEMPLATE:
            raise ValueError("The generated external-model template must not be imported")
        if name not in modules:
            if name.startswith("Itasca."):
                raise ValueError(f"Missing audited module: {name}")
            continue
        seen.add(name)
        pending.extend(header_imports(modules[name].read_text()))
    omitted = set(modules) - seen - {TEMPLATE}
    if omitted:
        raise ValueError("Modules outside Itasca.Audit: " + ", ".join(sorted(omitted)))
    print(f"Audit import coverage: {len(seen)} modules; unused external template excluded")


if __name__ == "__main__":
    try:
        check(ROOT)
    except ValueError as error:
        sys.exit(str(error))
