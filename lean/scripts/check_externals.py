#!/usr/bin/env python3
"""Compare fresh Aeneas external requests with actual concrete model declarations.

This checks declaration kinds and Rust attributes. The integrated Lean build
checks their types and the transitive axiom audit checks proof dependencies.
"""
from pathlib import Path
import sys

from lean_source import Token, tokens

ROOT = Path(__file__).resolve().parents[1]


def patterns(path: Path, declaration_kind: str) -> set[str]:
    source = list(tokens(path.read_text()))
    # A syntax quotation can contain attribute/definition tokens without
    # declaring a model. Current adapters need no quotation machinery; fail
    # closed rather than treating quoted commands as concrete definitions.
    if Token("symbol", "`") in source:
        raise ValueError(f"Lean syntax quotations require external-model review in {path}")
    found = set()
    for i in range(len(source) - 2):
        if source[i:i + 3] != [Token("symbol", "@"), Token("symbol", "["), Token("ident", "rust_fun")]:
            continue
        if i + 5 >= len(source) or source[i + 3].kind != "string" or source[i + 4] != Token("symbol", "]"):
            raise ValueError(f"Unsupported rust_fun attribute in {path}")
        pattern = source[i + 3].value
        if "\\" in pattern:
            raise ValueError(f"Escaped rust_fun pattern requires review in {path}")
        j = i + 5
        while j < len(source) and source[j].kind == "ident" and source[j].value in {
            "public", "private", "protected", "noncomputable", "unsafe"}:
            j += 1
        if j >= len(source) or source[j] != Token("ident", declaration_kind):
            raise ValueError(f"rust_fun {pattern!r} must annotate {declaration_kind}, not another declaration in {path}")
        if pattern in found:
            raise ValueError(f"Duplicate rust_fun pattern {pattern!r} in {path}")
        found.add(pattern)
    return found


def check(template: Path, model: Path) -> None:
    requested = patterns(template, "axiom")
    modeled = patterns(model, "def")
    if not requested:
        raise ValueError("No external requests found; check the generated template format")
    if requested != modeled:
        raise ValueError(f"External model mismatch: missing={sorted(requested - modeled)}, "
                         f"extra={sorted(modeled - requested)}")
    print(f"External model coverage: {len(requested)} concrete definitions")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("usage: check_externals.py FunsExternal_Template.lean")
    try:
        check(Path(sys.argv[1]), ROOT / "Itasca/Generated/FunsExternal.lean")
    except ValueError as error:
        sys.exit(str(error))
