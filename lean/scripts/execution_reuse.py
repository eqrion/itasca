#!/usr/bin/env python3
"""Derive exact runtime reuse maps from the checked validator extraction.

The LLBC supplies original Rust members, and generated Lean supplies their actual
extracted names. Mismatched declaration kinds/counts fail closed. No Rust bodies
or generated Lean definitions are rewritten.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re


def rust_name(decl: dict) -> str | None:
    parts = decl["item_meta"]["name"]
    if not all("Ident" in part for part in parts):
        return None
    return "::".join(part["Ident"][0] for part in parts)


def build_map(llbc: dict, lean: str) -> dict:
    source = llbc["translated"]
    rust_types = {rust_name(d): d for d in source["type_decls"] if d}
    rust_traits = {rust_name(d): d for d in source["trait_decls"] if d}
    types, traits = [], []
    pattern = r"/-- (Trait declaration: )?\[([^\]]+)\].*?-/(.*?)(?=\n/--|\Z)"
    for match in re.finditer(pattern, lean, re.S):
        trait, rust, body = match.groups()
        declaration = re.search(r"^(structure|inductive) (\S+)", body, re.M)
        if not declaration:
            continue
        kind, name = declaration.groups()
        fields = re.findall(r"^  (\S+)\s*:", body, re.M)
        variants = re.findall(r"^\| (\S+)\s*:", body, re.M)
        if trait:
            decl = rust_traits[rust]
            methods = [m["skip_binder"]["name"] for m in decl["methods"]]
            parents = fields[:len(decl["implied_clauses"])]
            lean_methods = fields[len(parents):]
            if len(methods) != len(lean_methods):
                raise ValueError(f"Trait member count changed: {rust}")
            if any(r != l.removeprefix("«").removesuffix("»") for r, l in zip(methods, lean_methods)):
                raise ValueError(f"Trait member identity changed: {rust}")
            traits.append(dict(rust=rust, lean="_root_.Itasca." + name,
                               parents=parents, methods=list(zip(methods, lean_methods))))
        else:
            source_kind = rust_types[rust]["kind"]
            if kind == "structure" and isinstance(source_kind, dict) and "Struct" in source_kind:
                members = [f["name"] for f in source_kind["Struct"]]
                lean_members = fields
            elif kind == "inductive" and isinstance(source_kind, dict) and "Enum" in source_kind:
                members = [v["name"] for v in source_kind["Enum"]]
                lean_members = variants
            else:
                raise ValueError(f"Type kind changed: {rust}")
            if len(members) != len(lean_members) or any(m is None for m in members):
                raise ValueError(f"Type member count changed: {rust}")
            if any(r != l.removeprefix("«").removesuffix("»") for r, l in zip(members, lean_members)):
                raise ValueError(f"Type member identity changed: {rust}")
            types.append(dict(rust=rust, lean="_root_.Itasca." + name,
                              kind="struct" if kind == "structure" else "enum",
                              members=list(zip(members, lean_members))))
    if not types or not traits:
        raise ValueError("Validator extraction contains no reusable types or traits")
    return dict(imports=["Exec.Generated.TypesExternal"], types=types, traits=traits)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("llbc", type=Path)
    parser.add_argument("types", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = build_map(json.loads(args.llbc.read_text()), args.types.read_text())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
