#!/usr/bin/env python3
"""Partition Aeneas Funs.lean without changing generated declaration text.

Usage: python3 scripts/split_funs.py Itasca/Generated/Funs.lean
The input is replaced by an umbrella; six sibling files retain the original
header and declaration order, with imports of all earlier partitions added.
"""

import re
import sys
from pathlib import Path


PARTS = ("FunsValidator", "FunsRuntimeCommon", "FunsCompiler", "FunsStore",
         "FunsInterp", "FunsInstantiate")
CHUNK_START = re.compile(r"(?m)^(?=/-- \[)")
RUST_PATH = re.compile(r"/-- \[(itasca::[^\]\n]+)\]")


def partition(rust_path):
    components = rust_path.split("::")
    if components[1] != "runtime":
        return "FunsValidator"
    if len(components) < 3:
        raise ValueError(f"missing runtime item: {rust_path}")
    area = components[2]
    if area == "store":
        return ("FunsInstantiate" if components[3:4] == ["instantiate"]
                else "FunsStore")
    if area == "compiler":
        return "FunsCompiler"
    if area == "interp":
        return "FunsInterp"
    return "FunsRuntimeCommon"


def split_funs(path):
    text = path.read_text()
    header_match = re.match(r"\A.*?^namespace Itasca\n\n", text, re.M | re.S)
    footer_match = re.search(r"(?m)^end Itasca\n?\Z", text)
    if header_match is None or footer_match is None:
        raise ValueError("expected generated header and final end Itasca")
    header = header_match.group()
    footer = footer_match.group()
    body = text[header_match.end():footer_match.start()]
    chunks = CHUNK_START.split(body)
    if chunks[0] != "" or len(chunks) == 1:
        raise ValueError("expected a Rust-path doc comment at every chunk start")
    chunks = chunks[1:]
    groups = {name: [] for name in PARTS}
    for chunk in chunks:
        match = RUST_PATH.match(chunk)
        if match is None:
            raise ValueError("chunk has no valid /-- [itasca::...] path")
        groups[partition(match[1])].append(chunk)
    if sum(map(len, groups.values())) != len(chunks):
        raise ValueError("declaration chunk count changed")
    imports = list(re.finditer(r"(?m)^public import [^\n]+\n", header))
    if not imports:
        raise ValueError("generated header has no public imports")
    insertion = imports[-1].end()
    comment_match = re.match(r"\A(?:--[^\n]*\n)+module\n", header)
    if comment_match is None:
        raise ValueError("expected generated comments followed by module")
    outputs = {}
    for index, name in enumerate(PARTS):
        added = "".join(f"public import Itasca.Generated.{earlier}\n"
                        for earlier in PARTS[:index])
        outputs[path.with_name(name + ".lean")] = (
            header[:insertion] + added + header[insertion:]
            + "".join(groups[name]) + footer)
    outputs[path] = comment_match.group() + "".join(
        f"public import Itasca.Generated.{name}\n" for name in PARTS)
    for output, content in outputs.items():
        output.write_text(content)
    return {name: len(groups[name]) for name in PARTS}


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__.splitlines()[2])
    try:
        counts = split_funs(Path(sys.argv[1]))
    except ValueError as error:
        raise SystemExit(f"split_funs: {error}") from error
    print("Split " + str(sum(counts.values())) + " declarations: "
          + ", ".join(f"{name}={count}" for name, count in counts.items()))


if __name__ == "__main__":
    main()
