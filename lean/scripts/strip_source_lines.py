#!/usr/bin/env python3
"""Remove Rust line ranges from Aeneas source-location comments.

    python3 scripts/strip_source_lines.py Itasca/Generated/Types.lean Itasca/Generated/Funs.lean

Aeneas writes `Source: 'src/runtime/store.rs', lines 119:4-137:5` above every declaration. Any Rust
edit that moves lines changes those comments, and Lake then rebuilds every module that imports the
generated files, even though no definition changed. This keeps the file path and drops the range.
Only comment text changes; no definition is touched.
"""
import re
import sys

LINES = re.compile(r"(Source: '[^']*'), lines \d+:\d+-\d+:\d+")

for path in sys.argv[1:]:
    text = open(path).read()
    stripped = LINES.sub(r"\1", text)
    if stripped != text:
        with open(path, "w") as out:
            out.write(stripped)
