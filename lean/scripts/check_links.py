#!/usr/bin/env python3
"""Check relative links in Markdown files and Lean docstrings.

    python3 scripts/check_links.py        (run from `lean/`)

Reports every `[text](relative/path)` whose target file does not exist. Moving or merging Lean
modules breaks these links; run this after any such change.
"""
import os
import re
import sys

LINK = re.compile(r"\[[^\]\n]*\]\(([^)\s]+)\)")
SKIP_DIRS = {".lake", ".build", ".git", "target", "vendor", "third_party"}


def files(root):
    for d, dirs, fs in os.walk(root):
        dirs[:] = [x for x in dirs if x not in SKIP_DIRS]
        for f in fs:
            if f.endswith(".md") or f.endswith(".lean"):
                yield os.path.join(d, f)


def main():
    broken = 0
    for path in files(".."):
        if os.sep + "Generated" + os.sep in path or os.sep + "SpecTec" + os.sep in path:
            continue
        text = open(path, errors="replace").read()
        for target in LINK.findall(text):
            if re.match(r"[a-z]+:", target) or target.startswith("#"):
                continue
            target = target.split("#")[0]
            if not target:
                continue
            if not os.path.exists(os.path.normpath(os.path.join(os.path.dirname(path), target))):
                print(f"{os.path.relpath(path, '..')}: broken link {target}")
                broken += 1
    return 1 if broken else 0


if __name__ == "__main__":
    sys.exit(main())
