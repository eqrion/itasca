#!/usr/bin/env python3
"""Cheap source check for forbidden proof constructs; no Lean build required.

Comments and string literals are ignored. The compiled audit separately inspects
proof dependencies, including opaque theorem values.
"""
from pathlib import Path
import re

from architecture import mask_comments_and_strings


FORBIDDEN = re.compile(
    r'\b(?:sorry|native_decide|axiom|admit|'
    r'Step_is_wf|Step_read_is_wf|Step_pure_is_wf)\b')


def check(root):
    errors = []
    for area in ('Itasca', 'SpecExt'):
        for path in sorted((root / area).rglob('*.lean')):
            if 'Generated' in path.relative_to(root).parts:
                continue
            source = mask_comments_and_strings(path.read_text())
            for match in FORBIDDEN.finditer(source):
                line = source.count('\n', 0, match.start()) + 1
                errors.append(f'{path.relative_to(root)}:{line}: forbidden {match[0]}')
    return errors


if __name__ == '__main__':
    problems = check(Path.cwd())
    for problem in problems:
        print(problem)
    raise SystemExit(bool(problems))
