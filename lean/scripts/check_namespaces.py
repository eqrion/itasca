#!/usr/bin/env python3
"""Enforce handwritten Itasca semantic namespace subjects; module paths stay independent.

Run from lean/. Imported module names are deliberately not namespace declarations.
Extracted/upstream operation extensions retain their existing lowercase subjects.
"""
from pathlib import Path
import re
from architecture import mask_comments_and_strings

SUBJECTS = frozenset({
    'Automation', 'Binary', 'Body', 'CodeEntry', 'Compiler', 'Computation', 'Examples', 'Handler',
    'Integration', 'Interp', 'Module', 'Platform', 'Representation', 'RustResult',
    'SourceMachine', 'Spec', 'Store', 'Stream', 'Translation', 'Visitor',
})
BOUNDARY_SUBJECTS = frozenset({'Primitive', 'code', 'core', 'error', 'limits',
                               'metadata', 'reader', 'runtime', 'signature', 'stream', 'wasm_types'})
COMMAND = re.compile(r'^\s*(?:noncomputable\s+)?(namespace|section|mutual|end)\b(?:\s+([\w.\']+))?')
DECLARATION = re.compile(
    r'^\s*(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*'
    r'(?:def|theorem|lemma|abbrev|structure|inductive|class)\s+([\w.\']+)')


def qualify(namespace, spelling):
    if spelling.startswith('_root_.'):
        return spelling[len('_root_.'):]
    if spelling.startswith('Itasca.') or not namespace:
        return spelling
    return namespace + '.' + spelling


def subject_error(name):
    parts = name.split('.')
    if len(parts) < 2 or parts[0] != 'Itasca':
        return None
    subject = parts[1]
    if subject in SUBJECTS:
        repeated = next((left for left, right in zip(parts[1:], parts[2:])
                         if left == right), None)
        if repeated:
            return f'{name}: repeated namespace component {repeated}; attach the type directly to its subject'
        return None
    if subject in BOUNDARY_SUBJECTS:
        return None
    return f'{name}: unknown semantic subject {subject}; see NAMESPACES.md'


def namespace_errors(source):
    stack, errors = [], []
    for line_number, line in enumerate(mask_comments_and_strings(source).splitlines(), 1):
        namespace = next((value for kind, value, _ in reversed(stack) if kind == 'namespace'), '')
        command = COMMAND.match(line)
        name = None
        if command:
            kind, spelling = command.groups()
            if kind == 'namespace':
                name = qualify(namespace, spelling)
                stack.append((kind, name, spelling))
            elif kind in ('section', 'mutual'):
                stack.append((kind, '', spelling))
            elif stack:
                scope, value, opening = stack.pop()
                if scope == 'namespace' and spelling and opening.endswith('.' + spelling):
                    stack.append((scope, value[:-len(spelling)-1], opening[:-len(spelling)-1]))
        elif declaration := DECLARATION.match(line):
            # A simple private helper is already qualified by Lean's owning module.
            # Explicit namespace extensions still obey the public subject map.
            private_local = ('.' not in declaration[1] and
                             re.search(r'\bprivate\b', line[:declaration.start(1)]))
            if not private_local:
                name = qualify(namespace, declaration[1])
        if name and (error := subject_error(name)):
            errors.append(f'{line_number}: {error}')
    return errors


def main():
    errors = []
    root = Path(__file__).resolve().parent.parent
    for source in sorted((root / 'Itasca').rglob('*.lean')):
        if 'Generated' in source.parts:
            continue
        errors.extend(f'{source.relative_to(root)}:{error}' for error in namespace_errors(source.read_text()))
    for error in errors:
        print(error)
    return bool(errors)


if __name__ == '__main__':
    raise SystemExit(main())
