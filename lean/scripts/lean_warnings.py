#!/usr/bin/env python3
"""Inventory handwritten Lean warnings from a completed build's cached traces.

Run after `just prove`; this command never rebuilds proofs or scans upstream and
generated warnings. `--check` rejects increases per module/category. `--update`
explicitly records a reviewed baseline; inspect that diff when moving modules.
"""
import argparse
import collections
import json
from pathlib import Path
import re


def collect(root):
    counts, missing = {}, []
    for area in ('Itasca', 'SpecExt'):
        for source in sorted((root / area).rglob('*.lean')):
            relative = source.relative_to(root)
            if 'Generated' in relative.parts:
                continue
            trace = root / '.lake/build/lib/lean' / relative.with_suffix('.trace')
            if not trace.exists():
                missing.append(str(relative))
                continue
            categories = collections.Counter()
            for entry in json.loads(trace.read_text()).get('log', []):
                if entry.get('level') != 'warning':
                    continue
                category = re.search(r'\blinter\.(\w+)', entry['message'])
                categories[category[1] if category else 'other'] += 1
            if categories:
                counts[str(relative)] = dict(sorted(categories.items()))
    return counts, missing


def increases(current, baseline):
    return [f'{path}: {category} warnings increased from '
            f'{baseline.get(path, {}).get(category, 0)} to {count}'
            for path, categories in sorted(current.items())
            for category, count in sorted(categories.items())
            if count > baseline.get(path, {}).get(category, 0)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--update', action='store_true')
    args = parser.parse_args()
    root = Path('.')
    counts, missing = collect(root)
    if missing:
        print('Missing build traces; run just prove before checking warnings:')
        print('\n'.join(missing))
        return 1
    path = root / 'metrics/warnings.json'
    if args.update:
        path.write_text(json.dumps(counts, indent=2, sort_keys=True) + '\n')
    errors = increases(counts, json.loads(path.read_text())) if args.check else []
    for error in errors:
        print(error)
    categories = collections.Counter()
    for module in counts.values():
        categories.update(module)
    print(f'{sum(categories.values())} handwritten warnings in {len(counts)} modules')
    for name, count in categories.most_common():
        print(f'  {name}: {count}')
    return bool(errors)


if __name__ == '__main__':
    raise SystemExit(main())
