#!/usr/bin/env python3
"""Build and audit the public surface; check artifacts unless --update is explicit.

--no-build reuses the caller's integrated build (CI and just verify).
Both modes enforce the same Lean ownership, root-registry and axiom checks.
"""
import argparse
import json
from pathlib import Path
import os
import subprocess
import sys
import tempfile
from audit_environment import collect_audit
from interface_manifest import join_metadata


def build_artifacts(root, report, metadata):
    origins = json.loads((root / 'metrics/interface-origins.json').read_text())
    current = join_metadata(metadata, origins)
    return {
        Path('metrics/audit.txt'): report.encode(),
        Path('metrics/interface-manifest.json'):
            (json.dumps(current, ensure_ascii=False, separators=(',', ':')) + '\n').encode(),
    }


def publish(root, artifacts, update=False):
    """Check without writes, or stage every complete output before replacing files."""
    changed = [path for path, data in artifacts.items()
               if not (root / path).exists() or (root / path).read_bytes() != data]
    if not update:
        for path in changed:
            print(f'stale audit artifact: {path}', file=sys.stderr)
        if changed:
            print('Run just audit --update and review the generated changes.', file=sys.stderr)
        return not changed
    if changed:
        build_dir = root / '.build'
        build_dir.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='audit-publish-', dir=build_dir) as directory:
            staged = []
            for index, path in enumerate(changed):
                temporary = Path(directory) / str(index)
                temporary.write_bytes(artifacts[path])
                staged.append((temporary, root / path))
            for temporary, destination in staged:
                os.replace(temporary, destination)
    return True


def main(argv=None, root=None):
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true', help='fail on stale artifacts (default)')
    mode.add_argument('--update', action='store_true', help='refresh the audit report and interface manifest')
    parser.add_argument('--no-build', action='store_true', help='reuse an already completed Lean build')
    parser.add_argument('--snapshot', type=Path,
                        help='also export full semantic identities from this same audit run')
    args = parser.parse_args(argv)
    root = Path(root) if root is not None else Path(__file__).resolve().parent.parent
    try:
        if not args.no_build:
            subprocess.run(['lake', 'build', 'Itasca', 'SpecExt'], cwd=root, check=True)
        with tempfile.TemporaryDirectory(prefix='itasca-public-audit-') as directory:
            report, metadata = collect_audit(root, Path(directory), full_export=args.snapshot)
            artifacts = build_artifacts(root, report, metadata)
            if not publish(root, artifacts, update=args.update):
                return 1
    except subprocess.CalledProcessError as error:
        if error.output:
            print(error.output, file=sys.stderr, end='')
        print(f'audit command failed: {error.cmd}', file=sys.stderr)
        return 1
    except (OSError, ValueError) as error:
        print(f'audit failed: {error}', file=sys.stderr)
        return 1
    print('Audit passed; ' + ('artifacts updated.' if args.update else 'all artifacts current.'))
    return 0


if __name__ == '__main__':
    sys.exit(main())
