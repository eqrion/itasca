"""Collect authoritative Lean audit data without publishing generated artifacts."""
import json
import os
from pathlib import Path
import subprocess


def discover_handwritten_modules(root):
    """Include unused implementations and examples in the global proof scan.

    Building a Lake library checks its submodules without making them imports of
    its root module. Main/Interface/Results alone do not load the whole project.
    """
    return sorted('.'.join(path.relative_to(root).with_suffix('').parts)
                  for area in ('Itasca', 'SpecExt')
                  for path in (root / area).rglob('*.lean')
                  if 'Generated' not in path.relative_to(root).parts)


def audit_source(root):
    root = root.resolve()
    source = (root / 'scripts/Audit.lean').read_text()
    imports = list(dict.fromkeys(['Itasca.Main', *discover_handwritten_modules(root)]))
    source = source.replace('import Itasca.Main', '\n'.join('import ' + name for name in imports), 1)
    return source.replace('include_str "public-results.txt"',
                          'include_str ' + json.dumps(str(root / 'scripts/public-results.txt')))



def collect_audit(root, directory, full_export=None):
    """Run the same strict audit for production reports and explicit snapshots."""
    root, directory = Path(root).resolve(), Path(directory).resolve()
    script, metadata = directory / 'Audit.lean', directory / 'metadata.json'
    script.write_text(audit_source(root))
    env = dict(os.environ, ITASCA_AUDIT_REQUIRE_INTERFACE='1',
               ITASCA_AUDIT_SLIM_JSON=str(metadata))
    env.pop('ITASCA_AUDIT_JSON', None)
    if full_export is not None:
        env['ITASCA_AUDIT_JSON'] = str(Path(full_export).resolve())
    result = subprocess.run(['lake', 'env', 'lean', str(script)], cwd=root,
                            env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, check=True)
    return result.stdout, json.loads(metadata.read_text())
