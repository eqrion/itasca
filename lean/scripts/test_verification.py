"""Exercise the real Make orchestration while substituting its expensive children."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


class VerifyTests(unittest.TestCase):
    def test_verify_runs_every_gate_in_order_and_builds_proofs_once(self):
        root = Path(__file__).resolve().parents[2]
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / 'commands.jsonl'
            child = Path(directory) / 'record-make'
            child.write_text('''#!/usr/bin/env python3
import json, os, sys
with open(os.environ['VERIFY_LOG'], 'a') as output:
    output.write(json.dumps(sys.argv[1:]) + '\\n')
''')
            child.chmod(0o755)
            subprocess.run(['make', 'verify', f'MAKE={child}'], cwd=root,
                           env=dict(os.environ, VERIFY_LOG=str(log)), check=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            commands = [json.loads(line) for line in log.read_text().splitlines()]
            self.assertEqual(commands, [['test'], ['tooling-test'], ['lint'], ['extract-check'],
                ['-C', 'lean', 'spec-compare'], ['prove'], ['warnings'], ['audit', 'AUDIT_ARGS=--no-build']])
