import json
from pathlib import Path
import tempfile
import unittest

from lean_warnings import collect, increases


class WarningTests(unittest.TestCase):
    def test_collection_ignores_generated_and_includes_specext(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ('Itasca/Generated/Types.lean', 'Itasca/Support/Translation.lean',
                         'SpecExt/Host.lean'):
                source = root / name
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text('')
                if 'Generated' in source.parts:
                    continue
                trace = root / '.lake/build/lib/lean' / Path(name).with_suffix('.trace')
                trace.parent.mkdir(parents=True, exist_ok=True)
                trace.write_text(json.dumps({'log': [
                    {'level': 'warning', 'message': 'unused; linter.unusedSimpArgs false'},
                    {'level': 'info', 'message': 'not a warning'},
                    {'level': 'warning', 'message': 'other warning'},
                ]}))
            counts, missing = collect(root)
            self.assertEqual(missing, [])
            self.assertEqual(counts, {name: {'other': 1, 'unusedSimpArgs': 1} for name in
                             ('Itasca/Support/Translation.lean', 'SpecExt/Host.lean')})

    def test_missing_trace_is_reported(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'SpecExt').mkdir()
            (root / 'SpecExt/Host.lean').write_text('')
            self.assertEqual(collect(root), ({}, ['SpecExt/Host.lean']))

    def test_decreases_cannot_hide_new_category_or_new_module(self):
        baseline = {'old': {'unusedSimpArgs': 20}}
        self.assertEqual(increases({'old': {'unusedSimpArgs': 19}}, baseline), [])
        self.assertEqual(len(increases({'old': {'unusedSimpArgs': 1, 'other': 1}}, baseline)), 1)
        self.assertEqual(len(increases({'new': {'other': 1}}, baseline)), 1)
