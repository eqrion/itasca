from pathlib import Path
import tempfile
import unittest
from audit_environment import discover_handwritten_modules, audit_source


class AuditDiscoveryTests(unittest.TestCase):
    def test_new_results_module_is_imported_without_main_edit(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'scripts').mkdir()
            (root / 'scripts/Audit.lean').write_text('import Itasca.Main\n#include_marker\n')
            (root / 'Itasca/Results/Nested').mkdir(parents=True)
            (root / 'Itasca/Results/Existing.lean').write_text('theorem existing : True := True.intro')
            (root / 'Itasca/Results/Nested/New.lean').write_text('theorem unfamiliar : True := True.intro')
            self.assertEqual(discover_handwritten_modules(root),
                             ['Itasca.Results.Existing', 'Itasca.Results.Nested.New'])
            self.assertIn('import Itasca.Results.Nested.New', audit_source(root))

    def test_only_lean_sources_form_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Itasca/Results').mkdir(parents=True)
            (root / 'Itasca/Results/README.md').write_text('not a module')
            self.assertEqual(discover_handwritten_modules(root), [])

    def test_unused_implementation_examples_and_extensions_are_imported(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'scripts').mkdir()
            (root / 'scripts/Audit.lean').write_text('import Itasca.Main\n')
            modules = ['Itasca/Runtime/Unused', 'Itasca/Examples/Unused',
                       'Itasca/Results/Definitions/Unused', 'SpecExt/Unused']
            for module in [*modules, 'Itasca/Generated/Excluded']:
                path = root / (module + '.lean')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('')
            source = audit_source(root)
            for module in modules:
                self.assertIn('import ' + module.replace('/', '.'), source)
            self.assertNotIn('import Itasca.Generated.Excluded', source)
            self.assertEqual(source.count('import Itasca.Main'), 1)
