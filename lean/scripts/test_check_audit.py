"""Regression tests for audit reachability, library boundaries and builtin stages."""
from contextlib import redirect_stdout
import io
from pathlib import Path
import tempfile
import unittest

import check_audit as audit


class AuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for library in audit.LIBRARIES:
            self.put(library + '.Audit', 'import Lean.Elab.Command\n')

    def put(self, name, source):
        path = (self.root / Path(*name.split('.'))).with_suffix('.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)

    def refresh(self, library):
        audit.write_audit(self.root, audit.load(self.root, library), library)

    def check(self, library):
        with redirect_stdout(io.StringIO()):
            audit.check(self.root, library)

    def test_sink_coverage_and_idempotent_write(self):
        self.put('Itasca.Runtime.Spec.Steps', 'import «wasm2.0»\n')
        self.put('Itasca.Runtime.Abs.State', 'import Itasca.Runtime.Spec.Steps\n')
        with self.assertRaisesRegex(ValueError, 'sink modules'):
            self.check('Itasca')
        self.refresh('Itasca')
        self.check('Itasca')
        before = (self.root / 'Itasca/Audit.lean').read_text()
        self.refresh('Itasca')
        self.assertEqual(before, (self.root / 'Itasca/Audit.lean').read_text())
        self.assertEqual(audit.sinks(audit.load(self.root, 'Itasca'), 'Itasca'), ['Itasca.Runtime.Abs.State'])

    def test_disconnected_cycle_is_not_coverage(self):
        self.put('Itasca.Runtime.Spec.A', 'import Itasca.Runtime.Spec.B\n')
        self.put('Itasca.Runtime.Spec.B', 'import Itasca.Runtime.Spec.A\n')
        with self.assertRaisesRegex(ValueError, 'Modules outside Itasca.Audit'):
            self.check('Itasca')

    def test_validator_cannot_import_runtime_or_extensions(self):
        for dependency in ['Itasca.Runtime.Spec.A', 'SpecExt.Builtins.Int']:
            with self.subTest(dependency=dependency):
                self.put(dependency, '')
                self.put('Itasca.Stream.A', f'import {dependency}\n')
                with self.assertRaisesRegex(ValueError, 'validator imports must stay independent'):
                    self.check('Itasca')

    def test_original_validator_layers_still_enforced(self):
        self.put('Itasca.Wasm2.A', '')
        self.put('Itasca.Binary.A', 'import Itasca.Wasm2.A\n')
        with self.assertRaisesRegex(ValueError, 'above the Binary'):
            self.check('Itasca')

    def test_headline_results_and_examples_stay_on_top(self):
        self.put('Itasca.Contracts', '')
        self.put('Itasca.Results.A', 'import Itasca.Contracts\n')
        self.put('Itasca.Main', 'import Itasca.Results.A\n')
        self.put('Itasca.Examples.A', 'import Itasca.Main\n')
        self.put('Itasca.Examples.B', 'import Itasca.Examples.A\nimport Aeneas\n')
        self.refresh('Itasca')
        self.check('Itasca')
        for source, dependency, message in [
            ('Itasca.Stream.A', 'Itasca.Results.A', 'only Main and Examples'),
            ('Itasca.Results.B', 'Itasca.Main', 'only Main and Examples'),
            ('Itasca.Contracts', 'Itasca.Stream.A', 'above the Contracts'),
            ('Itasca.Main', 'Itasca.Stream.A', 'above the Main'),
            ('Itasca.Examples.C', 'Itasca.Stream.A', 'examples import only Itasca.Main'),
        ]:
            with self.subTest(source=source, dependency=dependency):
                with self.assertRaisesRegex(ValueError, message):
                    audit.check_layer(source, dependency, 'Itasca')
        for source, dependency in audit.EXAMPLE_IMPORTS:
            audit.check_layer(source, dependency, source.split('.')[0])

    def test_runtime_results_and_examples_stay_on_top(self):
        for source, dependency, message in [
            ('Itasca.Runtime.Contracts', 'Itasca.Runtime.Platform.Alloc', None),
            ('Itasca.Runtime.Contracts', 'Itasca.Runtime.Theorems.Api.ExecutableInv', None),
            ('Itasca.Results.Invoke', 'Itasca.Runtime.Theorems.Invocation.A', None),
            ('Itasca.Results.Invoke', 'Itasca.Runtime.Contracts', None),
            ('Itasca.Main', 'Itasca.Results.Invoke', None),
            ('Itasca.Examples.Host.A', 'Itasca.Main', None),
            ('Itasca.Examples.Host.B', 'Itasca.Examples.Host.A', None),
            ('Itasca.Examples.Host.B', 'Aeneas', None),
            ('Itasca.Runtime.Theorems.Invocation.A', 'Itasca.Results.Invoke', 'only Main and Examples'),
            ('Itasca.Runtime.Theorems.Invocation.A', 'Itasca.Main', 'only Main and Examples'),
            ('Itasca.Results.Host', 'Itasca.Results.Invoke', 'only Main and Examples'),
            ('Itasca.Runtime.Contracts', 'Itasca.Runtime.Theorems.Invocation.A', 'outside the Itasca.Runtime.Contracts'),
            ('Itasca.Runtime.Contracts', 'Itasca.Runtime.Code.Module.A', 'outside the Itasca.Runtime.Contracts'),
            ('Itasca.Main', 'Itasca.Runtime.Theorems.Invocation.A', 'above the Main'),
            ('Itasca.Examples.Host.A', 'Itasca.Runtime.Theorems.Host.A', 'examples import only Itasca.Main'),
        ]:
            with self.subTest(source=source, dependency=dependency):
                if message is None:
                    audit.check_layer(source, dependency, 'Itasca')
                else:
                    with self.assertRaisesRegex(ValueError, message):
                        audit.check_layer(source, dependency, 'Itasca')

    def test_runtime_layers(self):
        for source, dependency, accepted in [
            ('Itasca.Runtime.Abs.State', 'Itasca.Runtime.Generated.Types', False),
            ('Itasca.Runtime.Abs.State', 'Itasca.Runtime.Spec.Steps', True),
            ('Itasca.Runtime.Spec.Steps', 'Itasca.Support.A', True),
            ('Itasca.Runtime.Spec.Steps', 'Itasca.Wasm2.A', False),
            ('Itasca.Runtime.Interp.Loop', 'Itasca.Runtime.Representation.StoreInvariant', True),
            ('Itasca.Runtime.Interp.Relations.Rel', 'Itasca.Runtime.Representation.Store', True),
            ('Itasca.Runtime.Interp.Relations.Rel', 'Itasca.Runtime.Store.Api.Api', False),
            ('Itasca.Runtime.Interp.Relations.SourceValueCauses', 'Itasca.Runtime.Representation.StoreCapacity', True),
            ('Itasca.Runtime.Interp.Relations.SourceValueCauses', 'Itasca.Runtime.Store.CapacityDefinition.Extra', False),
            ('Itasca.Runtime.Interp.Relations.SourceValueCauses', 'Itasca.Runtime.Store.Invariant.FunctionCapacities', False),
            ('Itasca.Runtime.Interp.Numeric.Float.Float', 'SpecExt.Builtins.Float.Sign', True),
            ('Itasca.Runtime.Interp.Numeric.Float.Float', 'SpecExt.Host', False),
            ('Itasca.Runtime.Interp.Relations.PrefixEffect', 'Itasca.Support.Result', True),
            ('Itasca.Runtime.Interp.Relations.PrefixEffect', 'Itasca.Handler.Step', False),
            ('Itasca.Runtime.Interp.Relations.PrefixEffect', 'Itasca.Wasm2.Soundness', False),
            ('Itasca.Runtime.Representation.StoreInvariant', 'Itasca.Runtime.Interp.Loop', False),
            ('Itasca.Runtime.Store.Initialization.InitializerCertificates', 'Itasca.Runtime.Code.Local.Initializer.InitializerComplete', True),
            ('Itasca.Runtime.Representation.StoreInvariant', 'Itasca.Runtime.Theorems.Invoke', False),
            ('Itasca.Runtime.Store.Initialization.PrecheckSource', 'SpecExt.Wasm1', True),
            ('Itasca.Runtime.Store.Initialization.PrecheckSource', 'SpecExt.Wasm1.Extra', False),
            ('Itasca.Runtime.Store.Initialization.PrecheckSource', 'SpecExt.Host', False),
            ('Itasca.Runtime.Store.Invariant.SourceStoreTyping', 'Itasca.Runtime.Abs.StoreTyping', True),
            ('Itasca.Runtime.Store.Invariant.SourceStoreTyping', 'Itasca.Runtime.Abs.StoreTyping.Extra', False),
            ('Itasca.Runtime.Spec.Wf', 'Itasca.Runtime.Abs.StoreTyping', False),
            ('Itasca.Runtime.Store.Initialization.SegmentCopySlice', 'Aeneas.Data.List.List', True),
            ('Itasca.Runtime.Store.Initialization.SegmentCopySlice', 'Aeneas', False),
            ('Itasca.Runtime.Store.Initialization.SegmentCopySlice', 'Aeneas.Data.List.List.Extra', False),
            ('Itasca.Runtime.Spec.SegmentCopy', 'Aeneas.Data.List.List', False),
            ('Itasca.Runtime.Spec.SegmentCopySlice', 'Aeneas.Data.List.List', True),
            ('Itasca.Runtime.Spec.SegmentCopySlice', 'Aeneas.Data.List.List.Extra', False),
            ('Itasca.Runtime.Spec.SegmentCopySlice', 'Aeneas', False),
            ('Itasca.Runtime.Spec.SegmentCopySlice', 'Itasca.Runtime.Representation.Store', False),
            ('Itasca.Runtime.Store.Initialization.InitializerResolve', 'Itasca.Module.Const.Syntax', True),
            ('Itasca.Runtime.Store.Initialization.InitializerResolve', 'Itasca.Module.Const.Validation', False),
            ('Itasca.Runtime.Store.Initialization.InitializerResolve', 'Itasca.Module.Const.Syntax.Extra', False),
            ('Itasca.Runtime.Store.InitializerMappings', 'Itasca.Module.Elab.SegmentSyntax', True),
            ('Itasca.Runtime.Store.InitializerMappings', 'Itasca.Module.Elab.Other', False),
            ('Itasca.Runtime.Store.InitializerMappings', 'Itasca.Module.Elab.SegmentSyntax.Extra', False),
            ('Itasca.Runtime.Store.Linking.LinkRawTypes', 'Itasca.Module.Elab.Metadata', True),
            ('Itasca.Runtime.Store.Linking.LinkRawTypes', 'Itasca.Module.Elab.Metadata.Extra', False),
            ('Itasca.Runtime.Store.Linking.LinkRawTypes', 'Itasca.Module.Elab.Soundness', False),
            ('Itasca.Runtime.Spec.ExternalMatching', 'Itasca.Module.Elab.Metadata', False),
            ('Itasca.Runtime.Store.LinkingContext', 'Itasca.Module.Env.Basic', True),
            ('Itasca.Runtime.Store.LinkingContext', 'Itasca.Module.Env.Basic.Extra', False),
            ('Itasca.Runtime.Store.LinkingContext', 'Itasca.Module.Env.Validation', False),
            ('Itasca.Runtime.Store.Invariant.FunctionTypingExtension', 'Itasca.Runtime.Abs.ModuleBindingsExtension', True),
            ('Itasca.Runtime.Store.Invariant.FunctionTypingExtension', 'Itasca.Runtime.Abs.ModuleBindingsExtension.Extra', False),
            ('Itasca.Runtime.Store.Invariant.FunctionTypingExtension', 'Itasca.Runtime.Abs.Sim', False),
            ('Itasca.Runtime.Store.Initialization.InitializerResolve', 'Itasca.Stream.Soundness', False),
            ('Itasca.Runtime.Platform.Float', 'SpecExt.Builtins.Int', True),
            ('Itasca.Runtime.Code.Local.Relations.Common.Rel', 'Itasca.Stream.A', True),
            ('Itasca.Runtime.Code.Local.Relations.Common.LayoutProofs', 'Itasca.Runtime.Platform.Alloc', True),
            ('Itasca.Runtime.Platform.Alloc', 'Itasca.Runtime.Code.Local.Relations.Common.LayoutProofs', False),
            ('Itasca.Runtime.Representation.Encoding', 'SpecExt.Builtins.Float.Encoding', True),
            ('Itasca.Runtime.Representation.Encoding', 'SpecExt.Host', False),
            ('Itasca.Runtime.Unknown.A', 'Lean', False),
        ]:
            with self.subTest(source=source, dependency=dependency):
                if accepted:
                    audit.check_layer(source, dependency, 'Itasca')
                else:
                    with self.assertRaises(ValueError):
                        audit.check_layer(source, dependency, 'Itasca')

    def test_runtime_foundations_and_integration_stages(self):
        for source, dependency in [
            ('Itasca.Runtime.Representation.Store', 'Itasca.Runtime.Code.Local.Relations.A'),
            ('Itasca.Runtime.Representation.Store', 'Itasca.Runtime.Store.Api.A'),
            ('Itasca.Runtime.Code.Local.Relations.A', 'Itasca.Runtime.Code.Body.Reader.A'),
            ('Itasca.Runtime.Code.Body.Reader.A', 'Itasca.Runtime.Code.Module.A'),
            ('Itasca.Runtime.Interp.Relations.A', 'Itasca.Runtime.Interp.Invocation.A'),
            ('Itasca.Runtime.Store.Api.A', 'Itasca.Runtime.Store.Instantiation.A'),
        ]:
            with self.subTest(source=source, dependency=dependency):
                with self.assertRaises(ValueError):
                    audit.check_layer(source, dependency, 'Itasca')
                audit.check_layer(dependency, source, 'Itasca')

    def test_builtin_layers(self):
        for dependency in ['Wasm2Prefix', 'Mathlib.Data.Nat.Basic', 'SpecExt.Builtins.Bits']:
            audit.check_layer('SpecExt.Builtins.Int', dependency, 'SpecExt')
        for dependency in ['wasm2.0', 'Itasca.Runtime.Spec.Steps', 'Itasca.Generated.Types', 'SpecExt.Host']:
            with self.assertRaises(ValueError):
                audit.check_layer('SpecExt.Builtins.Int', dependency, 'SpecExt')

    def builtin_review(self, signatures, reviewed, suffix=''):
        self.put('SpecTec.Wasm2Builtins', '\n'.join(
            f'example : Nat := @{name}' for name in signatures))
        self.put('SpecExt.Builtins.Inventory', 'def inventory := [\n' + ',\n'.join(
            f'  ⟨``{name}, .storage, .deterministic, .storageWidths⟩' for name in reviewed)
            + '\n]\ntheorem inventory_count : True := by trivial\n' + suffix)

    def test_builtin_review_exact_coverage(self):
        self.builtin_review(['ibytes_', 'fbytes_'], ['fbytes_', 'ibytes_'])
        audit.check_builtin_inventory(self.root)

    def test_builtin_review_rejects_missing_extra_and_duplicate_symbols(self):
        for reviewed, message in [(['ibytes_'], 'missing'),
                                  (['ibytes_', 'fbytes_', 'other'], 'extra'),
                                  (['ibytes_', 'fbytes_', 'ibytes_'], 'Duplicate')]:
            with self.subTest(reviewed=reviewed):
                self.builtin_review(['ibytes_', 'fbytes_'], reviewed)
                with self.assertRaisesRegex(ValueError, message):
                    audit.check_builtin_inventory(self.root)

    def test_builtin_review_ignores_comments_strings_and_later_quotations(self):
        self.builtin_review(['ibytes_', 'fbytes_'], ['ibytes_'],
                            '-- ``fbytes_\ndef later := ``fbytes_\n')
        path = self.root / 'SpecExt/Builtins/Inventory.lean'
        path.write_text(path.read_text().replace('def inventory := [',
                        '/- def inventory := [``fbytes_] -/\ndef decoy := "``fbytes_"\ndef inventory := ['))
        with self.assertRaisesRegex(ValueError, 'missing'):
            audit.check_builtin_inventory(self.root)

    def test_builtin_review_rejects_invalid_generated_symbol_sets(self):
        for signatures in [[], ['ibytes_', 'ibytes_']]:
            with self.subTest(signatures=signatures):
                self.builtin_review(signatures, ['ibytes_'])
                with self.assertRaisesRegex(ValueError, 'distinct builtin symbols'):
                    audit.check_builtin_inventory(self.root)

    def test_generated_functions_only_through_equations(self):
        audit.check_layer('Itasca.Runtime.Equations', 'Itasca.Generated.Funs', 'Itasca')
        for source in ['Itasca.Runtime.Representation.Store', 'Itasca.Runtime.Interp.Relations.A', 'Itasca.Runtime.Store.Api.A']:
            with self.subTest(source=source):
                audit.check_layer(source, 'Itasca.Generated.Types', 'Itasca')
                with self.assertRaisesRegex(ValueError, 'import Itasca.Runtime.Equations'):
                    audit.check_layer(source, 'Itasca.Generated.Funs', 'Itasca')
        with self.assertRaises(ValueError):
            audit.check_layer('Itasca.Runtime.Abs.State', 'Itasca.Generated.Types', 'Itasca')

    def test_public_import_cannot_bypass_generated_boundary(self):
        source, dependency = 'Itasca.Runtime.Equations', 'Itasca.Wasm2.Soundness'
        self.put(dependency, '')
        self.put(source, f'module\npublic import {dependency}\n@[expose] public section\n')
        with self.assertRaisesRegex(ValueError, 'outside the Itasca.Runtime.Equations layer'):
            self.check('Itasca')

    def test_templates_are_excluded_but_cannot_be_imported(self):
        for name in ['FunsExternal_Template', 'TypesExternal_Template']:
            self.put('Itasca.Generated.' + name, 'import Nonexistent\n')
            self.check('Itasca')
            self.put('Itasca.Generated.Funs', f'import Itasca.Generated.{name}\n')
            with self.assertRaisesRegex(ValueError, 'external-model template'):
                self.check('Itasca')
            (self.root / 'Itasca/Generated/Funs.lean').unlink()

    def test_import_tokens_and_missing_modules(self):
        self.put('Itasca.Runtime.Abs.State', '/- import Itasca.Runtime.Generated.Types -/\npublic import Itasca.Runtime.Spec.Missing\n')
        with self.assertRaisesRegex(ValueError, 'missing module Itasca.Runtime.Spec.Missing'):
            self.check('Itasca')

    def test_cross_library_audits_cannot_be_imported(self):
        self.put('Itasca.Runtime.Theorems.Invoke', 'import SpecExt.Audit\n')
        with self.assertRaisesRegex(ValueError, 'audit entry point'):
            self.check('Itasca')

    def test_builtin_stages_ignore_comments_and_strings(self):
        self.put('SpecExt.Builtins.Int', '/- opaque fake : Nat -/\ndef s := "opaque fake"\nopaque iand_ : Nat := 0\n')
        audit.check_builtins(self.root, 'placeholders')
        for stage in ['lanes', 'complete']:
            with self.assertRaisesRegex(ValueError, 'opaque builtin iand_'):
                audit.check_builtins(self.root, stage)
        self.put('SpecExt.Builtins.Int', '/- opaque fake -/\ndef s := "opaque fake"\n')
        self.put('SpecExt.Builtins.Lanes', 'opaque lanes_ : Nat := 0\nopaque inv_lanes_ : Nat := 0\n')
        audit.check_builtins(self.root, 'lanes')
        with self.assertRaisesRegex(ValueError, 'opaque builtin lanes_'):
            audit.check_builtins(self.root, 'complete')
        self.put('SpecExt.Builtins.Lanes', 'def lanes_ : Nat := 0\n')
        audit.check_builtins(self.root, 'complete')

    def test_missing_audit_fails_closed(self):
        (self.root / 'Itasca/Audit.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'Missing audit module'):
            self.check('Itasca')


if __name__ == '__main__':
    unittest.main()
