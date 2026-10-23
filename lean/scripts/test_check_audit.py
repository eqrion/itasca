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
        self.put('Exec.Spec.Steps', 'import «wasm2.0»\n')
        self.put('Exec.Abs.State', 'import Exec.Spec.Steps\n')
        with self.assertRaisesRegex(ValueError, 'sink modules'):
            self.check('Exec')
        self.refresh('Exec')
        self.check('Exec')
        before = (self.root / 'Exec/Audit.lean').read_text()
        self.refresh('Exec')
        self.assertEqual(before, (self.root / 'Exec/Audit.lean').read_text())
        self.assertEqual(audit.sinks(audit.load(self.root, 'Exec'), 'Exec'), ['Exec.Abs.State'])

    def test_disconnected_cycle_is_not_coverage(self):
        self.put('Exec.Spec.A', 'import Exec.Spec.B\n')
        self.put('Exec.Spec.B', 'import Exec.Spec.A\n')
        with self.assertRaisesRegex(ValueError, 'Modules outside Exec.Audit'):
            self.check('Exec')

    def test_validator_cannot_import_execution_or_extensions(self):
        for dependency in ['Exec.Spec.A', 'SpecExt.Builtins.Int']:
            with self.subTest(dependency=dependency):
                self.put(dependency, '')
                self.put('Itasca.Examples.A', f'import {dependency}\n')
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

    def test_execution_results_and_examples_stay_on_top(self):
        for source, dependency, message in [
            ('Exec.Contracts', 'Exec.Platform.Alloc', None),
            ('Exec.Contracts', 'Exec.Theorems.Api.ExecutableInv', None),
            ('Exec.Results.Invoke', 'Exec.Theorems.Invocation.A', None),
            ('Exec.Results.Invoke', 'Exec.Contracts', None),
            ('Exec.Main', 'Exec.Results.Invoke', None),
            ('Exec.Examples.Host.A', 'Exec.Main', None),
            ('Exec.Examples.Host.B', 'Exec.Examples.Host.A', None),
            ('Exec.Examples.Host.B', 'Aeneas', None),
            ('Exec.Theorems.Invocation.A', 'Exec.Results.Invoke', 'only Main and Examples'),
            ('Exec.Theorems.Invocation.A', 'Exec.Main', 'only Main and Examples'),
            ('Exec.Results.Host', 'Exec.Results.Invoke', 'only Main and Examples'),
            ('Exec.Contracts', 'Exec.Theorems.Invocation.A', 'outside the Exec.Contracts'),
            ('Exec.Contracts', 'Exec.Code.Module.A', 'outside the Exec.Contracts'),
            ('Exec.Main', 'Exec.Theorems.Invocation.A', 'outside the Exec.Main'),
            ('Exec.Examples.Host.A', 'Exec.Theorems.Host.A', 'examples import only Exec.Main'),
        ]:
            with self.subTest(source=source, dependency=dependency):
                if message is None:
                    audit.check_layer(source, dependency, 'Exec')
                else:
                    with self.assertRaisesRegex(ValueError, message):
                        audit.check_layer(source, dependency, 'Exec')

    def test_execution_layers(self):
        for source, dependency, accepted in [
            ('Exec.Abs.State', 'Exec.Generated.Types', False),
            ('Exec.Abs.State', 'Exec.Spec.Steps', True),
            ('Exec.Spec.Steps', 'Itasca.Support.A', True),
            ('Exec.Spec.Steps', 'Itasca.Wasm2.A', False),
            ('Exec.Interp.Loop', 'Exec.Representation.StoreInvariant', True),
            ('Exec.Interp.Relations.Rel', 'Exec.Representation.Store', True),
            ('Exec.Interp.Relations.Rel', 'Exec.Store.Api.Api', False),
            ('Exec.Interp.Relations.SourceValueCauses', 'Exec.Representation.StoreCapacity', True),
            ('Exec.Interp.Relations.SourceValueCauses', 'Exec.Store.CapacityDefinition.Extra', False),
            ('Exec.Interp.Relations.SourceValueCauses', 'Exec.Store.Invariant.FunctionCapacities', False),
            ('Exec.Interp.Numeric.Float.Float', 'SpecExt.Builtins.Float.Sign', True),
            ('Exec.Interp.Numeric.Float.Float', 'SpecExt.Host', False),
            ('Exec.Interp.Relations.PrefixEffect', 'Itasca.Support.Result', True),
            ('Exec.Interp.Relations.PrefixEffect', 'Itasca.Handler.Step', False),
            ('Exec.Interp.Relations.PrefixEffect', 'Itasca.Wasm2.Soundness', False),
            ('Exec.Representation.StoreInvariant', 'Exec.Interp.Loop', False),
            ('Exec.Store.Initialization.InitializerCertificates', 'Exec.Code.Local.Initializer.InitializerComplete', True),
            ('Exec.Representation.StoreInvariant', 'Exec.Theorems.Invoke', False),
            ('Exec.Store.Initialization.PrecheckSource', 'SpecExt.Wasm1', True),
            ('Exec.Store.Initialization.PrecheckSource', 'SpecExt.Wasm1.Extra', False),
            ('Exec.Store.Initialization.PrecheckSource', 'SpecExt.Host', False),
            ('Exec.Store.Invariant.SourceStoreTyping', 'Exec.Abs.StoreTyping', True),
            ('Exec.Store.Invariant.SourceStoreTyping', 'Exec.Abs.StoreTyping.Extra', False),
            ('Exec.Spec.Wf', 'Exec.Abs.StoreTyping', False),
            ('Exec.Store.Initialization.SegmentCopySlice', 'Aeneas.Data.List.List', True),
            ('Exec.Store.Initialization.SegmentCopySlice', 'Aeneas', False),
            ('Exec.Store.Initialization.SegmentCopySlice', 'Aeneas.Data.List.List.Extra', False),
            ('Exec.Spec.SegmentCopy', 'Aeneas.Data.List.List', False),
            ('Exec.Spec.SegmentCopySlice', 'Aeneas.Data.List.List', True),
            ('Exec.Spec.SegmentCopySlice', 'Aeneas.Data.List.List.Extra', False),
            ('Exec.Spec.SegmentCopySlice', 'Aeneas', False),
            ('Exec.Spec.SegmentCopySlice', 'Exec.Representation.Store', False),
            ('Exec.Store.Initialization.InitializerResolve', 'Itasca.Module.Const.Syntax', True),
            ('Exec.Store.Initialization.InitializerResolve', 'Itasca.Module.Const.Validation', False),
            ('Exec.Store.Initialization.InitializerResolve', 'Itasca.Module.Const.Syntax.Extra', False),
            ('Exec.Store.InitializerMappings', 'Itasca.Module.Elab.SegmentSyntax', True),
            ('Exec.Store.InitializerMappings', 'Itasca.Module.Elab.Other', False),
            ('Exec.Store.InitializerMappings', 'Itasca.Module.Elab.SegmentSyntax.Extra', False),
            ('Exec.Store.Linking.LinkRawTypes', 'Itasca.Module.Elab.Metadata', True),
            ('Exec.Store.Linking.LinkRawTypes', 'Itasca.Module.Elab.Metadata.Extra', False),
            ('Exec.Store.Linking.LinkRawTypes', 'Itasca.Module.Elab.Soundness', False),
            ('Exec.Spec.ExternalMatching', 'Itasca.Module.Elab.Metadata', False),
            ('Exec.Store.LinkingContext', 'Itasca.Module.Env.Basic', True),
            ('Exec.Store.LinkingContext', 'Itasca.Module.Env.Basic.Extra', False),
            ('Exec.Store.LinkingContext', 'Itasca.Module.Env.Validation', False),
            ('Exec.Store.Invariant.FunctionTypingExtension', 'Exec.Abs.ModuleBindingsExtension', True),
            ('Exec.Store.Invariant.FunctionTypingExtension', 'Exec.Abs.ModuleBindingsExtension.Extra', False),
            ('Exec.Store.Invariant.FunctionTypingExtension', 'Exec.Abs.Sim', False),
            ('Exec.Store.Initialization.InitializerResolve', 'Itasca.Stream.Soundness', False),
            ('Exec.Platform.Float', 'SpecExt.Builtins.Int', True),
            ('Exec.Code.Local.Relations.Common.Rel', 'Itasca.Stream.A', True),
            ('Exec.Code.Local.Relations.Common.LayoutProofs', 'Exec.Platform.Alloc', True),
            ('Exec.Platform.Alloc', 'Exec.Code.Local.Relations.Common.LayoutProofs', False),
            ('Exec.Representation.Encoding', 'SpecExt.Builtins.Float.Encoding', True),
            ('Exec.Representation.Encoding', 'SpecExt.Host', False),
            ('Exec.Unknown.A', 'Lean', False),
        ]:
            with self.subTest(source=source, dependency=dependency):
                if accepted:
                    audit.check_layer(source, dependency, 'Exec')
                else:
                    with self.assertRaises(ValueError):
                        audit.check_layer(source, dependency, 'Exec')

    def test_execution_foundations_and_integration_stages(self):
        for source, dependency in [
            ('Exec.Representation.Store', 'Exec.Code.Local.Relations.A'),
            ('Exec.Representation.Store', 'Exec.Store.Api.A'),
            ('Exec.Code.Local.Relations.A', 'Exec.Code.Body.Reader.A'),
            ('Exec.Code.Body.Reader.A', 'Exec.Code.Module.A'),
            ('Exec.Interp.Relations.A', 'Exec.Interp.Invocation.A'),
            ('Exec.Store.Api.A', 'Exec.Store.Instantiation.A'),
        ]:
            with self.subTest(source=source, dependency=dependency):
                with self.assertRaises(ValueError):
                    audit.check_layer(source, dependency, 'Exec')
                audit.check_layer(dependency, source, 'Exec')

    def test_host_composition_stages(self):
        for source_stage, source_rank in audit.HOST_STAGES.items():
            for target_stage, target_rank in audit.HOST_STAGES.items():
                source = f'Exec.Theorems.Host.{source_stage}.Program'
                dependency = f'Exec.Theorems.Host.{target_stage}.Nested.Contract'
                with self.subTest(source=source, dependency=dependency):
                    if target_rank > source_rank:
                        with self.assertRaisesRegex(ValueError, 'host composition stage'):
                            audit.check_layer(source, dependency, 'Exec')
                    else:
                        audit.check_layer(source, dependency, 'Exec')
        # Atomic host proofs and callers outside this hierarchy keep their
        # existing library rules; these are not artificial integration stages.
        audit.check_layer('Exec.Theorems.Host.Callbacks.Program', 'Exec.Theorems.Host.HostResume', 'Exec')
        audit.check_layer('Exec.Theorems.Invocation.Public', 'Exec.Theorems.Host.Open.Driver.Model', 'Exec')

    def test_builtin_layers(self):
        for dependency in ['Wasm2Prefix', 'Mathlib.Data.Nat.Basic', 'SpecExt.Builtins.Bits']:
            audit.check_layer('SpecExt.Builtins.Int', dependency, 'SpecExt')
        for dependency in ['wasm2.0', 'Exec.Spec.Steps', 'Itasca.Generated.Types', 'SpecExt.Host']:
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

    def test_validator_mapping_only_in_external_adapters(self):
        for name in ['Exec.Generated.FunsExternal', 'Exec.Generated.TypesExternal']:
            audit.check_layer(name, 'Itasca.Generated.Types', 'Exec')
        with self.assertRaises(ValueError):
            audit.check_layer('Exec.Generated.Funs', 'Itasca.Generated.Funs', 'Exec')

    def test_generated_reuse_boundary_applies_to_all_execution_layers(self):
        for source in ['Exec.Representation.Store', 'Exec.Code.Local.Relations.A',
                       'Exec.Interp.Relations.A', 'Exec.Store.Api.A', 'Exec.Theorems.A']:
            with self.subTest(source=source):
                with self.assertRaises(ValueError):
                    audit.check_layer(source, 'Itasca.Generated.Types', 'Exec')

    def test_public_import_cannot_bypass_generated_boundary(self):
        for source, dependency in [
            ('Exec.Generated.Funs', 'Itasca.Generated.Types'),
            ('Exec.Generated.TypesExternal', 'Itasca.Wasm2.Soundness'),
            ('Exec.Generated.FunsExternal', 'Itasca.Stream.Soundness'),
        ]:
            with self.subTest(source=source, dependency=dependency):
                self.put(dependency, '')
                self.put(source, f'module\npublic import {dependency}\n@[expose] public section\n')
                with self.assertRaisesRegex(ValueError, 'outside the Exec.Generated layer'):
                    self.check('Exec')
                (self.root / Path(*source.split('.'))).with_suffix('.lean').unlink()

    def test_templates_are_excluded_but_cannot_be_imported(self):
        for name in ['FunsExternal_Template', 'TypesExternal_Template']:
            self.put('Exec.Generated.' + name, 'import Nonexistent\n')
            self.check('Exec')
            self.put('Exec.Generated.Funs', f'import Exec.Generated.{name}\n')
            with self.assertRaisesRegex(ValueError, 'external-model template'):
                self.check('Exec')
            (self.root / 'Exec/Generated/Funs.lean').unlink()

    def test_import_tokens_and_missing_modules(self):
        self.put('Exec.Abs.State', '/- import Exec.Generated.Types -/\npublic import Exec.Spec.Missing\n')
        with self.assertRaisesRegex(ValueError, 'missing module Exec.Spec.Missing'):
            self.check('Exec')

    def test_cross_library_audits_cannot_be_imported(self):
        self.put('Exec.Theorems.Invoke', 'import Itasca.Audit\n')
        with self.assertRaisesRegex(ValueError, 'audit entry point'):
            self.check('Exec')

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
        (self.root / 'Exec/Audit.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'Missing audit module'):
            self.check('Exec')


if __name__ == '__main__':
    unittest.main()
