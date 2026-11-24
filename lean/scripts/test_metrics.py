import json
import os
import tempfile
import unittest

from metrics import (explicit_tactic_items, extracted_definitions,
                     extracted_tactic_definitions,
                     ratchet_values, short_module_exemptions, interface_line_accounting)


class InterfaceOriginTests(unittest.TestCase):
    def test_semantic_sections_preserve_cross_area_attribution(self):
        module = "Itasca.Results.Definitions.Semantics"
        source = "import Aeneas\nsection Bytes\na\nend Bytes\nsection Compiler\nb\nend Compiler\n"
        rows = [
            {"source_module": "Itasca.Binary.Encoding", "destination_module": module,
             "destination_section": "Bytes"},
            {"source_module": "Itasca.Runtime.Compiler.Local.X", "destination_module": module,
             "destination_section": "Compiler"}]
        origins, areas = interface_line_accounting({module.replace('.', '/') + '.lean': source}, rows)
        self.assertEqual(areas, {"validator": 3, "compiler": 3})
        self.assertEqual(origins["_entrypoints"], 1)
        self.assertEqual(sum(origins.values()), source.count("\n"))
        with self.assertRaisesRegex(ValueError, "mixed whole-module"):
            interface_line_accounting({module.replace('.', '/') + '.lean': source},
                                      rows + [{"source_module": "Itasca.Binary.X", "destination_module": module}])
        rows[1]["destination_section"] = "Missing"
        with self.assertRaisesRegex(ValueError, "invalid Interface section"):
            interface_line_accounting({module.replace('.', '/') + '.lean': source}, rows)

    def test_relocated_compiler_lines_keep_origin_and_subjects_separate(self):
        origin, area = interface_line_accounting({
            "Itasca/Results/Definitions/Compiler/Local/X.lean": "a\nb\n",
            "Itasca/Results/Definitions/Compilation.lean": "import X\n",
        }, [{"source_module": "Itasca.Runtime.Compiler.Local.X",
             "destination_module": "Itasca.Results.Definitions.Compiler.Local.X"},
            {"source_module": "", "destination_module": "Itasca.Results.Definitions.Compilation"}])
        self.assertEqual(origin, {"Itasca.Runtime.Compiler.Local.X": 2, "_entrypoints": 1})
        self.assertEqual(area, {"compiler": 2})

    def test_consolidated_origins_keep_both_labels_and_count_area_once(self):
        destination = "Itasca.Results.Definitions.Binary.ScalarEncoding"
        sources = {destination.replace('.', '/') + '.lean': "a\nb\n"}
        migrations = [{"source_module": origin, "destination_module": destination}
                      for origin in ["Itasca.Binary.SignedLeb32", "Itasca.Binary.SignedLeb64"]]
        origins, areas = interface_line_accounting(sources, migrations)
        self.assertEqual(origins, {"Itasca.Binary.SignedLeb32 + Itasca.Binary.SignedLeb64": 2})
        self.assertEqual(areas, {"validator": 2})
        migrations[1]['source_module'] = "Itasca.Runtime.Compiler.Local.X"
        with self.assertRaisesRegex(ValueError, "ambiguous Interface origin"):
            interface_line_accounting(sources, migrations)

    def test_unregistered_interface_lines_remain_visible(self):
        origin, area = interface_line_accounting({"Itasca/Results/Definitions/New.lean": "x\n"}, [])
        self.assertEqual(origin, {"_unregistered": 1})
        self.assertEqual(area, {})

    def test_consolidated_integration_origins_have_no_rust_ratio(self):
        destination = 'Itasca.Results.Definitions.Integration.Invocation.Outcomes'
        sources = {destination.replace('.', '/') + '.lean': 'a\nb\n'}
        owners = ['Itasca.Runtime.Integration.Execution.Resources.InvocationErrors',
                  'Itasca.Runtime.Integration.Invocation.Outcomes']
        migrations = [{'source_module': owner, 'destination_module': destination}
                      for owner in owners]
        origins, areas = interface_line_accounting(sources, migrations)
        self.assertEqual(origins, {' + '.join(owners): 2})
        self.assertEqual(areas, {})
        # Distinct unmeasured subjects must not silently collapse together.
        migrations[1]['source_module'] = 'Itasca.Runtime.SourceMachine.State'
        with self.assertRaisesRegex(ValueError, 'ambiguous Interface origin'):
            interface_line_accounting(sources, migrations)

    def test_renamed_validator_owners_keep_historical_line_attribution(self):
        sources, migrations = {}, []
        for old, new in (('Wasm1', 'Scalar'), ('Wasm2', 'Body'), ('Profile', 'CodeEntry')):
            destination = f'Itasca.Results.Definitions.{new}.X'
            sources[destination.replace('.', '/') + '.lean'] = 'definition\n'
            migrations.append({'source_module': f'Itasca.{old}.X',
                               'destination_module': destination})
        origins, areas = interface_line_accounting(sources, migrations)
        self.assertEqual(areas, {'validator': 3})
        self.assertEqual(set(origins), {'Itasca.Wasm1.X', 'Itasca.Wasm2.X', 'Itasca.Profile.X'})


class ExplicitTacticItemsTests(unittest.TestCase):
    def test_counts_actual_simp_and_unfold_definitions(self):
        source = '''
        simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor,
          runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const.eq,
          lift, bind_ok]
        unfold runtime.compiler.lower.FunctionCompiler.op at called
        '''
        self.assertEqual(list(explicit_tactic_items(source)), [
            ('simp', (
                'runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor',
                'runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_i32_const.eq',
                'lift', 'bind_ok')),
            ('unfold', ('runtime.compiler.lower.FunctionCompiler.op',)),
        ])

    def test_extracted_multiline_definition_headers(self):
        source = """def
  runtime.compiler.CompileScheduler.compile_entry (x : Nat) : Nat := x
noncomputable def
  runtime.compiler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop := 0
"""
        extracted = extracted_definitions(source)
        self.assertEqual(extracted, {
            "runtime.compiler.CompileScheduler.compile_entry",
            "runtime.compiler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop",
        })
        tactic = "simp only [runtime.compiler.CompileScheduler.compile_entry, runtime.compiler.Insts.ItascaStreamStreamingVisitor.submit_code_batch_loop]"
        self.assertEqual(set(extracted_tactic_definitions(tactic, extracted)), extracted)

    def test_metrics_keep_real_heads_but_ignore_extracted_argument_defs(self):
        source = 'simp only [runtime.direct, wrapper (runtime.argument)]'
        extracted = {'runtime.direct', 'wrapper', 'runtime.argument'}
        self.assertEqual(set(extracted_tactic_definitions(source, extracted)),
                         {'runtime.direct', 'wrapper'})

    def test_parameterized_lemma_arguments_are_not_definition_sites(self):
        visitor = 'runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor'
        source = f'''simp only [tableBody_eq ({visitor} ops) data env count,
          dispatch_numeric ({visitor} ops) st data env]'''
        self.assertEqual(list(explicit_tactic_items(source)), [
            ('simp', ('tableBody_eq', 'dispatch_numeric')),
        ])

    def test_backward_rewrite_prefix_is_removed_before_head_detection(self):
        source = 'rw [← runtime.before, → runtime.after] at hypothesis'
        self.assertEqual(list(explicit_tactic_items(source)), [
            ('rw', ('runtime.before', 'runtime.after')),
        ])

    def test_multiline_nested_lists_split_only_at_top_level(self):
        source = '''simpa only [
          runtime.outer (runtime.argument,
            [runtime.nested_argument, runtime.another_argument]),
          runtime.second (by
            simp only [runtime.inner, runtime.inner₂])]
        '''
        self.assertEqual(list(explicit_tactic_items(source)), [
            ('simpa', ('runtime.outer', 'runtime.second')),
            ('simp', ('runtime.inner', 'runtime.inner₂')),
        ])

    def test_delta_uses_standalone_whitespace_targets(self):
        source = 'by delta runtime.first runtime.second at hypothesis'
        self.assertEqual(list(explicit_tactic_items(source)), [
            ('delta', ('runtime.first', 'runtime.second')),
        ])

    def test_delta_term_identifier_is_not_an_unfold_site(self):
        source = 'def ordinary (delta : Nat) : Nat := delta + 1\\n'
        self.assertEqual(list(explicit_tactic_items(source)), [])

    def test_unfold_names_form_a_separate_whitespace_list(self):
        source = '''unfold runtime.first runtime.second at runtime.target
        simp only [runtime.third]
        '''
        self.assertEqual(list(explicit_tactic_items(source)), [
            ('unfold', ('runtime.first', 'runtime.second')),
            ('simp', ('runtime.third',)),
        ])



class ShortModuleLedgerTests(unittest.TestCase):
    def test_short_module_ratchet_keeps_old_baseline_and_uses_adjusted_when_present(self):
        current = {
            "modules_under_50_lines": 57,
            "modules_under_50_lines_after_structural_exemptions": 55,
        }
        self.assertEqual(ratchet_values("modules_under_50_lines", current,
                                        {"modules_under_50_lines": 52}), (52, 55))
        self.assertEqual(ratchet_values("modules_under_50_lines", current,
                                        {"modules_under_50_lines": 52,
                                         "modules_under_50_lines_after_structural_exemptions": 51}),
                         (51, 55))

    def test_empty_ledger_and_exact_valid_entry(self):
        src = {"Itasca/Small.lean": "line\n"}
        with tempfile.TemporaryDirectory() as directory:
            ledger = os.path.join(directory, "ledger.json")
            with open(ledger, "w") as out:
                json.dump([], out)
            self.assertEqual(short_module_exemptions(src, [1], ledger), ([], []))
            with open(ledger, "w") as out:
                json.dump([{"path": "Itasca/Small.lean", "reason": "definition split"}], out)
            self.assertTrue(any("absent from migration manifest" in error
                                for error in short_module_exemptions(src, [1], ledger)[1]))

    def test_manifest_provenance_allows_interface_or_split_paths_only(self):
        src = {"Itasca/Results/Definitions/X.lean": "line\n",
               "Itasca/Small.lean": "line\n"}
        with tempfile.TemporaryDirectory() as directory:
            ledger = os.path.join(directory, "ledger.json")
            manifest = os.path.join(directory, "manifest.tsv")
            with open(manifest, "w") as out:
                out.write("source_module\tdeclaration\tdestination_module\n")
                out.write("Itasca.Other\tItasca.Other.Def\tItasca.Results.Definitions.X\n")
            with open(ledger, "w") as out:
                json.dump([{"path": "Itasca/Results/Definitions/X.lean", "reason": "isolates public definition"}], out)
            self.assertEqual(short_module_exemptions(src, [1, 1], ledger, manifest),
                             (["Itasca/Results/Definitions/X.lean"], []))
            with open(ledger, "w") as out:
                json.dump([{"path": "Itasca/Small.lean", "reason": "arbitrary reason"}], out)
            exemptions, errors = short_module_exemptions(src, [1, 1], ledger, manifest)
            self.assertEqual(exemptions, [])
            self.assertTrue(any("absent from migration manifest" in error for error in errors))

    def test_renamed_split_owner_retains_historical_origin(self):
        src = {"Itasca/Renamed.lean": "line\n"}
        with tempfile.TemporaryDirectory() as directory:
            ledger = os.path.join(directory, "ledger.json")
            manifest = os.path.join(directory, "manifest.tsv")
            with open(manifest, "w") as out:
                out.write("source_module\tdestination_module\tcurrent_source_module\n")
                out.write("Itasca.Old\tItasca.Results.Definitions.X\tItasca.Renamed\n")
            with open(ledger, "w") as out:
                json.dump([{"path": "Itasca/Renamed.lean", "reason": "residual split owner"}], out)
            self.assertEqual(short_module_exemptions(src, [1], ledger, manifest),
                             (["Itasca/Renamed.lean"], []))
        accounting = interface_line_accounting(
            {"Itasca/Results/Definitions/X.lean": "line\n"},
            [{"source_module": "Itasca.Old", "current_source_module": "Itasca.Renamed",
              "destination_module": "Itasca.Results.Definitions.X"}])
        self.assertEqual(accounting[0], {"Itasca.Old": 1})

    def test_ledger_rejects_pattern_and_missing_paths(self):
        src = {"Itasca/Small.lean": "line\n"}
        with tempfile.TemporaryDirectory() as directory:
            ledger = os.path.join(directory, "ledger.json")
            with open(ledger, "w") as out:
                json.dump([{"path": "Itasca/*.lean", "reason": "too broad"}], out)
            _, errors = short_module_exemptions(src, [1], ledger)
            self.assertTrue(any("exact paths" in error for error in errors))
            with open(ledger, "w") as out:
                json.dump([{"path": "Itasca/Missing.lean", "reason": "stale"}], out)
            _, errors = short_module_exemptions(src, [1], ledger)
            self.assertTrue(any("not a handwritten module" in error for error in errors))

    def test_comments_and_strings_are_not_tactic_sites(self):
        source = '''
        -- simp only [runtime.line_comment]
        /- unfold runtime.block_comment
           /- simp [runtime.nested_comment] -/ -/
        let s := "simp only [runtime.string_contents]"
        simp [runtime.real_definition]
        '''
        self.assertEqual(list(explicit_tactic_items(source)), [
            ('simp', ('runtime.real_definition',)),
        ])

    def test_negative_simp_modifier_is_not_an_unfold_site(self):
        source = 'simp only [(← runtime.backward), -runtime.removed, +runtime.added]'
        self.assertEqual(list(explicit_tactic_items(source)), [
            ('simp', ('runtime.backward', 'runtime.added')),
        ])

    def test_simp_and_dsimp_config_syntax(self):
        source = '''simp (config := { zeta := true }) only [runtime.first]
        dsimp (config := { proj := true }) [runtime.second]'''
        self.assertEqual(list(explicit_tactic_items(source)), [
            ('simp', ('runtime.first',)),
            ('dsimp', ('runtime.second',)),
        ])

    def test_multiline_unfold_stops_before_the_next_tactic(self):
        source = '''unfold
          runtime.first
          runtime.second
          simp only [runtime.next_tactic]
        exact proof'''
        self.assertEqual(list(explicit_tactic_items(source)), [
            ('unfold', ('runtime.first', 'runtime.second')),
            ('simp', ('runtime.next_tactic',)),
        ])


if __name__ == '__main__':
    unittest.main()
