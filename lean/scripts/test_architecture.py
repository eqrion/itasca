import os
import tempfile
import unittest

from architecture import layer_violations, parse_imports, source_graph, missing_project_imports


class ImportParsingTests(unittest.TestCase):
    def test_missing_owner_cannot_hide_behind_a_cached_olean(self):
        with tempfile.TemporaryDirectory() as root:
            os.makedirs(os.path.join(root, "Itasca"))
            with open(os.path.join(root, "Itasca", "A.lean"), 'w') as out:
                out.write("import Itasca.Moved Mathlib.Data.Nat.Basic\n")
            os.makedirs(os.path.join(root, ".lake", "build", "lib", "lean", "Itasca"))
            with open(os.path.join(root, ".lake", "build", "lib", "lean", "Itasca", "Moved.olean"), 'w') as out:
                out.write("obsolete cache")
            self.assertEqual(missing_project_imports(root),
                             ["Itasca.A imports missing source module Itasca.Moved"])
            with open(os.path.join(root, "Itasca", "Moved.lean"), 'w') as out:
                out.write("")
            self.assertEqual(missing_project_imports(root), [])

    def test_ignores_fake_imports_in_line_block_and_string_comments(self):
        source = '''
-- import Itasca.Runtime.Hidden
/- import Itasca.Runtime.Hidden
   /- import SpecExt.Hidden -/
-/
def example := "import Itasca.Runtime.Hidden"
import Itasca.Binary.Real
'''
        self.assertEqual(parse_imports(source), ["Itasca.Binary.Real"])

    def test_indented_imports_are_not_hidden(self):
        self.assertEqual(parse_imports("  public meta import Itasca.Binary.A\n"),
                         ["Itasca.Binary.A"])

    def test_import_modifiers_and_multiline_whitespace(self):
        source = "module\npublic meta import Itasca.Binary.A\nmeta import all\n Itasca.Binary.B\nimport -- comment\n Itasca.Binary.C\n"
        self.assertEqual(parse_imports(source), ["Itasca.Binary.A", "Itasca.Binary.B", "Itasca.Binary.C"])

    def test_quoted_aliases_and_primed_modules_keep_real_edges(self):
        self.assertEqual(parse_imports("import «Itasca».«Runtime».Hidden'\n"),
                         ["Itasca.Runtime.Hidden'"])
        with tempfile.TemporaryDirectory() as root:
            os.makedirs(os.path.join(root, "Itasca", "Results", "Definitions"))
            os.makedirs(os.path.join(root, "Itasca", "Runtime"))
            with open(os.path.join(root, "Itasca", "Results", "Definitions", "A.lean"), 'w') as out:
                out.write("meta import «Itasca».«Runtime».Hidden'\n")
            with open(os.path.join(root, "Itasca", "Runtime", "Hidden'.lean"), 'w') as out:
                out.write('')
            self.assertTrue(layer_violations(source_graph(root)))

    def test_characters_inside_module_identifiers_are_not_literals(self):
        self.assertEqual(parse_imports("import Itasca.Runtime.Foo'a'\nimport Itasca.Runtime.«'a'»\n"),
                         ["Itasca.Runtime.Foo'a'", "Itasca.Runtime.'a'"])

    def test_quoted_dotted_components_do_not_alias_nested_modules(self):
        self.assertEqual(parse_imports('import Itasca.«Foo.Bar»\nimport Itasca.Foo.Bar\n'),
                         ['Itasca.«Foo.Bar»', 'Itasca.Foo.Bar'])

    def test_parses_multiple_modules_on_one_import_line(self):
        self.assertEqual(parse_imports("import Itasca.Binary.A Mathlib.Data.Nat.Basic\n"),
                         ["Itasca.Binary.A", "Mathlib.Data.Nat.Basic"])

    def test_source_graph_filters_external_imports_to_known_sources(self):
        with tempfile.TemporaryDirectory() as root:
            os.makedirs(os.path.join(root, "Itasca"))
            with open(os.path.join(root, "Itasca", "A.lean"), "w") as out:
                out.write("import Itasca.B Mathlib.Data.Nat\n")
            with open(os.path.join(root, "Itasca", "B.lean"), "w") as out:
                out.write("-- import Itasca.A\n")
            self.assertEqual(source_graph(root), {"Itasca.A": ["Itasca.B"], "Itasca.B": []})


class ArchitecturePolicyTests(unittest.TestCase):
    def test_layer_rules_cover_direct_and_transitive_boundaries(self):
        graph = {
            "Itasca.Binary.Parser": ["Itasca.Results.Validate"],
            "Itasca.Results.Validate": ["Itasca.Results.Definitions.Validation"],
            "Itasca.Results.Definitions.Validation": ["Itasca.Helper"],
            "Itasca.Helper": ["Itasca.Generated.FunsRuntimeCommon"],
            "Itasca.Generated.FunsRuntimeCommon": [],
            "Itasca.Runtime.Compiler.Local.X": ["Itasca.Runtime.Compiler.Module.Relation"],
            "Itasca.Runtime.Compiler.Module.Relation": [],
        }
        violations = layer_violations(graph)
        rules = [rule for _, _, rule in violations]
        self.assertTrue(any("Support/Spec/Binary" in rule for rule in rules))
        self.assertTrue(any("Definition transitive import" in rule for rule in rules))
        self.assertTrue(any("validator surface" in rule for rule in rules))
        self.assertTrue(any("Compiler stages" in rule for rule in rules))

    def test_narrow_interface_definitions_remain_allowed_in_foundations(self):
        graph = {
            "Itasca.Binary.Encoding": ["Itasca.Results.Definitions.Binary.Encoding"],
            "Itasca.Results.Definitions.Binary.Encoding": [],
        }
        self.assertEqual(layer_violations(graph), [])


class BoundaryChecksTests(unittest.TestCase):
    def test_shared_results_directory_does_not_mix_definition_and_proof_layers(self):
        definitions = "Itasca.Results.Definitions.Store"
        result = "Itasca.Results.Store"
        implementation = "Itasca.Runtime.Store.Proof"
        allowed = {result: [definitions, implementation], implementation: [definitions], definitions: []}
        self.assertEqual(layer_violations(allowed), [])
        for leaked in (result, implementation):
            graph = {definitions: ["Itasca.Results.Definitions.Helper"],
                     "Itasca.Results.Definitions.Helper": [leaked], leaked: []}
            self.assertTrue(any("Definition transitive import" in rule for rule in self.rules(graph)))

    def test_consolidated_validator_units_keep_transitive_isolation(self):
        for unit in ["Foundations", "Binary", "Visitor", "Observations", "Validation", "Streaming"]:
            source = "Itasca.Results.Definitions." + unit
            graph = {source: ["Itasca.Results.Definitions.Helper"],
                     "Itasca.Results.Definitions.Helper": ["Itasca.Generated.FunsRuntimeCommon"],
                     "Itasca.Generated.FunsRuntimeCommon": []}
            self.assertTrue(any("validator surface" in rule for _, _, rule in layer_violations(graph)))

    def test_compiler_stage_rules_follow_moved_owners(self):
        for source in ("Itasca.Runtime.Compiler.Local.Caller",
                       "Itasca.Results.Definitions.Compiler.Local.Caller"):
            target = "Itasca.Results.Definitions.Compiler.Body.Relation"
            violations = layer_violations({source: [target], target: []})
            self.assertTrue(any("Compiler stages" in rule for _, _, rule in violations))

    def test_compiler_interface_cannot_import_interpreter(self):
        source = "Itasca.Results.Definitions.Compiler.Module"
        target = "Itasca.Generated.FunsInterp"
        violations = layer_violations({source: [target], target: []})
        self.assertTrue(any("interpreter functions" in rule for _, _, rule in violations))

    def rules(self, graph):
        return [rule for _, _, rule in layer_violations(graph)]

    def test_interface_transitive_leakage_through_helper(self):
        graph = {
            "Itasca.Results.Definitions.Validation": ["Itasca.Results.Definitions.Helper"],
            "Itasca.Results.Definitions.Helper": ["Itasca.Runtime.Internal"],
            "Itasca.Runtime.Internal": [],
        }
        self.assertTrue(any("Definition transitive import" in rule for rule in self.rules(graph)))

    def test_interface_rejects_broad_generated_umbrella(self):
        graph = {
            "Itasca.Results.Definitions.Validation": ["Itasca.Generated.Funs"],
            "Itasca.Generated.Funs": [],
        }
        self.assertTrue(any("Funs umbrella" in rule for rule in self.rules(graph)))

    def test_implementation_cannot_import_results_and_results_cannot_cross_import(self):
        graph = {
            "Itasca.Runtime.Compiler.Internal": ["Itasca.Results.Validate"],
            "Itasca.Results.Validate": ["Itasca.Results.Stream"],
            "Itasca.Results.Stream": [],
        }
        rules = self.rules(graph)
        self.assertTrue(any("implementation modules" in rule for rule in rules))
        self.assertTrue(any("another theorem module" in rule for rule in rules))

    def test_results_cannot_import_full_interface_umbrella(self):
        graph = {
            "Itasca.Results.Validate": ["Itasca.Results.Definitions"],
            "Itasca.Results.Definitions": [],
        }
        self.assertTrue(any("definitions umbrella" in rule for rule in self.rules(graph)))

    def test_foundation_layers_allow_only_narrow_interface_definitions(self):
        narrow = {"Itasca.Binary.Encoding": ["Itasca.Results.Definitions.Binary.Encoding"],
                  "Itasca.Results.Definitions.Binary.Encoding": []}
        self.assertFalse(any("Support/Spec/Binary" in rule for rule in self.rules(narrow)))
        broad = {"Itasca.Binary.Encoding": ["Itasca.Results.Definitions"],
                 "Itasca.Results.Definitions": []}
        self.assertTrue(any("Support/Spec/Binary" in rule for rule in self.rules(broad)))

    def test_namespace_name_does_not_stand_in_for_module_ownership(self):
        graph = {
            "Itasca.Runtime.PublicNamespace": ["Itasca.Results.Definitions.Validation"],
            "Itasca.Results.Definitions.Validation": [],
        }
        self.assertFalse(any("Results" in rule for rule in self.rules(graph)))

    def test_validator_runtime_partition_leakage_through_helper(self):
        graph = {
            "Itasca.Module.Layout": ["Itasca.Module.Helper"],
            "Itasca.Module.Helper": ["Itasca.Generated.FunsRuntimeCommon"],
            "Itasca.Generated.FunsRuntimeCommon": [],
        }
        self.assertTrue(any("validator surface" in rule for rule in self.rules(graph)))

    def test_validator_rejects_nested_specext_and_includes_support_spec_contracts(self):
        graph = {
            "Itasca.Support.Helper": ["SpecExt.Host"],
            "SpecExt.Host": [],
            "Itasca.Spec.Helper": ["Itasca.Spec.Helper2"],
            "Itasca.Spec.Helper2": ["Itasca.Generated.FunsRuntimeCommon"],
            "Itasca.Generated.FunsRuntimeCommon": [],
            "Itasca.CodeEntry.Helper": ["SpecExt.Host"],
        }
        rules = self.rules(graph)
        self.assertTrue(any("Itasca.Support.Helper" in str(rule) and "SpecExt" in rule for rule in rules))
        self.assertTrue(any("Itasca.Spec.Helper" in str(rule) and "runtime partitions" in rule for rule in rules))
        self.assertTrue(any("Itasca.CodeEntry.Helper" in str(rule) and "SpecExt" in rule for rule in rules))



if __name__ == "__main__":
    unittest.main()
