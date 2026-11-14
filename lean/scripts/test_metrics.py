import unittest

from metrics import explicit_tactic_items, extracted_definitions, extracted_tactic_definitions


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
