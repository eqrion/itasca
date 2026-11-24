import unittest
from check_namespaces import namespace_errors


class NamespacePolicyTests(unittest.TestCase):
    def test_semantic_subjects_and_operation_extensions(self):
        self.assertEqual(namespace_errors('''namespace Itasca.Compiler
structure Output where
  bytes : Nat
end Itasca.Compiler
namespace Itasca
 theorem runtime.compiler.compile_with.spec : True := True.intro
 theorem Compiler.compile_with.sound : True := True.intro
end Itasca
'''), [])

    def test_import_names_and_prose_are_not_declaration_names(self):
        self.assertEqual(namespace_errors('''import Itasca.Runtime.Compiler.Local.Foo
-- namespace Itasca.Runtime
/- namespace Itasca.ModuleEnv -/
namespace Itasca.Compiler
def text := "namespace Itasca.StreamBatch"
end Itasca.Compiler
'''), [])

    def test_old_runtime_and_flat_subjects_are_rejected(self):
        self.assertEqual(len(namespace_errors('''namespace Itasca.Runtime.Compiler
end Itasca.Runtime.Compiler
namespace Itasca
namespace ModuleEnv
end ModuleEnv
 theorem StreamBatch.valid : True := True.intro
end Itasca
''')), 3)

    def test_explicit_root_cannot_hide_legacy_declaration(self):
        self.assertEqual(len(namespace_errors('''namespace Itasca.Compiler
 theorem _root_.Itasca.Runtime.hidden : True := True.intro
end Itasca.Compiler
''')), 1)

    def test_sections_mutual_and_partial_namespace_closing(self):
        errors = namespace_errors('''section
namespace Itasca.CodeEntry
noncomputable section
mutual
 def locals := 0
end
end
end CodeEntry
namespace ModuleEnv
end ModuleEnv
end Itasca
end
''')
        self.assertEqual(len(errors), 1)
        self.assertIn('Itasca.ModuleEnv', errors[0])

    def test_private_local_helpers_keep_module_scope(self):
        self.assertEqual(namespace_errors('''namespace Itasca
private theorem local_helper : True := True.intro
private def local_value := 0
end Itasca
'''), [])
        self.assertEqual(len(namespace_errors('''namespace Itasca
private theorem Runtime.hidden : True := True.intro
end Itasca
''')), 1)

    def test_new_arbitrary_subject_needs_policy_review(self):
        for spelling in ('Miscellaneous', 'miscellaneous'):
            self.assertEqual(len(namespace_errors(f'namespace Itasca.{spelling}\nend Itasca.{spelling}\n')), 1)

    def test_subject_and_record_names_must_not_repeat(self):
        errors = namespace_errors('''namespace Itasca.Binary.Module
structure Module where
  size : Nat
end Itasca.Binary.Module
namespace Itasca.Module.Layout
structure Layout where
  size : Nat
end Itasca.Module.Layout
''')
        self.assertEqual(len(errors), 2)
        self.assertTrue(all('repeated namespace component' in error for error in errors))
        self.assertEqual(namespace_errors('''namespace Itasca.Binary
structure Module where
  size : Nat
end Itasca.Binary
namespace Itasca.Module
structure Layout where
  size : Nat
end Itasca.Module
'''), [])


if __name__ == '__main__':
    unittest.main()
