import unittest

from exec_stats import declarations, namespace_file_counts, swap_profile


class ExecStatsTest(unittest.TestCase):
    def test_declarations(self):
        text = """
theorem a : True := trivial
@[simp] private theorem b.c : True := trivial
  theorem indented : True := trivial
noncomputable def d (x : Nat) : Nat := x
structure E where
instance : Inhabited E := ⟨⟩
"""
        self.assertEqual(declarations(text), [
            ("theorem", "a"), ("theorem", "b.c"), ("def", "d"),
            ("structure", "E"), ("instance", ""),
        ])

    def test_swap_profile(self):
        self.assertEqual(swap_profile("Code/Wasm1/BodyWasm1.lean"), "Code/Wasm2/BodyWasm2.lean")
        self.assertEqual(swap_profile("reader_wasm2_ok"), "reader_wasm1_ok")

    def test_reopened_namespace_counts_once_per_file(self):
        texts = ["namespace A\nend A\nnamespace A\nend A\n",
                 "namespace A\nend A\nnamespace B\nend B\n"]
        self.assertEqual(namespace_file_counts(texts), {"A": 2, "B": 1})


if __name__ == "__main__":
    unittest.main()
