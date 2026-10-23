import unittest

from exec_stats import declarations, swap_profile


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


if __name__ == "__main__":
    unittest.main()
