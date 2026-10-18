"""Regression tests for the generated-specification split's rejection paths."""
import unittest

from spec_split import BUILTINS, split


def builtin(name: str, signature: str = "(x : Nat) : Nat") -> str:
    return (f"/- Axiom Definition at: fixture.spectec:1 -/\n"
            f"opaque {name} {signature} := by\n"
            "  first\n"
            "     | exact Inhabited.default\n"
            "     | intros ; assumption\n\n\n")


def fixture() -> str:
    return ("import ExtendedDeriveDecEq\n\n" + builtin("inv_concat_")
            + "abbrev PrefixType : Type := Nat\n\n"
            + builtin("s33_to_u32")
            + "".join(builtin(n) for n in sorted(BUILTINS - {"inv_concat_", "s33_to_u32"})))


class SpecSplitTests(unittest.TestCase):
    def test_deterministic_split_and_exact_inventory(self):
        result = split(fixture())
        self.assertEqual(result, split(fixture()))
        self.assertEqual(result["Wasm2Builtins.lean"].count("example :"), len(BUILTINS))
        self.assertIn("abbrev PrefixType", result["Wasm2Prefix.lean"])
        self.assertNotIn("opaque", result["wasm2.0.lean"])

    def test_changed_body(self):
        with self.assertRaises(ValueError):
            split(fixture().replace("exact Inhabited.default", "exact 0", 1))

    def test_new_builtin(self):
        with self.assertRaises(ValueError):
            split(fixture() + builtin("new_builtin"))

    def test_unrecognized_opaque(self):
        with self.assertRaises(ValueError):
            split(fixture() + "opaque unknown : Nat := 0\n")

    def test_duplicate_builtin(self):
        with self.assertRaises(ValueError):
            split(fixture() + builtin("truncz"))

    def test_signature_depends_on_later_type(self):
        source = fixture().replace(builtin("truncz"), builtin("truncz", "(x : Later) : Nat"))
        with self.assertRaisesRegex(ValueError, "later declarations"):
            split(source + "abbrev Later : Type := Nat\n")

    def test_prefix_depends_on_builtin(self):
        with self.assertRaisesRegex(ValueError, "Prefix depends"):
            split(fixture().replace("abbrev PrefixType", "def uses := inv_concat_\nabbrev PrefixType"))

    def test_binder_can_shadow_later_name(self):
        source = fixture().replace(builtin("truncz"), builtin("truncz", "(Later : Nat) : Nat"))
        split(source + "abbrev Later : Type := Nat\n")


if __name__ == "__main__":
    unittest.main()
