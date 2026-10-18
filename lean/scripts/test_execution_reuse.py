import unittest
from execution_reuse import build_map


class ReuseMapTests(unittest.TestCase):
    def fixture(self):
        def meta(name):
            return {"name": [{"Ident": [part, 0]} for part in name.split("::")]}
        source = {"translated": {
            "type_decls": [{"item_meta": meta("itasca::Kind"), "kind": {"Enum": [
                {"name": "Type"}, {"name": "Empty"}]}}],
            "trait_decls": [{"item_meta": meta("itasca::Visitor"), "implied_clauses": [],
                             "methods": [{"skip_binder": {"name": "visit"}}]}]}}
        lean = """/-- [itasca::Kind] -/
inductive Kind where
| «Type» : Kind
| Empty : Kind
/-- Trait declaration: [itasca::Visitor] -/
structure Visitor (Self : Type) where
  visit : Self → Bool
"""
        return source, lean

    def test_maps_escaped_constructor(self):
        result = build_map(*self.fixture())
        self.assertEqual(result["types"][0]["members"], [("Type", "«Type»"), ("Empty", "Empty")])
        self.assertEqual(result["traits"][0]["methods"], [("visit", "visit")])

    def test_rejects_member_count_change(self):
        source, lean = self.fixture()
        with self.assertRaisesRegex(ValueError, "member count"):
            build_map(source, lean.replace("| Empty : Kind\n", ""))

    def test_rejects_reordered_same_count_members(self):
        source, lean = self.fixture()
        with self.assertRaisesRegex(ValueError, "member identity"):
            build_map(source, lean.replace("| «Type» : Kind\n| Empty : Kind", "| Empty : Kind\n| «Type» : Kind"))

    def test_rejects_kind_change(self):
        source, lean = self.fixture()
        with self.assertRaisesRegex(ValueError, "kind changed"):
            build_map(source, lean.replace("inductive Kind", "structure Kind"))

    def test_rejects_trait_count_change(self):
        source, lean = self.fixture()
        with self.assertRaisesRegex(ValueError, "Trait member count"):
            build_map(source, lean.replace("  visit : Self → Bool\n", ""))


if __name__ == "__main__":
    unittest.main()
