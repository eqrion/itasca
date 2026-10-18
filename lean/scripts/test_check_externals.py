import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from check_externals import check


class ExternalCoverageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def file(self, name, patterns, kind):
        path = self.root / name
        path.write_text("\n".join(f'@[rust_fun "{p}"] {kind} {p} : Nat' for p in patterns))
        return path

    def test_explicit_imported_models_cover_template(self):
        template = self.file("template", ["primitive", "shared"], "axiom")
        own = self.file("own", ["primitive"], "def")
        imported = self.file("imported", ["shared"], "def")
        with contextlib.redirect_stdout(io.StringIO()):
            check(template, own, imported)

    def test_unrelated_extra_model_is_rejected(self):
        template = self.file("template", ["primitive"], "axiom")
        own = self.file("own", ["primitive"], "def")
        extra = self.file("extra", ["unrelated"], "def")
        with self.assertRaisesRegex(ValueError, "extra=.*unrelated"):
            check(template, own, extra)

    def test_duplicate_mapping_across_files_is_rejected(self):
        template = self.file("template", ["primitive"], "axiom")
        own = self.file("own", ["primitive"], "def")
        duplicate = self.file("duplicate", ["primitive"], "def")
        with self.assertRaisesRegex(ValueError, "Duplicate external models"):
            check(template, own, duplicate)

    def test_missing_import_is_not_assumed_from_source_text(self):
        template = self.file("template", ["primitive", "shared"], "axiom")
        own = self.file("own", ["primitive"], "def")
        own.write_text("public import Imported.Models\n" + own.read_text())
        with self.assertRaisesRegex(ValueError, "missing=.*shared"):
            check(template, own)

    def test_local_opaque_request_requires_concrete_alias(self):
        template = self.file("template", ["primitive"], "axiom")
        template.write_text(template.read_text() +
                            '\n/-- [itasca::shared]:\n    Source: x -/\naxiom shared : Nat')
        own = self.file("own", ["primitive"], "def")
        with self.assertRaisesRegex(ValueError, "missing=.*itasca::shared"):
            check(template, own)
        shared = self.file("shared", ["itasca::shared"], "def")
        with contextlib.redirect_stdout(io.StringIO()):
            check(template, own, shared)

    def test_unidentified_local_axiom_is_rejected(self):
        template = self.file("template", ["primitive"], "axiom")
        template.write_text(template.read_text() + '\naxiom hidden : Nat')
        own = self.file("own", ["primitive"], "def")
        with self.assertRaisesRegex(ValueError, "Unidentified external axiom"):
            check(template, own)

    def test_local_trait_default_request_is_checked(self):
        template = self.root / "template"
        template.write_text('/-- [itasca::Trait::method]:\n Source: x -/\n'
                            '@[trait_default]\naxiom method.default : Nat')
        own = self.file("own", ["itasca::Trait::method"], "def")
        with contextlib.redirect_stdout(io.StringIO()):
            check(template, own)

    def test_nested_doc_comment_cannot_identify_an_axiom(self):
        template = self.file("template", ["primitive"], "axiom")
        template.write_text(template.read_text() +
                            '\n/- /-- [itasca::shared]:\n -/ -/\naxiom hidden : Nat')
        own = self.file("own", ["primitive"], "def")
        with self.assertRaisesRegex(ValueError, "Unidentified external axiom"):
            check(template, own)


if __name__ == "__main__":
    unittest.main()
