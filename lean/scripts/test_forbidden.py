"""Exercise the actual cheap source gate, including inline/private forms."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class ForbiddenSourceTests(unittest.TestCase):
    def check_source(self, source, generated=False):
        justfile = Path(__file__).resolve().parents[1] / 'justfile'
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'lean/Itasca').mkdir(parents=True)
            (root / 'lean/SpecExt').mkdir()
            scripts = root / 'lean/scripts'
            scripts.mkdir()
            for name in ('check_forbidden.py', 'architecture.py'):
                shutil.copyfile(Path(__file__).parent / name, scripts / name)
            folder = root / 'lean/Itasca'
            if generated:
                folder = folder / 'Generated'
                folder.mkdir()
            (folder / 'Fixture.lean').write_text(source)
            return subprocess.run(
                ['just', '--justfile', str(justfile), '--working-directory', str(root / 'lean'),
                 '_lint-forbidden'],
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            ).returncode

    def test_inline_private_and_unproved_specification_references_are_rejected(self):
        for source in ['private axiom bad : True',
                       'theorem bad : True := by admit',
                       'theorem bad : True := by sorry',
                       'example : True := by native_decide',
                       '#check Step_is_wf', '#check Step_read_is_wf',
                       '#check Step_pure_is_wf']:
            with self.subTest(source=source):
                self.assertNotEqual(self.check_source(source), 0)

    def test_valid_handwritten_proofs_and_excluded_generated_inputs(self):
        self.assertEqual(self.check_source('theorem good : True := True.intro'), 0)
        self.assertEqual(self.check_source('axiom generated_fixture : True', generated=True), 0)

    def test_comments_and_strings_are_not_proof_constructs(self):
        self.assertEqual(self.check_source('''
/- Axioms and targets that admit inhabitants.
   /- Step_is_wf, sorry, admit, native_decide, axiom -/
-/
-- The unproved Step_read_is_wf must not be used.
def explanation := "admit sorry axiom native_decide Step_pure_is_wf"
theorem good : True := True.intro
'''), 0)
