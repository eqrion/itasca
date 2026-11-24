import contextlib
import io
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_links


class LinkScopeTests(unittest.TestCase):
    def test_checks_only_the_repository_from_an_unrelated_working_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            parent = Path(directory)
            root = parent / 'repo'
            root.mkdir()
            (root / 'README.md').write_text('[guide](guide.md)')
            (root / 'guide.md').write_text('Guide')
            (parent / 'unrelated.md').write_text('[missing](outside.md)')
            previous = Path.cwd()
            try:
                os.chdir(parent)
                output = io.StringIO()
                with patch.object(check_links, 'ROOT', str(root)), contextlib.redirect_stdout(output):
                    self.assertEqual(check_links.main(), 0)
                    (root / 'guide.md').unlink()
                    self.assertEqual(check_links.main(), 1)
                self.assertEqual(output.getvalue(), 'README.md: broken link guide.md\n')
            finally:
                os.chdir(previous)
