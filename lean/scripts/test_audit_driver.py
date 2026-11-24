import contextlib
import io
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import run_audit
from audit_environment import collect_audit


class ArtifactTests(unittest.TestCase):
    def artifacts(self):
        return {Path('metrics/audit.txt'): b'report\n',
                Path('metrics/interface-manifest.json'): b'{}\n'}

    def setup_root(self, root):
        (root / 'metrics').mkdir()

    def test_check_detects_every_missing_or_stale_output_without_writes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.setup_root(root)
            (root / 'metrics/audit.txt').write_bytes(b'old\n')
            with contextlib.redirect_stderr(io.StringIO()) as diagnostics:
                self.assertFalse(run_audit.publish(root, self.artifacts()))
            for name in self.artifacts():
                self.assertIn(str(name), diagnostics.getvalue())
            self.assertEqual((root / 'metrics/audit.txt').read_bytes(), b'old\n')
            self.assertFalse((root / 'metrics/interface-manifest.json').exists())
            self.assertFalse((root / '.build').exists())

    def test_update_publishes_all_outputs_and_check_is_read_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.setup_root(root)
            self.assertTrue(run_audit.publish(root, self.artifacts(), update=True))
            timestamps = {name: (root / name).stat().st_mtime_ns for name in self.artifacts()}
            self.assertTrue(run_audit.publish(root, self.artifacts()))
            self.assertTrue(run_audit.publish(root, self.artifacts(), update=True))
            self.assertEqual(timestamps, {name: (root / name).stat().st_mtime_ns
                                          for name in self.artifacts()})

    def test_staging_failure_leaves_committed_outputs_intact(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.setup_root(root)
            old = {name: b'old\n' for name in self.artifacts()}
            run_audit.publish(root, old, update=True)
            write_bytes = Path.write_bytes
            def fail_second(path, data):
                if path.name == '1':
                    raise OSError('staging failure')
                return write_bytes(path, data)
            with patch.object(Path, 'write_bytes', fail_second):
                with self.assertRaises(OSError):
                    run_audit.publish(root, self.artifacts(), update=True)
            self.assertTrue(all((root / name).read_bytes() == data for name, data in old.items()))

    def test_build_default_and_no_build_reuse_have_identical_check_path(self):
        for arguments, builds in (([], 1), (['--no-build', '--check'], 0)):
            with self.subTest(arguments=arguments), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                self.setup_root(root)
                run_audit.publish(root, self.artifacts(), update=True)
                with patch('run_audit.subprocess.run') as build, \
                     patch('run_audit.collect_audit', return_value=('report', {})), \
                     patch('run_audit.build_artifacts', return_value=self.artifacts()), \
                     contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(run_audit.main(arguments, root=root), 0)
                    self.assertEqual(build.call_count, builds)
                    if builds:
                        self.assertEqual(build.call_args.args[0], ['lake', 'build', 'Itasca', 'SpecExt'])

    def test_cli_default_rejects_stale_artifacts_and_update_is_explicit(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.setup_root(root)
            old = {name: b'old\n' for name in self.artifacts()}
            run_audit.publish(root, old, update=True)
            with patch('run_audit.subprocess.run'), \
                 patch('run_audit.collect_audit', return_value=('report', {})), \
                 patch('run_audit.build_artifacts', return_value=self.artifacts()), \
                 contextlib.redirect_stderr(io.StringIO()), \
                 contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(run_audit.main([], root=root), 1)
                self.assertTrue(all((root / name).read_bytes() == data for name, data in old.items()))
                self.assertEqual(run_audit.main(['--no-build', '--update'], root=root), 0)
                self.assertTrue(all((root / name).read_bytes() == data
                                    for name, data in self.artifacts().items()))

    def test_audit_failure_never_replaces_artifacts(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.setup_root(root)
            run_audit.publish(root, self.artifacts(), update=True)
            failure = subprocess.CalledProcessError(1, ['lean'], output='unregistered result\n')
            with patch('run_audit.collect_audit', side_effect=failure), \
                 contextlib.redirect_stderr(io.StringIO()) as errors:
                self.assertEqual(run_audit.main(['--no-build'], root=root), 1)
            self.assertIn('unregistered result', errors.getvalue())
            self.assertTrue(all((root / name).read_bytes() == data
                                for name, data in self.artifacts().items()))

    def test_snapshot_reuses_the_same_strict_audit_collection(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.setup_root(root)
            with patch('run_audit.collect_audit', return_value=('report', {})) as collect, \
                 patch('run_audit.build_artifacts', return_value=self.artifacts()), \
                 contextlib.redirect_stdout(io.StringIO()):
                snapshot = root / 'snapshot.json'
                self.assertEqual(run_audit.main(
                    ['--no-build', '--update', '--snapshot', str(snapshot)], root=root), 0)
                self.assertEqual(collect.call_count, 1)
                self.assertEqual(collect.call_args.kwargs, {'full_export': snapshot})

    def test_collection_always_enables_strict_gate_and_captures_report(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'scripts').mkdir()
            (root / 'scripts/Audit.lean').write_text('import Itasca.Main\n')
            def run(command, **kwargs):
                self.assertEqual(kwargs['env']['ITASCA_AUDIT_REQUIRE_INTERFACE'], '1')
                self.assertNotIn('ITASCA_AUDIT_JSON', kwargs['env'])
                Path(kwargs['env']['ITASCA_AUDIT_SLIM_JSON']).write_text('{"roots":[]}')
                return subprocess.CompletedProcess(command, 0, stdout='axioms passed\n')
            with patch('audit_environment.subprocess.run', side_effect=run):
                self.assertEqual(collect_audit(root, root), ('axioms passed\n', {'roots': []}))
