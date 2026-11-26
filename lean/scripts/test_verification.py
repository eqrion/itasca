"""Exercise the real just recipes with stand-ins for expensive commands."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class VerifyTests(unittest.TestCase):
    def test_verify_runs_every_gate_in_order_and_builds_proofs_once(self):
        repo = Path(__file__).resolve().parents[2]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / 'lean').mkdir()
            for filename in ('justfile', 'lean/justfile'):
                shutil.copyfile(repo / filename, root / filename)

            log = root / 'commands.log'
            cache = root / 'tool cache'
            env = dict(os.environ, PATH=f'{root}{os.pathsep}{os.environ["PATH"]}',
                       TOOLS_CACHE=str(cache), OPAM_SWITCH='test-switch', VERIFY_LOG=str(log))
            tools_dir = subprocess.check_output(
                ['just', '--evaluate', 'tools_dir'], cwd=root / 'lean', env=env, text=True,
            ).strip()
            spectec = root / 'vendor/spectec/spectec'
            (spectec.parent / 'specification/wasm-2.0').mkdir(parents=True)
            (spectec.parent / 'specification/wasm-2.0/input.spectec').touch()
            (root / 'patches').mkdir()
            (root / 'patches/spectec-wasm2-builtins.patch').touch()
            children = [root / command for command in ('cargo', 'make', 'python3', 'opam', 'patch', 'cmp', 'lake')]
            children += [Path(tools_dir) / 'bin' / name for name in ('aeneas', 'charon', 'charon-driver')]
            children.append(spectec / '_build/default/src/exe-spectec/main.exe')
            for child in children:
                child.parent.mkdir(parents=True, exist_ok=True)
                child.write_text('#!/bin/sh\nprintf \'%s\\n\' "${0##*/} $*" >> "$VERIFY_LOG"\n')
                child.chmod(0o755)
            (root / 'git').write_text('#!/bin/sh\nexit 0\n')
            (root / 'git').chmod(0o755)
            result = subprocess.run(
                ['just', 'verify'], cwd=root, env=env,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            )
            self.assertEqual(result.returncode, 0, result.stdout)
            comparisons = [
                f'cmp .build/extract-check/Itasca/Generated/{name}.lean Itasca/Generated/{name}.lean'
                for name in ('Types', 'Funs', 'FunsValidator', 'FunsRuntimeCommon',
                             'FunsCompiler', 'FunsStore', 'FunsInterp', 'FunsInstantiate')
            ]
            self.assertEqual(log.read_text().splitlines(), [
                'cargo test',
                'cargo test --no-default-features',
                'python3 -m unittest discover -s scripts -p test_*.py',
                'python3 scripts/architecture.py',
                'python3 scripts/metrics.py --check metrics/baseline.json',
                'python3 scripts/check_links.py',
                'python3 scripts/check_forbidden.py',
                'python3 scripts/check_namespaces.py',
                'charon cargo --preset=aeneas --sysroot=default --rustc-arg=--cfg=charon '
                '--exclude={impl core::clone::Clone for _} --exclude={impl core::marker::Copy for _} '
                '--include=core::marker::{impl core::marker::Copy for u8} '
                '--include=core::clone::impls::{impl core::clone::Clone for u8} '
                f'--dest-file={root}/lean/.build/itasca.llbc',
                'aeneas -backend lean .build/itasca.llbc -dest .build/extract-check '
                '-subdir /Itasca/Generated -split-files -namespace Itasca -no-progress-bar',
                'python3 scripts/strip_source_lines.py .build/extract-check/Itasca/Generated/Types.lean '
                '.build/extract-check/Itasca/Generated/Funs.lean',
                'python3 scripts/split_funs.py .build/extract-check/Itasca/Generated/Funs.lean',
                *comparisons,
                'make -C ../vendor/spectec/spectec src/backend-interpreter/reference-interpreter',
                'opam exec --switch=test-switch -- dune build src/exe-spectec/main.exe',
                'main.exe ../specification/wasm-2.0/input.spectec --lean --single-pattern-match '
                f'--wf-state all -o {root}/lean/.build/spec/wasm2.0.lean',
                'patch -f -F 0 -p1 -d .build/spec',
                'cmp .build/spec/wasm2.0.lean SpecTec/wasm2.0.lean',
                'lake build Itasca SpecExt',
                'python3 scripts/lean_warnings.py --check',
                'python3 scripts/run_audit.py --no-build',
            ])
