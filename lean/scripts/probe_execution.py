#!/usr/bin/env python3
"""Run the M0 execution extraction probes without changing committed models.

Requires the pinned tools and the repository's existing Lean dependency cache.
Generated LLBC, Lean, and compiled modules stay in a fresh TMPDIR directory.
"""
from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean"
FIXTURES = ROOT / "tests" / "extraction"
CHARON = ROOT / "vendor/aeneas-lean/charon/charon/target/release/charon"
AENEAS = ROOT / "vendor/aeneas-lean/src/_build/default/main.exe"


def run(args: list[str | Path], *, env: dict[str, str] | None = None) -> None:
    subprocess.run([str(x) for x in args], cwd=LEAN, env=env, check=True)


def main() -> None:
    scratch = Path(tempfile.mkdtemp(prefix="itasca-exec-probes-"))
    print(f"Probe outputs: {scratch}", flush=True)
    env = dict(os.environ, RUSTUP_TOOLCHAIN="nightly-2026-09-17")
    env["LEAN_PATH"] = str(scratch) + os.pathsep + env.get("LEAN_PATH", "")
    help_text = subprocess.check_output([CHARON, "rustc", "--help"], text=True)
    for flag in ("--start-from", "--opaque", "--exclude"):
        if flag not in help_text:
            raise RuntimeError(f"Pinned Charon lacks {flag}")
    flags = ["--preset=aeneas", "--sysroot=default",
             "--exclude={impl core::clone::Clone for _}",
             "--exclude={impl core::marker::Copy for _}"]
    for filename in ("split.rs", "platform.rs"):
        shutil.copyfile(FIXTURES / filename, scratch / filename)
    for name, source, crate, selection, namespace in (
        ("validator", "split.rs", "probe", ["--exclude=probe::runtime"], "Validator"),
        ("runtime", "split.rs", "probe", ["--start-from=probe::runtime", "--opaque=probe::validator"], "Runtime"),
        ("platform", "platform.rs", "platform", [
            "--include=core::marker::{impl core::marker::Copy for u8}",
            "--include=core::clone::impls::{impl core::clone::Clone for u8}",
        ], "Platform"),
    ):
        llbc = scratch / f"{name}.llbc"
        run([CHARON, "rustc", *flags, *selection, f"--dest-file={llbc}",
             "--", "--crate-type", "lib", "--crate-name", crate, scratch / source], env=env)
        run([AENEAS, "-backend", "lean", llbc, "-dest", scratch,
             "-subdir", f"/{namespace}", "-namespace", namespace,
             "-split-files", "-no-progress-bar"], env=env)
    shutil.copyfile(FIXTURES / "SplitTypesExternal.lean", scratch / "Runtime/TypesExternal.lean")
    shutil.copyfile(FIXTURES / "SplitFunsExternal.lean", scratch / "Runtime/FunsExternal.lean")
    shutil.copyfile(FIXTURES / "Audit.lean", scratch / "Audit.lean")
    for module in ("Validator/Types", "Validator/Funs", "Runtime/TypesExternal",
                   "Runtime/Types", "Runtime/FunsExternal", "Runtime/Funs",
                   "Platform/Types", "Platform/Funs"):
        run(["lake", "env", "lean", "-R", scratch, "-o", scratch / f"{module}.olean",
             scratch / f"{module}.lean"], env=env)
    run(["lake", "env", "lean", "-R", scratch, scratch / "Audit.lean"], env=env)
    print("P0.1-P0.3 passed: split bridge, platform shape, loop model, and axiom audit.")


if __name__ == "__main__":
    main()
