#!/usr/bin/env python3
"""Check transparent type/trait reuse across two Aeneas extraction passes."""
from __future__ import annotations
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from probe_execution import ROOT, LEAN, FIXTURES, CHARON, AENEAS, run


def main() -> None:
    scratch = Path(tempfile.mkdtemp(prefix="itasca-reuse-probe-"))
    print(f"Reuse probe outputs: {scratch}", flush=True)
    env = dict(os.environ, RUSTUP_TOOLCHAIN="nightly-2026-09-17")
    env["LEAN_PATH"] = str(scratch) + os.pathsep + env.get("LEAN_PATH", "")
    shutil.copyfile(FIXTURES / "reuse.rs", scratch / "reuse.rs")
    for name, selection, options in (
        ("ReuseBase", ["--exclude=reuse::runtime"], []),
        ("Reuse", ["--start-from=reuse::runtime", "--opaque=reuse::validator",
                   "--include=reuse::validator::Kind", "--include=reuse::validator::Token"],
         ["-reuse-definitions", FIXTURES / "reuse.json"]),
    ):
        llbc = scratch / f"{name}.llbc"
        run([CHARON, "rustc", "--preset=aeneas", "--sysroot=default", *selection,
             f"--dest-file={llbc}", "--", "--crate-type", "lib", "--crate-name",
             "reuse", scratch / "reuse.rs"], env=env)
        run([AENEAS, "-backend", "lean", llbc, "-dest", scratch,
             "-subdir", f"/{name}", "-namespace", name, "-split-files",
             "-no-progress-bar", "-strict-joins", *options], env=env)
    # The optional dead-local optimization must preserve the entire generated
    # model on this borrowed callback/enum/projection fixture.
    optimized = scratch / "optimized"
    run([AENEAS, "-backend", "lean", scratch / "Reuse.llbc", "-dest", optimized,
         "-subdir", "/Reuse", "-namespace", "Reuse", "-split-files",
         "-no-progress-bar", "-strict-joins", "-skip-bottom-storage-dead",
         "-reuse-definitions", FIXTURES / "reuse.json"], env=env)
    for filename in ("Types.lean", "Funs.lean", "FunsExternal_Template.lean"):
        if (scratch / "Reuse" / filename).read_bytes() != (optimized / "Reuse" / filename).read_bytes():
            raise RuntimeError(f"Dead-local optimization changed generated {filename}")
    for name in ("TypesExternal", "FunsExternal"):
        shutil.copyfile(FIXTURES / f"Reuse{name}.lean", scratch / "Reuse" / f"{name}.lean")
    for module in ("ReuseBase/Types", "ReuseBase/Funs", "Reuse/TypesExternal",
                   "Reuse/Types", "Reuse/FunsExternal", "Reuse/Funs"):
        run(["lake", "env", "lean", "-R", scratch, "-o", scratch / f"{module}.olean",
             scratch / f"{module}.lean"], env=env)
    shutil.copyfile(FIXTURES / "ReuseAudit.lean", scratch / "Audit.lean")
    run(["lake", "env", "lean", "-R", scratch, scratch / "Audit.lean"], env=env)
    print("Type reuse passed: direct fields, enum matching, trait implementation, and axiom audit.")


if __name__ == "__main__":
    main()
