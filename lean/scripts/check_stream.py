#!/usr/bin/env python3
"""Extract and compile the experimental stream feature without changing proofs."""

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="keep generated models here")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    output = (args.output or Path(tempfile.mkdtemp(prefix="itasca-stream-"))).resolve()
    output.mkdir(parents=True, exist_ok=True)
    print(f"Streaming extraction: {output}", flush=True)
    aeneas = root / "vendor/aeneas-lean"
    env = os.environ.copy()
    env["RUSTUP_TOOLCHAIN"] = "nightly-2026-09-17"
    env["CARGO_TARGET_DIR"] = str(root / "lean/.build/stream-cargo")

    subprocess.run(
        [str(aeneas / "charon/charon/target/release/charon"), "cargo",
         "--preset=aeneas", "--sysroot=default", "--rustc-arg=--cfg=charon",
         "--exclude={impl core::clone::Clone for _}",
         "--exclude={impl core::marker::Copy for _}",
         f"--dest-file={output / 'itasca.llbc'}", "--", "--features", "stream"],
        cwd=root, env=env, check=True,
    )
    subprocess.run(
        [str(aeneas / "src/_build/default/main.exe"), "-backend", "lean",
         str(output / "itasca.llbc"), "-dest", str(output),
         "-subdir", "/Itasca/Generated", "-split-files", "-namespace", "Itasca",
         "-no-progress-bar"],
        cwd=root, check=True,
    )
    generated = output / "Itasca/Generated"
    subprocess.run(
        ["python3", str(root / "lean/scripts/check_externals.py"),
         str(generated / "FunsExternal_Template.lean")],
        check=True,
    )
    for name in ("Types", "Funs"):
        text = (generated / f"{name}.lean").read_text()
        if re.search(r"\b(axiom|sorry|admit)\b", text):
            raise RuntimeError(f"Unexpected unchecked declaration in {name}.lean")
    shutil.copyfile(root / "lean/Itasca/Generated/FunsExternal.lean",
                    generated / "FunsExternal.lean")
    lean_env = os.environ.copy()
    search_path = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=root / "lean", text=True,
    ).strip()
    lean_env["LEAN_PATH"] = str(output) + os.pathsep + search_path
    for name in ("Types", "FunsExternal", "Funs"):
        source = generated / f"{name}.lean"
        subprocess.run(
            ["lean", "-R", str(output), "-o", str(source.with_suffix(".olean")),
             str(source)],
            cwd=root / "lean", env=lean_env, check=True,
        )
    print("Streaming model extracted and compiled; correctness proofs remain deferred.")


if __name__ == "__main__":
    main()
