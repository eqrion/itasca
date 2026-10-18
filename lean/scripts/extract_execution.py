#!/usr/bin/env python3
"""Extract the complete generic runtime while reusing the validator model."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess

from execution_reuse import build_map

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean"
BUILD = LEAN / ".build"
CHARON = ROOT / "vendor/aeneas-lean/charon/charon/target/release/charon"
AENEAS = ROOT / "vendor/aeneas-lean/src/_build/default/main.exe"
LLBC = BUILD / "exec.llbc"
MAPPING = BUILD / "exec-reuse.json"


def run(args: list[str | Path], *, cwd: Path = LEAN, env: dict | None = None) -> None:
    subprocess.run([str(arg) for arg in args], cwd=cwd, env=env, check=True)


def extract_llbc() -> None:
    mapping = build_map(json.loads((BUILD / "itasca.llbc").read_text()),
                        (LEAN / "Itasca/Generated/Types.lean").read_text())
    MAPPING.write_text(json.dumps(mapping, indent=2) + "\n")
    flags = ["--preset=aeneas", "--sysroot=default", "--rustc-arg=--cfg=charon",
             "--rustc-arg=--cfg=charon_exec",
             "--exclude={impl core::clone::Clone for _}",
             "--exclude={impl core::marker::Copy for _}",
             "--include=core::marker::{impl core::marker::Copy for u8}",
             "--include=core::clone::impls::{impl core::clone::Clone for u8}",
             "--start-from=itasca::runtime"]
    flags.extend(f"--opaque=itasca::{module}" for module in
                 ("code", "module", "stream", "signature", "types", "error"))
    flags.extend(f"--include={item['rust']}" for item in mapping["types"])
    env = dict(os.environ)
    env["RUSTUP_TOOLCHAIN"] = "nightly-2026-09-17"
    env["CARGO_TARGET_DIR"] = str(BUILD / "cargo")
    run([CHARON, "cargo", *flags, f"--dest-file={LLBC}"], cwd=ROOT, env=env)


def translate(destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    run([AENEAS, "-backend", "lean", LLBC, "-dest", destination,
         "-subdir", "/Exec/Generated", "-namespace", "Exec", "-split-files",
         "-no-progress-bar", "-strict-joins", "-sequential", "-abort-on-error",
         "-skip-bottom-storage-dead", "-reuse-definitions", MAPPING])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("llbc", "translate", "check"))
    args = parser.parse_args()
    if args.command == "llbc":
        extract_llbc()
        return
    destination = LEAN if args.command == "translate" else BUILD / "extract-check"
    translate(destination)
    generated = destination / "Exec/Generated"
    if args.command == "check":
        for name in ("Types.lean", "Funs.lean"):
            if (generated / name).read_bytes() != (LEAN / "Exec/Generated" / name).read_bytes():
                raise SystemExit(f"Stale generated execution model: Exec/Generated/{name}")
    run(["python3", LEAN / "scripts/check_externals.py",
         generated / "FunsExternal_Template.lean",
         LEAN / "Exec/Generated/FunsExternal.lean",
         LEAN / "Itasca/Generated/FunsExternal.lean"])


if __name__ == "__main__":
    main()
