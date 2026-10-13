#!/usr/bin/env python3
"""Reproducible bounded execution smoke; intentionally not coverage instrumented."""

import os
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
TARGETS = [
    "wasm1_execute", "wasm2_execute", "runtime_linking",
    "runtime_stateful", "runtime_numeric", "runtime_compile",
]


def main():
    subprocess.run(
        ["cargo", "build", "--manifest-path", str(ROOT / "fuzz/Cargo.toml"), "--bins"],
        cwd=ROOT, check=True,
    )
    work = Path(tempfile.mkdtemp(prefix="itasca-runtime-smoke-"))
    target_dir = Path(os.environ.get("CARGO_TARGET_DIR", ROOT / "fuzz/target"))
    print(f"Smoke inputs, logs, and any failure artifacts: {work}", flush=True)
    for number, target in enumerate(TARGETS, 1):
        corpus = work / target
        corpus.mkdir()
        if target == "runtime_compile":
            for index, fixture in enumerate(sorted((ROOT / "tests/spec/valid").glob("*.wasm"))[:100]):
                for profile in (0, 1):
                    (corpus / f"seed-{profile}-{index}").write_bytes(bytes([profile]) + fixture.read_bytes())
        else:
            for seed in range(64):
                state = seed + 1
                data = bytearray()
                for _ in range(1024 + seed * 16):
                    state = (state * 6364136223846793005 + 1) % (1 << 64)
                    data.append((state >> 32) & 255)
                (corpus / f"seed-{seed}").write_bytes(data)
        log = work / f"{target}.log"
        command = [
            str(target_dir / "debug" / target), "-runs=1024", f"-seed={number}",
            "-max_len=65536" if target == "runtime_compile" else "-max_len=4096",
            f"-artifact_prefix={corpus}/", str(corpus),
        ]
        with log.open("w") as output:
            result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        text = log.read_text()
        reports = re.findall(r"execution coverage total=1024.*", text)
        if result.returncode != 0 or not reports:
            print(text)
            raise SystemExit(f"{target} failed or did not report complete accounting; see {log}")
        print(f"{target}: {reports[-1]}", flush=True)
    print("All six bounded smoke targets passed; use cargo-fuzz for an instrumented campaign.")


if __name__ == "__main__":
    main()
