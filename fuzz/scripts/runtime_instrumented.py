#!/usr/bin/env python3
"""Short AddressSanitizer and coverage-instrumented differential campaigns."""

import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cargo-fuzz", default="cargo-fuzz")
    parser.add_argument("--seconds", type=int, default=60)
    parser.add_argument("--target-dir", type=Path)
    options = parser.parse_args()
    if options.seconds <= 0:
        parser.error("--seconds must be positive")
    work = Path(tempfile.mkdtemp(prefix="itasca-instrumented-"))
    target_dir = options.target_dir or (ROOT / "fuzz/target/instrumented")
    environment = dict(os.environ, RUSTUP_TOOLCHAIN="nightly-2026-09-17", ITASCA_FUZZ_REPORT_EACH="1")
    print(f"Instrumented inputs, logs, and failure artifacts: {work}", flush=True)
    targets = ["wasm1_execute", "wasm2_execute", "runtime_linking",
               "runtime_numeric", "runtime_stateful", "runtime_compile"]
    for number, target in enumerate(targets, 1):
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
        command = [options.cargo_fuzz, "fuzz", "run", "--dev", "--target-dir", str(target_dir),
                   target, str(corpus), "--", f"-seed={number}",
                   f"-max_total_time={options.seconds}", "-timeout=10", "-rss_limit_mb=2048",
                   "-max_len=65536" if target == "runtime_compile" else "-max_len=4096",
                   f"-artifact_prefix={corpus}/"]
        log = work / f"{target}.log"
        with log.open("w") as output:
            result = subprocess.run(command, cwd=ROOT, env=environment, stdout=output, stderr=subprocess.STDOUT)
        text = log.read_text()
        counts = re.findall(r"execution coverage total=.*", text)
        coverage = re.findall(r"#\d+\s+DONE.*", text)
        if result.returncode != 0 or not counts or not coverage:
            print(text[-16000:])
            raise SystemExit(f"{target} failed or did not finish; see {log}")
        print(f"{target}: {coverage[-1]}\n{counts[-1]}", flush=True)
    print("All six instrumented campaigns passed.")


if __name__ == "__main__":
    main()
