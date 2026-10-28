#!/usr/bin/env python3
"""Size and duplication statistics for a handwritten proof library.

`exec_stats.py [LIB]` prints the metrics tracked by `EXEC_PLAN.md`.
`exec_stats.py timing [LIB]` compares import-only and full elaboration time on a
fixed file sample. Extraction outputs are excluded throughout, and so are oleans
left behind by deleted sources.
"""
from collections import Counter
from pathlib import Path
import re
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
OLEANS = ROOT / ".lake" / "build" / "lib" / "lean"
TIMING_SAMPLE = 20
EXTRACTED = {"Types.lean", "Funs.lean", "FunsExternal_Template.lean"}

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\b\s*([^\s:({\[]*)",
    re.M,
)
THEOREMS = {"theorem", "lemma"}
PLATFORM_BINDER = re.compile(r"\(memory\s*:")
HOST_LAW = re.compile(r"\bHostWorldSound\b")
PROJECTION = re.compile(r"\.[0-9](?:\.[0-9])+")
PROFILE = re.compile(r"Wasm([12])|wasm([12])")


def sources(lib: str) -> list[Path]:
    return sorted(p for p in (ROOT / lib).rglob("*.lean")
                  if not ("Generated" in p.parts and p.name in EXTRACTED))


def module(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def declarations(text: str) -> list[tuple[str, str]]:
    return DECL.findall(text)


def swap_profile(name: str) -> str:
    return PROFILE.sub(lambda m: m.group(0)[:-1] + ("2" if m.group(0)[-1] == "1" else "1"), name)


def profile_duplicates(files: dict[Path, str]) -> tuple[int, int]:
    """Count Wasm1/Wasm2 file pairs and theorem-name pairs within them or across names."""
    by_rel = {p.relative_to(ROOT).as_posix(): p for p in files}
    def theorems(text: str) -> set[str]:
        return {n for k, n in declarations(text) if k in THEOREMS}

    file_pairs = [(p, by_rel[swap_profile(rel)]) for rel, p in by_rel.items()
                  if re.search(r"[Ww]asm1", rel) and swap_profile(rel) in by_rel]
    names = set().union(*(theorems(t) for t in files.values()))
    pairs = {n for n in names if re.search(r"[Ww]asm1", n) and swap_profile(n) in names}
    for a, b in file_pairs:
        pairs |= {f"{a}:{n}" for n in theorems(files[a]) & theorems(files[b])}
    return len(file_pairs), len(pairs)


def stats(lib: str) -> None:
    files = {p: p.read_text() for p in sources(lib)}
    lines = [t.count("\n") for t in files.values()]
    kinds = {p: Counter(k for k, _ in declarations(t)) for p, t in files.items()}
    theorems = {p: sum(c[k] for k in THEOREMS) for p, c in kinds.items()}
    definitions = {p: sum(c.values()) - theorems[p] for p, c in kinds.items()}
    single = sum(1 for p in files if theorems[p] == 1 and definitions[p] == 0)
    docs = sum(1 for t in files.values() if "/-!" in t)
    oleans = [(f.stat().st_size, f) for p in files
              if (f := OLEANS / p.relative_to(ROOT).with_suffix(".olean")).exists()]
    big = sorted((s for s in oleans if s[0] > 10 * 2**20), reverse=True)
    file_pairs, name_pairs = profile_duplicates(files)
    flat = Counter(m.group(1) for t in files.values()
                   for m in re.finditer(r"^namespace (\S+)$", t, re.M))
    widest, width = flat.most_common(1)[0] if flat else ("-", 0)
    gib = lambda n: f"{n / 2**30:.2f} GiB"
    rows = [
        ("Handwritten files / lines", f"{len(files):,} / {sum(lines):,} (median {statistics.median(lines):.0f})"),
        ("Single-theorem files (no definitions)", f"{single:,}"),
        ("Theorems / definitions", f"{sum(theorems.values()):,} / {sum(definitions.values()):,}"),
        ("Module docstrings", f"{docs:,} of {len(files):,}"),
        ("Olean size", f"{gib(sum(s for s, _ in oleans))}; {len(big)} > 10 MiB totalling {gib(sum(s for s, _ in big))}"),
        ("Wasm1/Wasm2 duplicate theorem names / file pairs", f"{name_pairs:,} / {file_pairs:,}"),
        ("`*WithTables*` files", f"{sum(1 for p in files if 'WithTables' in p.name):,}"),
        ("`(memory :` binders / `HostWorldSound` mentions", f"{sum(len(PLATFORM_BINDER.findall(t)) for t in files.values()):,} / {sum(len(HOST_LAW.findall(t)) for t in files.values()):,}"),
        ("`.2.2.1`-style projections", f"{sum(len(PROJECTION.findall(t)) for t in files.values()):,}"),
        ("Widest namespace (files)", f"`{widest}` ({width:,})"),
        ("`maxHeartbeats` / `maxRecDepth` overrides", f"{sum(t.count('maxHeartbeats') for t in files.values()):,} / {sum(t.count('maxRecDepth') for t in files.values()):,}"),
    ]
    print("| Metric | Value |\n| --- | --- |")
    for k, v in rows:
        print(f"| {k} | {v} |")
    print("\nLargest oleans:")
    for size, f in big[:10]:
        print(f"  {size / 2**20:7.1f} MiB  {f.relative_to(OLEANS).with_suffix('')}")


def elapsed(path: Path) -> float:
    start = time.monotonic()
    subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, check=True,
                   stdout=subprocess.DEVNULL)
    return time.monotonic() - start


def timing(lib: str) -> None:
    files = sources(lib)
    sample = files[:: max(1, len(files) // TIMING_SAMPLE)][:TIMING_SAMPLE]
    total_import = total_full = 0.0
    with tempfile.TemporaryDirectory() as tmp:
        for path in sample:
            imports = [l for l in path.read_text().splitlines() if l.startswith("import ")]
            header = Path(tmp) / "Imports.lean"
            header.write_text("\n".join(imports) + "\n")
            load, full = elapsed(header), elapsed(path)
            total_import += load
            total_full += full
            print(f"{load:6.1f}s import  {full:6.1f}s full  {module(path)}")
    n = len(sample)
    print(f"mean over {n} files: {total_import / n:.2f}s import, "
          f"{(total_full - total_import) / n:.2f}s elaboration")


def main(args: list[str]) -> None:
    if args and args[0] == "timing":
        timing(args[1] if len(args) > 1 else "Itasca/Runtime")
    else:
        stats(args[0] if args else "Itasca/Runtime")


if __name__ == "__main__":
    main(sys.argv[1:])
