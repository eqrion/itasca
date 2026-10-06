# Final Lean migration validation

Review date: 2026-10-06. The active migration branch is `lean-port`; `main`
remains at the pre-port revision until review. The annotated `rocq-baseline`
tag preserves `e7a6ce602de0716de89f955300f711b23bc1403e` with its original
sources, submodule pins, extraction patches, and build instructions.

## Runtime and generation checks

| Check | Result |
| --- | --- |
| `cargo test` | 294 tests and 1 doctest passed. |
| `cargo test --no-default-features` | 294 tests and 1 doctest passed. |
| `cargo check --no-default-features --lib` | Passed. |
| Aeneas regression extraction and generated Lean checks | Namespace shadowing and 48-branch indentation cases passed. |
| Fresh Charon/Aeneas extraction in an isolated Cargo/output directory | `Types.lean`, `Funs.lean`, and the external template matched existing output byte for byte. |
| New `just extract-check` command | Passed; both committed models match and the two external requests have concrete models. |
| SpecTec `spec-check` | Regenerated specification matched byte for byte and compiled. |
| SpecTec `spec-repro` | Both known general transformation defects remain reproducible; this does not claim those defects are fixed. |
| Archived Rocq `just prove` | Existing complete proof build remained up to date and passed. |
| Archived Rocq `just extract-check` | Fresh extraction matched committed theories; no guard/positivity bypasses. |
| Final Lean-only `just verify` after Rocq removal | Passed both Rust configurations, extraction/specification consistency, regressions, audit coverage and the integrated proof build. |

The no-default-feature test run exposed three existing unit-test uses of
unqualified `vec!`. The migration qualifies those three calls as `alloc::vec!`
without moving source lines. No production Rust behavior changed, and both
the Lean and Rocq extractions remain identical to their preceding models.
Three adjacent source-comment references were also updated from the retired
Rocq filenames to the Lean proofs; the final Lean regeneration check covers
those documentation changes too.

The specification suite is part of `cargo test`. Long-running fuzz campaigns
and SpiderMonkey integration tests were not rerun during this migration.

## Proof comparison and trust

The clean Lean build passed **1,981 jobs**, auditing **7,312 Itasca theorem
declarations and 55 adapters**. All 266 implementation/proof modules are reachable
from the audit; the unused generated external template is excluded. No project
axiom, admitted proof, or kernel bypass was introduced. The new import-coverage
and external-model checks run through the default build/extraction commands.
An independent review exercised 26 temporary negative/positive fixtures for
these helpers, including omitted imports, nested comments, strings/quotations,
and nonconcrete external declarations. All expected outcomes passed.

[PARITY.md](../PARITY.md) compares every public guarantee listed in the archived
README with its Lean replacement and records the precise hypothesis changes.
The intended bounded-module/decomposed consumer guarantees are covered.
This is not a proof equating WasmCert-Coq with the generated SpecTec semantics,
and it does not assert literal parity for every auxiliary theorem. In
particular, full raw-expression/module AST uniqueness remains unported;
some arbitrary-environment/oversized-region helper statements are narrower.

The [saved Rocq audit](rocq-trust.txt) is retained from the unchanged proof
baseline. Its headline counts are 41, 48, 51, and 52 assumptions; it reported
zero kernel bypasses. Re-extraction produced no changes, so the expensive
per-theorem Rocq assumption report was not repeated. Lean allows only
`propext`, `Classical.choice`, and `Quot.sound`, rejecting `sorryAx` and domain
axioms. Counts across the two provers measure different things and should not
be compared numerically as equivalent trust units.

## Reproduction

Source pins are in [revisions.json](revisions.json), the submodule gitlinks,
`lean/lean-toolchain`, and the committed Lake manifest. Tests used Rust 1.88.0;
extraction used `nightly-2026-09-17`; proofs used Lean 4.31.0.

Follow [the setup guide](../README.md#setup), then run `just verify`. This runs
both Rust test configurations, Rust/specification regeneration comparisons,
extractor regressions, audit import coverage, and all Lean proofs. Use
`just trust` for the explicit transitive assumption listing. The clean rebuild
for this review set aside the project's old `lean/.lake/build` directory while
retaining pinned dependency caches; it did not rely on prior itasca proof
artifacts. All local source fixes are tracked in [UPSTREAM.md](../../UPSTREAM.md).
