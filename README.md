# itasca

***veritas caput***

A formally verified streaming WebAssembly 1.0 validator.

## Background

This project was built using Claude extensively. It's meant to be an experiment of AI-assisted formal verification.

Written by Ryan Hunt, who is learning formal verification but is a newbie.

With formal verification it is very easy to be mistaken about what you have proved. I've tried to be as rigorous as I can, but be warned.

The proof statements and their limits are documented below, including the obligations on decomposed and deferred validation consumers.

## Overview

This is a Rust library that implements the Wasm 1.0 decoding and validation algorithm. You can view the [docs here](https://docs.rs/itasca/latest/itasca/).

It implements both a 'whole module' validator, and also a 'decomposed' streaming validator. The interface is compatible with SpiderMonkey's WebAssembly engine and a branch with it integrated is [here](https://github.com/eqrion/firefox/tree/itasca).

The library is verified in Lean against declarative judgments generated from the [SpecTec](https://github.com/zilinc/spectec/tree/lean-backend) WebAssembly specification. It implements Wasm 1.0, with an explicit profile of the generated Wasm 2.0 specification. See [formal verification](#formal-verification) for the exact claims.

To build and test the Rust library:

```sh
cargo build
just test
```

For verification, first follow the [toolchain setup](lean/README.md), then run:

```sh
just extract        # Rust -> Charon LLBC -> generated Lean
just extract-check  # Regenerate separately and compare committed output
just prove          # Check all Lean proofs and the axiom audit
```

See [DEVELOPMENT.md](DEVELOPMENT.md) for the complete workflow and checks required after each kind of change.

## Decomposed module validation

In order to be useful in a real production Wasm engine, we can't just expose a single 'validate module' entry point.

For example SpiderMonkey does the following:
  - It fuses decoding and validation to minimize the size of AST it builds.
  - It validates functions in parallel on other threads.
  - It validates function bodies while building internal compiler IRs.
  - It can validate while bytes are streaming off the network, and are discontiguous.

This library was designed to expose an API compatible with all of the above.

This complicates the proofs and leaves preconditions that the user must follow (these are hypotheses that must be met for the proofs to apply).

The goal is that the preconditions are straightforward to follow and don't require reasoning over the contents of the Wasm module.

The overall sequence of calls must roughly be:
```
// Validate everything all at once.
validate_module() {
  // Validate all sections until the code section.
  validate_env()

  // Validate the code section and call a hook for each entry.
  // Must be called after validate_env, and the hook must call
  // validate_code_entry.
  validate_code() {
    // Validate a single code section entry (i.e. function body).
    validate_code_entry()
  }

  // Validate everything after the code section.
  validate_tail()
}
```

The `validate_code` hook allows for each function to be dispatched to worker threads for parallel validation and compilation. The caller is obligated to just ensure `validate_code_entry` is eventually called and the result reported.

`validate_code_entry` has a hook per-opcode to allow it to be used by a compiler to build an IR. Importantly `validate_code_entry` drives all the validation and the compiler just listens to the results.

Custom sections are reported via hooks on `validate_env/tail`

## Testing

In addition to formal verification, the validator has been conventionally tested.

`/tests/` contains both an ad-hoc unit test suite, along with an import of the Wasm 1.0 spec-test suite.
`/fuzz/` contains a differential fuzzer against the `wasmparser` Rust crate.

It has also been integrated into SpiderMonkey in a [branch](https://github.com/eqrion/firefox/tree/itasca) and passes all of SpiderMonkey's tests.

## Formal verification

The proofs cover the actual extracted public Rust validator, including malformed
input, size guards, streaming loops, visitor dispatch, and final byte-consumption
checks. The pipeline is:

```text
Rust --Charon--> LLBC --Aeneas--> Lean program model
SpecTec Wasm 2.0 source ----------> Lean declarative specification
                                   + independent Wasm 1.0 binary grammar
                                   + handwritten proofs checked by Lean
```

The [Lean guide](lean/README.md) describes the proof architecture, dependencies,
and commands. [The parity review](lean/PARITY.md) maps the previous Rocq claims
to their Lean replacements. [UPSTREAM.md](UPSTREAM.md) tracks the local tool and
specification repairs and the remaining upstream work.

### Reading the guarantees

“Accepts” means the extracted function returns an ordinary `Ok`. “Returns”
means it produces ordinary success or a validation error, without modeled panic,
arithmetic overflow, out-of-bounds access, or divergence. Allocation failure is
outside this model. “Decodes to” uses the independent handwritten binary grammar;
“well typed” uses the generated SpecTec declarative judgments.

| Entry point | Checked guarantees and proof sources |
| --- | --- |
| Whole module | [`module.validate_module.wasm_total` and `wasm_sound`](lean/Itasca/ModuleValidation.lean) prove arbitrary-byte termination and acceptance soundness. The certificate includes the full binary encoding, generated `Module_ok`, the Wasm 1.0 profile, coherent index spaces, and exact public import/export metadata. [`wasm_complete` and `wasm_complete_with_metadata`](lean/Itasca/ModuleCompleteness.lean) derive acceptance directly from independent encoding and declarative typing, within the implementation limits. |
| Function body | [`code.validate_body.wasm_total` and `wasm_sound`](lean/Itasca/WasmSoundness.lean) cover every Wasm 1.0 opcode and arbitrary bytes. [`wasm1_sound`](lean/Itasca/Wasm1Soundness.lean) also establishes the recursive 1.0 profile. [`wasm_complete`](lean/Itasca/WasmComplete.lean) proves completeness from encoding, declarative typing, and that profile. |
| Visiting APIs | [Body acceptance soundness](lean/Itasca/VisitorBodyErasure.lean) holds for arbitrary opcode visitors. [Module acceptance soundness](lean/Itasca/ModuleVisitorTransfer.lean) additionally requires an overridden code-entry hook to accept only entries the validator accepts. [Module termination](lean/Itasca/ModuleVisitorValidation.lean) and [body termination](lean/Itasca/WasmSoundness.lean) require terminating hooks; completeness requires accepting hooks. Acceptance-only theorems do not assume termination of unrelated callback runs. |
| Decomposed APIs | [Entry contracts](lean/Itasca/ModuleDecomposed.lean) derive their environment obligations from an actual accepted environment decode. [Entry completeness](lean/Itasca/ModuleCodeEntryComplete.lean) covers typed entries within the limits. [Composition](lean/Itasca/ModuleRegions.lean) covers adjacent phases on one buffer and exact concatenations of separate environment/code/tail buffers. |
| Deferred workers | [Deferred soundness](lean/Itasca/ModuleDeferredValidation.lean) permits code-entry callbacks to return before validation, provided every recorded entry later validates. [Entry ordering](lean/Itasca/ModuleEntryOrder.lean) proves exactly one obligation per defined function, in index order. Custom callbacks must preserve the work observation when obligations are read from the final visitor state. |
| Callback traces | [Body traces](lean/Itasca/VisitorBodyTrace.lean) identify hook names, order, and original immediates, including float bits and branch-table labels. [Entry traces](lean/Itasca/ModuleEntryTrace.lean) add the function-start context and precise body/local boundaries. [Accepted module traces](lean/Itasca/ModuleTraceValidation.lean) identify custom-section ranges, byte requests, and ordered entry handoffs. [Rejection properties](lean/Itasca/VisitorTraceCorollaries.lean) prove an observed rejecting body callback is last and matches the returned visitor error. |

Body soundness assumes the function's result vector has the API's zero-or-one
result shape. Body termination permits arbitrary caller-supplied environments
and result vectors. Standalone body completeness also requires zero-or-one
results in the environment's stored function signatures. Whole-module theorems
derive these facts, index validity, and cache coherence from the actual module;
they do not assume successful parser steps or prevalidated function bodies.

The binary grammar accounts for nonminimal but valid LEB encodings, strict UTF-8
names, section framing and ordering, grouped local declarations, active segments,
and complete consumption of the input. Float constants retain their raw bits,
including signed zero and NaN payloads. The body context is constructed from the
actual stored environment, locals, and results; it is not an unrelated assumed
specification context.

### Wasm 1.0 profile and limits

The generated specification describes Wasm 2.0. The independent grammar and
[`Profile`](lean/Itasca/ModuleProfile.lean) restrict the result to Wasm 1.0:
scalar value types and 1.0 instruction/section forms, at most one table and one
memory counting imports and definitions together, and at most one function or
block result. The profile also requires unique decoded export names, a condition
missing from the current generated module judgment.

Branch-table targets must have identical signatures, including in unreachable
code. Wasm 2.0 permits some cases through its `BOT` subtype that this 1.0
validator rejects. A [checked counterexample](lean/Itasca/WasmCompletenessBoundary.lean)
shows why 1.0 opcode bytes alone are insufficient for completeness against the
2.0 typing judgment. [Elaboration](lean/Itasca/ModuleElaboration.lean) separately
requires valid function-type references and matching function/code counts.

Completeness respects the actual limits in [src/limits.rs](src/limits.rs):

| Implementation cap | Value |
| --- | ---: |
| Module bytes | 1,073,741,824 |
| Instruction-body bytes, including the final `end` and excluding local declarations | 7,654,321 |
| Declared locals per function, excluding parameters | 50,000 |

These caps are represented by [`ModuleEncodingWithinLimits`](lean/Itasca/ModuleLimits.lean)
and [`CodeEncodingWithinLimits`](lean/Itasca/ModuleCodeLimits.lean). Valid modules
outside them may be rejected. Specification limits, such as the 65,536-page
memory bound, also remain in force.

### Trust boundary

The checked claims rely on the following correspondence with the real program
and specification:

- Charon and Aeneas must translate Rust faithfully. The generated files are
  committed and reproducibly checked; local extractor fixes are source patches
  with regressions, not edits to generated Lean.
- The pinned SpecTec source and its Lean backend must faithfully express the
  intended WebAssembly judgments. Known repairs and gaps are listed in
  [UPSTREAM.md](UPSTREAM.md). Generated typing is supplemented by the explicit
  profile above.
- The handwritten [body grammar](lean/Itasca/WasmBinary.lean),
  [module grammar](lean/Itasca/ModuleBinary.lean), and translations must describe
  the intended binary format and map it to the intended specification syntax.
  The pinned backend does not provide a generated binary-format judgment or an
  executable validator used by these proofs.
- Aeneas's standard-library and loop models, and the concrete local
  [`Vec.pop`/`Vec.is_empty` models](lean/Itasca/Generated/FunsExternal.lean), must
  correspond to Rust. Allocation capacity, allocator behavior, and allocation
  failure are not modeled; the return guarantees assume allocation succeeds.
- Lean's kernel and its standard logical foundations are trusted, as are the
  compiler/runtime/hardware when running the resulting Rust library.

There are **no project-specific axioms or kernel bypasses** in the checked proof
dependencies. [`Audit.lean`](lean/Itasca/Audit.lean) checks every imported Itasca
theorem transitively, plus the semantic adapters and public predicates. It permits
only `propext`, `Classical.choice`, and `Quot.sound`, and rejects `sorryAx` and
other domain axioms. Upstream's generated file still contains unfinished lemmas
and opaque execution definitions; the audited proofs do not depend on them.
Run `just trust` to check the current dependency report.

### Scope and retained baseline

These are validation and decoding proofs, not proofs of WebAssembly execution,
compiler correctness, a consumer's generated IR, or actual thread scheduling.
Deferred soundness is conditional on completing all recorded validation work.
Body callback rejection is characterized; a complete trace specification for
rejected whole-module runs and a general specification of which validation error
must be selected are not claimed. Individual rejection regressions do check exact
errors. An arbitrary overriding code-entry callback can accept invalid code;
typing follows only under its validation contract or completed worker obligations.

The [comparison](lean/PARITY.md) records narrower premises for some
arbitrary-environment and oversized-region helper statements. Full uniqueness
of the independently encoded structured-body and raw-module ASTs remains an
unported auxiliary guarantee; flat instruction/token decoding uniqueness is
proved. No equivalence theorem between the complete Rocq and SpecTec
specifications is claimed.

Lean is the active verification pipeline. The previous Rocq implementation,
proofs, and toolchain are retained in the annotated `rocq-baseline` tag at
`e7a6ce602de0716de89f955300f711b23bc1403e`; they are not a dependency of the Lean
build. The saved [baseline revisions](lean/baseline/revisions.json) and
[Rocq assumption report](lean/baseline/rocq-trust.txt) remain available for comparison.
