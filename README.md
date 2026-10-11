# itasca

***veritas caput***

A formally verified streaming WebAssembly validator for Wasm 1.0 and a multi-value extension profile.

Both profiles use the same streaming entry point. Select `ValidationProfile::Wasm1`
or `ValidationProfile::MultiValue` explicitly in `validate_module(bytes, profile)`
or `stream::validate_streaming`. The multi-value profile supports multi-result
functions, indexed block signatures with parameters, and Wasm 2.0 branch-table
typing, including parallel workers and compiler callbacks.

Whole-module and streaming totality, soundness, and completeness theorems apply
to both profiles through shared, profile-parameterized proofs. `MultiValue` is
the first supported Wasm 2.0 feature set, not a claim of full Wasm 2.0 support.

## Background

This project was built using Claude extensively. It's meant to be an experiment of AI-assisted formal verification.

Written by Ryan Hunt, who is learning formal verification but is a newbie.

With formal verification it is very easy to be mistaken about what you have proved. I've tried to be as rigorous as I can, but be warned.

The proof statements and their limits are documented below, including the obligations on streaming sources and workers.

## Overview

This Rust library implements decoding and validation for Wasm 1.0 and the multi-value profile. You can view the [docs here](https://docs.rs/itasca/latest/itasca/).

`validate_streaming` is the module driver. `validate_module(bytes, profile)` supplies a contiguous source and a synchronous worker to that same driver. Component entry points support compilers that consume validated operators. An experimental SpiderMonkey integration is available [here](https://github.com/eqrion/firefox/tree/itasca); external consumers must migrate separately when APIs change.

The library is verified in Lean against declarative judgments generated from the [SpecTec](https://github.com/zilinc/spectec/tree/lean-backend) WebAssembly specification. Both supported profiles use explicit restrictions of the generated Wasm 2.0 specification. See [formal verification](#formal-verification) for the exact claims.

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

## Streaming and component validation

The streaming API supports discontiguous input, parallel function validation,
and compiler callbacks that build IR while validation runs. The driver owns
phase order, framing, pending batch identities, and final acceptance:

```text
validate_module(bytes, profile)
  -> contiguous source + synchronous worker
     -> validate_streaming(..., profile, ...)
        -> validate_env_with(ModuleVisitor)
        -> frame and submit CodeBatch work carrying profile
           -> CodeBatch::validate_func(OpVisitor)
              -> validate_code_entry_with
                 -> validate_body_with
        -> validate_tail_with(ModuleVisitor)
        -> retire every pending batch
```

Workers may complete in any order. A batch has independent dispatch and
validation cursors; dispatching an entry does not validate it. Workers advance
validation through `CodeBatch::validate_func`, or use `validate_all`. The driver
checks each returned batch's module ID, pending batch ID, and successful finish.
Only a successful driver result certifies a module. The profile is fixed when
the driver issues each batch and is used by every worker.

`ModuleVisitor` reports custom sections from the environment and tail parsers.
`OpVisitor` reports validated function context and body operators. Control hooks
carry `signature::BlockType`; branch hooks carry `signature::ResultType`, with
loop labels referring to parameters. Indexed descriptors resolve against the
function environment. The component
APIs remain available, but calling one alone does not certify a whole module or
discharge a pending batch. Sources must present coherent bytes, and environments
and input buffers must outlive workers, including after an error. See the
[embedding obligations](DEVELOPMENT.md#embedding-obligations).

The old `validate_module_with`, `validate_code`, `validate_code_with`,
`CodeVisitor`, `ValidatingCodeVisitor`, and `code_section`/`CodeSection` APIs have
been removed. Streaming consumers use `StreamingVisitor`; synchronous consumers
use `validate_module`. The old deferred code-walk and whole-module callback-trace
contracts were retired with those APIs. Body and entry callback traces remain
proved; the new streaming protocol has its own batch and phase contracts.

## Testing

In addition to formal verification, the validator has been conventionally tested.

`/tests/` contains focused tests, imported Wasm 1.0 specification binaries,
and a [pinned Wasm 2.0 control-flow corpus](tests/spec2/README.md). The
multi-value tests also compare generated modules and mutated binaries against
wasmparser with the same feature selection.
`/fuzz/` contains a differential fuzzer against the `wasmparser` Rust crate.

It has also been integrated into SpiderMonkey in an experimental
[branch](https://github.com/eqrion/firefox/tree/itasca). See the
[integration notes](DEVELOPMENT.md#streaming-api) for its current
API, verification status, and limitations.

## Formal verification

The whole-module proofs cover `stream::validate_streaming` and its synchronous
whole-module wrapper for both explicit `ValidationProfile` selections. The generic
driver has explicit source and scheduler contracts; the contiguous wrapper
discharges them for its concrete adapters.

The proofs cover the actual extracted public Rust validator, including malformed
input, size guards, streaming loops, visitor dispatch, and final byte-consumption
checks. The pipeline is:

```text
Rust --Charon--> LLBC --Aeneas--> Lean program model
SpecTec Wasm 2.0 source ----------> Lean declarative specification
                                   + independent profile-selected binary grammar
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
| Whole module | [`module.validate_module.profile_total` and `profile_sound`](lean/Itasca/Module/ModuleValidation.lean) prove arbitrary-byte termination and acceptance soundness through the synchronous streaming adapter. The certificate includes full binary encoding, generated `Module_ok`, the selected profile, coherent index spaces, and exact public import/export metadata. [`profile_complete` and `profile_complete_with_metadata`](lean/Itasca/Module/ModuleCompleteness.lean) derive acceptance from independent encoding and declarative typing within the implementation limits. |
| Generic streaming | [`stream.validate_streaming.profile_sound`](lean/Itasca/Stream/StreamValidation.lean) requires coherent source views and provenance linking returned workers to issued batches. [`profile_total`](lean/Itasca/Stream/StreamDriverTotal.lean) requires returning callbacks, even when returned batches are malformed or unfinished. [`profile_complete`](lean/Itasca/Stream/StreamDriverComplete.lean) requires independent valid module bytes, available canonical regions, and an accepting scheduler policy. Its execution witness identifies the exact delivered tail. |
| Batches and scheduling | [Actual batch reachability and successful finish](lean/Itasca/Stream/StreamBatch.lean) derive ordered entry validation and exact byte coverage. [Submission](lean/Itasca/Stream/StreamSubmission.lean) and [retirement](lean/Itasca/Stream/StreamRetirement.lean) connect this evidence to the actual pending IDs and driver checks, permitting arbitrary completion order. [Worker completeness](lean/Itasca/Stream/StreamBatchComplete.lean) runs the real validation loop on independently typed entry encodings. |
| Function body | [`code.validate_body.wasm_total` and `wasm_sound`](lean/Itasca/Body/WasmSoundness.lean) cover every Wasm 1.0 opcode and arbitrary bytes. [`wasm1_sound`](lean/Itasca/Body/Wasm1Soundness.lean) also establishes the recursive 1.0 profile. [`wasm_complete`](lean/Itasca/Body/WasmComplete.lean) proves completeness from encoding, declarative typing, and that profile. |
| Multi-value function body | [`multi_value.validate_body.wasm_total`](lean/Itasca/MultiValue/BodyTotal.lean) and [`wasm_sound`](lean/Itasca/MultiValue/Soundness.lean) cover arbitrary bytes, environments, locals, and type indices. [`wasm_complete` and `wasm_accepts_iff`](lean/Itasca/MultiValue/Complete.lean) connect acceptance to independent encoding and generated Wasm 2.0 typing within body-byte and signature limits. The grammar includes scalar instructions, indexed block parameters/results, and Wasm 2.0 branch-table typing. |
| Visiting components | [Shared body contracts](lean/Itasca/Profile/BodyVisitor.lean) and [entry soundness](lean/Itasca/Profile/EntrySound.lean) cover arbitrary opcode visitors under either profile. Termination requires returning hooks; completeness requires accepting hooks. [Entry contracts](lean/Itasca/Module/ModuleDecomposed.lean) derive environment obligations from an actual environment decode, and [entry completeness](lean/Itasca/Profile/EntryComplete.lean) covers independently typed entries within the limits. |
| Wasm 1.0 callback traces | [Body traces](lean/Itasca/Visitor/VisitorBodyTrace.lean) identify hook names, order, and original immediates, including float bits and branch-table labels. [Entry traces](lean/Itasca/Module/ModuleEntryTrace.lean) add the function-start context and precise body/local boundaries. [Rejection properties](lean/Itasca/Visitor/VisitorTraceCorollaries.lean) prove an observed rejecting body callback is last and matches the returned visitor error. |

The `profile_*` module and streaming theorems quantify over the selected profile.
Existing `wasm_*` names remain Wasm 1.0 specializations with their prior contracts.

Soundness, totality, and completeness have separate streaming premises.
[Source coherence](lean/Itasca/Stream/StreamSource.lean) fixes logical environment,
code, and tail bytes and relates successful range reads to those bytes; it does
not assume valid input or available reads. [Scheduler provenance](lean/Itasca/Stream/StreamScheduler.lean)
relates worker states to actual batch operations and is preserved through every
callback. It does not assume a polled batch is finished: the driver checks that.
Returning callbacks suffice for totality without either soundness premise.

Completeness additionally uses available regions from the canonical split and
an [accepting scheduler policy](lean/Itasca/Stream/StreamAcceptingScheduler.lean).
The checked policy permits any positive batch settings and arbitrary return
order, with returned workers produced by actual `validate_all` executions.
Their successful finish is derived from independent byte encoding and typing.
This is one sufficient worker policy, not a characterization of every possible
worker strategy. The private synchronous worker discharges these obligations.

Wasm 1.0 body soundness assumes the function's result vector has the API's zero-or-one
result shape. Body termination permits arbitrary caller-supplied environments
and result vectors. Standalone body completeness also requires zero-or-one
results in the environment's stored function signatures. Whole-module theorems
derive these facts, index validity, and cache coherence from the actual module;
they do not assume successful parser steps or prevalidated function bodies.

Multi-value body soundness selects the function signature from the actual type
index and permits arbitrary result arity. Completeness requires at most 1000
parameters and 1000 results in each stored type and direct-call signature, plus
the existing body-byte limit. It covers loop input labels, parameterized blocks,
both forms of `if`, and branch tables with a common `BOT` subtype. Its independent
grammar does not include other Wasm 2.0 instruction proposals. The shared
whole-module proofs derive environment validity and cache coherence from the
actual environment parser and compose these body certificates with module typing.

The binary grammar accounts for nonminimal but valid LEB encodings, strict UTF-8
names, section framing and ordering, grouped local declarations, active segments,
and complete consumption of the input. Float constants retain their raw bits,
including signed zero and NaN payloads. The body context is constructed from the
actual stored environment, locals, and results; it is not an unrelated assumed
specification context.

### Profiles and limits

The generated specification describes Wasm 2.0. The independent grammar and
[`Profile`](lean/Itasca/Module/ModuleProfile.lean) select the supported language.
Both profiles retain scalar value types, at most one table and one memory
counting imports and definitions together, and unique decoded export names,
a condition missing from the current generated module judgment. Wasm 1.0
also requires its instruction/section forms and at most one function or block result.

`MultiValue` permits multiple function results and indexed block signatures with
parameters and results. Its active element/data segments use Wasm 2.0 flags:
0 selects index zero; 2 supplies an explicit index, with an element-kind byte
for explicit element segments. Wasm 1.0 retains its original segment-index
grammar. Passive/declarative segments and other Wasm 2.0 proposals are not covered.

Wasm 1.0 branch-table targets must have identical signatures, including in unreachable
code. Wasm 2.0 permits some cases through its `BOT` subtype that this 1.0
validator rejects. A [checked counterexample](lean/Itasca/Examples/WasmCompletenessBoundary.lean)
shows why 1.0 opcode bytes alone are insufficient for completeness against the
2.0 typing judgment. [Elaboration](lean/Itasca/Module/ModuleElaboration.lean) separately
requires valid function-type references and matching function/code counts.

Completeness respects the actual limits in [src/limits.rs](src/limits.rs):

| Implementation cap | Value |
| --- | ---: |
| Module bytes | 1,073,741,824 |
| Instruction-body bytes, including the final `end` and excluding local declarations | 7,654,321 |
| Declared locals per function, excluding parameters | 50,000 |

These byte/local caps are represented by [`ModuleEncodingWithinLimits`](lean/Itasca/Module/ModuleLimits.lean)
and [`Profile.CodeEncodingWithinLimits`](lean/Itasca/Profile/CodeEntry.lean).
Multi-value completeness additionally requires `ModuleSignaturesWithinLimits`: at
most 1000 parameters and 1000 results per declared signature. Wasm 1.0 retains
its prior parameter behavior. Signature allocation caps are separate from
language validity; otherwise valid modules outside the implementation limits
may be rejected. Specification limits, such as the 65,536-page memory bound,
also remain in force.

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
- The handwritten [body grammar](lean/Itasca/Binary/WasmBinary.lean),
  [module grammar](lean/Itasca/Binary/ModuleBinary.lean), and translations must describe
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
dependencies. [`Audit.lean`](lean/Itasca/Audit.lean) checks every declaration
originating in an imported Itasca module, including private helpers, definitions,
semantic adapters, and external models in other namespaces. It permits
only `propext`, `Classical.choice`, and `Quot.sound`, and rejects `sorryAx` and
other domain axioms. Upstream's generated file still contains unfinished lemmas
and opaque execution definitions; the audited proofs do not depend on them.
Run `just trust` to check the current dependency report.

### Scope and retained baseline

These are validation and decoding proofs, not proofs of WebAssembly execution,
compiler correctness, a consumer's generated IR, actual thread scheduling,
network progress, or FFI memory safety. Generic streaming soundness depends on
the source and worker provenance contracts; generic totality depends on ordinary
callback returns. A worker or compiler callback may reject an otherwise valid
module. Body callback rejection is characterized; a complete callback trace for
rejected whole-module runs and a general specification of which validation error
must be selected are not claimed. Individual rejection regressions do check exact
errors. The API consolidation changes no trust-base assumptions.

The [comparison](lean/PARITY.md) records narrower premises for some
arbitrary-environment and oversized-region helper statements. Independent
[structured-body decoding](lean/Itasca/Binary/WasmBinaryUnique.lean) and
[raw-module decoding](lean/Itasca/Binary/ModuleBinaryUnique.lean) are unique, with no
typing or implementation-size premises. No equivalence theorem between the
complete Rocq and SpecTec specifications is claimed.

Lean is the active verification pipeline. The previous Rocq implementation,
proofs, and toolchain are retained in the annotated `rocq-baseline` tag at
`e7a6ce602de0716de89f955300f711b23bc1403e`; they are not a dependency of the Lean
build. The saved [baseline revisions](lean/baseline/revisions.json) and
[Rocq assumption report](lean/baseline/rocq-trust.txt) remain available for comparison.
