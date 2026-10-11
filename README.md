# itasca

***veritas caput***

A streaming WebAssembly validator written in Rust and verified in Lean. It
supports the WebAssembly 1.0 and 2.0 core profiles, including
parallel function validation and compiler callbacks. Both profiles have
whole-module termination, soundness, and completeness proofs.

This is an experiment in AI-assisted formal verification by Ryan Hunt, built
extensively with Claude. The proof statements and their trust boundary are
part of the project: read [formal verification](#formal-verification) before
relying on a guarantee.

## Usage

```rust
let bytes = b"\x00asm\x01\x00\x00\x00";
let module = itasca::validate_module(bytes, itasca::ValidationProfile::Wasm1)?;
let imports = itasca::import_types(module.env())?;
let exports = itasca::export_types(module.env())?;
```

`validate_module` accepts arbitrary bytes, validates the complete module, and
returns read-only declarations and data segments. `Module::env`, `Module::tail`,
and the `Env` accessors expose metadata without allowing callers to change the
validated environment. Import and export types are resolved in declaration order.
The crate supports `no_std` with `alloc` when default features are disabled.

Select a profile explicitly:

| Profile | Supported language |
| --- | --- |
| `ValidationProfile::Wasm1` | WebAssembly 1.0, including single-result functions and blocks, original active-segment encodings, and identical branch-table target signatures. |
| `ValidationProfile::Wasm2` | WebAssembly Core 2.0: multi-value control, sign extension, saturating conversions, reference types, multiple tables, bulk memory, passive and declarative segments, and all 236 SIMD instructions. |

Both profiles allow at most one memory, counting imports and definitions
together, and require unique decoded export names. Wasm 1.0 permits one table;
Wasm 2.0 permits multiple tables of `funcref` or `externref`. Constant expressions
contain one permitted constant, reference instruction, or read of an immutable
imported global, according to the selected profile. Proposals added after Core
2.0, including relaxed SIMD, are outside these profiles.

## Streaming and callbacks

`validate_streaming` is the shared module driver. `validate_module`
supplies its private contiguous source and synchronous worker. Advanced consumers
implement `Source` and `StreamingVisitor` to provide separate
input regions and schedule the issued `CodeBatch` workers.

The driver decodes the environment, submits code batches, validates the tail,
and retires every outstanding batch before accepting. Workers may finish in any
order. `CodeBatch::next_entry` frames entries for dispatch;
`CodeBatch::validate_func` validates them with an `OpVisitor` and retains the
first error. The driver checks module identity, pending batch identity, complete
validation, and exact byte coverage.

`OpVisitor` reports function context and decoded operators. `ModuleVisitor`
reports custom sections. Callback errors can reject valid input. Metadata or
operators observed before the driver returns successfully do not certify a
complete module. Sources must provide coherent bytes, invocation IDs must be
unique among workers sharing a scheduler, and borrowed storage must outlive
workers even after an error. See the
[embedding contract](DEVELOPMENT.md#streaming-contract).

Implementation modules, raw body/environment/entry/tail validators, opcode
constants, and dispatch macros are private. Consumers use the crate's explicit
root exports, including all streaming types and entry points. The duplicate
`validate_module_with_profile` spelling has been removed; use
`validate_module(bytes, profile)`.

## Formal verification

The checked pipeline is:

```text
Rust --Charon--> LLBC --Aeneas--> Lean program model
SpecTec Wasm 2.0 source ----------> Lean declarative judgments
Independent binary grammar ------> exact bytes and selected profile
Handwritten Lean proofs ----------> validator guarantees
```

“Accepts” means the extracted function returns ordinary `Ok`. “Terminates”
means it returns success or an error without modeled panic, arithmetic overflow,
out-of-bounds access, or divergence. Allocation failure is outside the model.
“Well typed” refers to the generated SpecTec declarative judgments; byte
provenance comes from the independent handwritten binary grammar.

| Entry point | Guarantee |
| --- | --- |
| `validate_module` | Arbitrary bytes terminate. Acceptance establishes exact module encoding, generated `Module_ok`, the selected profile, coherent index spaces, and exact returned metadata. Independently encoded and typed modules within the limits are accepted. |
| `validate_streaming` | Soundness requires coherent source views and worker provenance. Termination requires returning callbacks. Completeness additionally requires available canonical input regions and an accepting scheduler policy. |
| `CodeBatch::validate_func` and visitors | Batch proofs connect actual entry validations to ordered function coverage. Shared body and entry proofs establish typing under both profiles. Wasm 1.0 trace proofs identify callback names, order, immediates, and an observed rejecting callback's stopping behavior. |

The [Lean guide](lean/README.md#proof-contracts) links these statements to their
source files and spells out their premises. Whole-module completeness starts
from independent encoding, elaboration, typing, profile restrictions, and
resource bounds. It does not assume parser success or prevalidated bodies.

The grammar covers nonminimal valid LEB encodings, strict UTF-8, section order
and framing, grouped locals, active/passive/declarative segments, data-count
sections, and complete input consumption. Float and vector immediates preserve
their raw bits. Independent body and module decoding are unique without typing or implementation-size premises.

### Implementation limits

Completeness applies within the caps in [src/limits.rs](src/limits.rs):

| Resource | Limit |
| --- | ---: |
| Complete module bytes | 1,073,741,824 |
| Instruction-body bytes, including final `end`, excluding local declarations | 7,654,321 |
| Declared locals per function, excluding parameters | 50,000 |
| Parameters per signature in the Wasm 2.0 profile | 1,000 |
| Results per signature in the Wasm 2.0 profile | 1,000 |

Wasm 1.0 retains its single-result restriction and existing parameter behavior.
Resource caps are separate from language validity; otherwise valid modules may
exceed them. Specification bounds, including 65,536 memory pages, also apply.

### Trust boundary

The proofs depend on faithful Rust translation by Charon and Aeneas, faithful
specification generation by SpecTec, and the correspondence of handwritten
grammars and type translations with WebAssembly. They also rely on Aeneas's
standard-library and loop models, including the local concrete models of
`Vec.pop` and `Vec.is_empty`. Allocation capacity and allocator failure are not
modeled. Lean's kernel and standard logical foundations are trusted, together
with the compiler, runtime, and hardware used to run the Rust library.

Generated Rust models and the specification are committed and reproducibly
checked. Local tool/specification repairs are versioned [source patches](patches),
with their scope described in the [Lean guide](lean/README.md#source-patches).
The explicit profile supplements gaps in the generated module judgment, including
export-name uniqueness. The independent
[declared-reference condition](lean/Itasca/Profile/DeclaredReferences.lean) requires
every `ref.func` target to occur in the module outside function definitions and
the start declaration. This supplements the pinned model's missing reference
declaration context without modifying its generated typing rules. Elaboration
checks type references and function/code counts. The independent SIMD grammar
also distinguishes the two load-zero encodings duplicated in the pinned binary
table, as documented in the [Lean guide](lean/README.md#expanding-the-supported-profile).

[Itasca.Audit](lean/Itasca/Audit.lean) checks every declaration originating in
an imported local module, including private helpers, generated auxiliaries,
proof-bearing definitions, and external models. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. There are no project-specific
axioms or kernel bypasses in the checked dependencies. Unfinished upstream lemmas
and opaque execution models are excluded from those dependencies.

These guarantees cover validation and decoding. They do not establish Wasm
execution, compiler IR correctness, OS scheduling, network progress, or FFI memory
safety. Generic streaming retains its source and worker contracts. A general
choice of error variant and complete traces of rejected whole-module runs are
not specified. The earlier Rocq implementation is archived under the
`rocq-baseline` tag and is not an active build dependency.

## Development

```sh
cargo build
just test         # Default and no-default-feature corpus tests
```

The retained tests use the Wasm 1.0 specification corpus and a
[complete pinned Wasm 2.0 corpus](tests/spec2/README.md), with wasmparser as
an independent oracle. [fuzz](fuzz) contains differential byte and generated-module
fuzzers. Lean examples check typing, malformed inputs, traces, and worker protocol
behavior. External integrations have their own validation and lifetime obligations.

See [DEVELOPMENT.md](DEVELOPMENT.md) for the source layout and change workflow,
[lean/README.md](lean/README.md) for verification setup and proof architecture,
and [AGENTS.md](AGENTS.md) for coding-agent requirements.
