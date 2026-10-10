# Development

The active pipeline is Rust → Charon → Aeneas → Lean. The proofs target
SpecTec's generated declarative typing judgments with an independent binary
grammar and explicit Wasm 1.0 restrictions. Read the
[public guarantees](README.md#formal-verification),
[Lean architecture/setup](lean/README.md), and [Rocq comparison](lean/PARITY.md).

## Layout

| Path | Purpose |
| --- | --- |
| `src/module.rs` | Environment, code-entry/section, tail and whole-module validation; visitors. |
| `src/code.rs` | Streaming body validator and opcode dispatch. |
| `src/stream.rs` | Streaming and parallel module driver; extracted, not yet proved. |
| `src/reader.rs`, `types.rs`, `limits.rs`, `error.rs` | Byte readers, API types, implementation bounds and errors. |
| `lean/Itasca/Generated/Types.lean`, `Funs.lean` | Committed Aeneas extraction; never edit by hand. |
| `lean/Itasca/Generated/FunsExternal.lean` | Handwritten concrete models of `Vec.pop` and `Vec.is_empty`. |
| `lean/Itasca/Wasm*.lean`, `Visitor*.lean` | Body grammar, typing, completeness and callback proofs. |
| `lean/Itasca/Module*.lean` | Module parsing/typing, metadata, completeness and consumer APIs. |
| `lean/Itasca/Audit.lean` | Transitive theorem/adapter axiom audit. |
| `lean/SpecTec/wasm2.0.lean` | Specification regenerated from pinned sources and patches. |
| `lean/Makefile`, `lake-manifest.json`, `lean-toolchain` | Extraction, generation and pinned Lean dependencies. |
| `vendor/aeneas-lean`, `vendor/spectec` | Pinned upstream source checkouts. |
| `patches/`, `lean/upstream/`, `UPSTREAM.md` | Source patches, reproducers and submission tracker. |
| `tests/` | Rust tests and extracted Wasm 1.0 specification cases. |
| `tests/third_party/wasm-spec` | Specification tests pinned to `wg-1.0`. |
| `examples/wast_extract.rs`, `tests/support/` | Fixture generation and shared helpers. |
| `fuzz/` | Differential fuzzers against wasmparser. |
| `lean/baseline/` | Rocq revision pins, assumption report and final validation record. |

## Setup and routine checks

Follow [lean/README.md#setup](lean/README.md#setup) to install the pinned Rust,
Lean and OCaml toolchains and initialize dependencies. No Rocq compiler or
WasmCert-Coq checkout is needed. Source patches apply automatically; upstream
working trees are expected to be patched while their commit pins stay fixed.

```sh
cargo test
cargo test --no-default-features
just extract                 # Regenerate after Rust changes
just extract-check           # Regenerate separately and compare models
just check Itasca.ModuleValidation # One module and dependencies
just prove                   # Integrated build, import coverage and axiom audit
just trust                   # Rerun the transitive axiom report
just spec-check              # Regenerate and compare the specification
just regressions             # Aeneas extraction regression cases
just verify                  # Full verification sequence
```

`just lean-extract` and `just lean-prove` remain aliases. Reuse `lean/.lake/`
and `lean/.build/` during iteration. `just clean` removes only this project's
Lean build outputs, preserving downloaded dependencies. Scratch files belong
in `$TMPDIR`. New proof modules must be imported transitively by `Itasca.Audit`;
`just prove` rejects an omitted file before building.

Generated models are committed. Consistency checks write to ignored build
directories and fail on differences instead of silently updating sources.
An intentional specification update uses `make -C lean spec-update`, followed
by proof review and a full build. Run `lake update` only for an intentional
dependency update; ordinary builds use the committed manifest.

## Rust extraction constraints

These are retained implementation/proof constraints, not a claim that every
alternative is unsupported by the current backend. Changing one requires an
extraction experiment and corresponding proofs.

- Use safe Rust; no raw pointers or `unsafe`.
- Thread `data` and cursors explicitly instead of storing borrows in structures.
  Prefer an end position to a new slice unless its exact extent is part of a
  theorem.
- Use `match` for opcode and binary-tag dispatch, including grouped literal
  patterns and byte ranges. The Lean backend supports these; the archived Rocq
  backend's dispatch chains are no longer required.
- Use explicit loop counters; avoid iterators, closures, labeled control flow,
  and returns from nested loops.
- Preserve the arithmetic LEB128 implementation. New bitwise operations change
  the extracted operations and proof obligations.
- Use `core` and `alloc::vec::Vec`. Names are UTF-8 byte vectors with verified
  decoding; replacing them with `String` changes the extraction boundary.
- Do not use `.clone()`. Charon excludes Clone and Copy implementations;
  copy required values through the existing explicit helpers.

Current Charon reads Cargo metadata rather than the retired `Charon.toml`.
The Makefile supplies the verified flags explicitly: `cfg(charon)`, Clone/Copy
exclusions and `--sysroot=default`. Source locations appear in the generated
declarations, so source line changes can create extensive comment-only diffs.
Inspect those differences without editing generated output. Test-only edits
inside `src/` still require regeneration consistency.

## Updating visitor APIs

An opcode hook requires updates to the extracted API, `FullVisitor` and
`FullVisitorAccept` contracts, callback events/recording, and visitor transfer
proofs. A new dispatch shape also needs step/trace handling. Callback meanings
must be transcribed from hook names independently of opcode dispatch; the
concrete recorder and audit check the resulting correspondence.

A module/custom hook changes `ModuleTail.HooksTotal`, `HooksAccept`, custom
visitor transfers and `ModuleTrace.RecordsCustom`. For code hooks, also review
`ModuleCode.HooksTotal`, `ModuleCodeVisitor.Accepts`, `Validates`, `Records`,
deferred composition and `ModuleTrace.RecordsCode`. Termination and entry
correctness are separate: dispatch-only callbacks can return before workers
validate bodies. Custom callbacks after code must preserve the work observation.

New `Env` fields need exact representation/cache correspondence. Preserve
imported and defined index spaces and original byte provenance, including when
consumers use separate buffers.

## Implementation limits and consumers

Do not import SpiderMonkey-specific type/function/import/export/parameter caps.
Extra caps reject valid modules and strengthen completeness hypotheses.
`MAX_LOCALS` bounds declared locals, excluding parameters.
`MAX_FUNCTION_BYTES` bounds actual body bytes including final `end`, excluding
local declarations. Consumers enforce tighter limits while building metadata.

Error values do not carry byte positions. Adding positions throughout the
validator changes many extracted branches and proofs. Body callback traces
identify observed operators and stopping behavior; general module/entry error
traces are not currently proved. Keep this boundary clear in embedding APIs.

C ABIs must validate pointers and caller-supplied indices separately from Wasm
validation. Preserve buffer identity and offsets when dispatching workers:
separate-buffer proofs require exact concatenation of validated regions.
Consumer allocation and execution are outside these proofs.

## Streaming API

`stream::validate_streaming` is one entry point for streaming and parallel
validation, and `stream::validate_module_slice` is a synchronous adapter over
it for one contiguous buffer. Both are part of the normal extraction but have
no whole-module proof yet. `validate_module` keeps the proved implementation
until the proof lands.

### Design

Start an audit with `src/stream.rs`; its rustdoc states each contract. The
driver owns phase order and acceptance:

1. Decode the environment from `Source::environment` into caller-provided
   storage.
2. Read the code section header, then frame its entries into `CodeBatch`es of
   about `Config::batch_bytes` body bytes and submit each to the
   `StreamingVisitor`.
3. Validate the tail from `Source::tail` at EOF.
4. Retire every outstanding batch, accepting each exactly once.

The visitor schedules work and may return batches in any order, but cannot skip
a phase or certify success. A batch carries private module and batch IDs, its
environment and bytes, independent dispatch and validation cursors, and its
first error. Only `CodeBatch::validate_func` advances validation. The driver
keeps one ID per outstanding batch, bounded by `Config::max_batches`: no
per-function ledger, reference counts, or code copies. A visitor that returns a
foreign, duplicate or unfinished batch, or requests no batches, gets
`Error::Host`.

`validate_module_slice` splits the buffer by framing section headers and uses a
private `SyncVisitor` that validates each batch as it is submitted. It holds at
most one batch and never shares it, so a constant module ID suffices. The
decomposed APIs remain and serve as a differential test oracle.

### Embedding obligations

A `Source` serves the module as three regions, split at its first section
whose id is not below the code section's: the environment, the code region
(that section if it is the code section, otherwise empty), and the tail. The
embedding states the code region's length up front, and every code read is an
exact range inside it. The driver checks the split: the environment must
decode to its end, the code section header must span exactly the code region,
and the tail must hold only data and custom sections. Reads that only locate
batch boundaries are revalidated by the batch. So soundness can be stated over
the concatenated regions, and a split matching the module is only a
completeness hypothesis: a wrong split can cause a rejection but not an
acceptance. The embedding still owes:

- Every view of a region shows the same bytes, which stay unchanged while a
  batch borrows them. Rust borrows enforce this; an FFI must uphold it.
- `module_id` is unique among invocations whose batches can reach the same
  visitor.
- The environment and source outlive every worker, including after an error.
  Only `Ok` from `validate_streaming` certifies acceptance.
- FFI handles are valid, exclusively owned, and not accessed concurrently.

A worker's compiler failure also rejects the module, even if the bytes are
valid.

The Firefox adapter allocates the environment at a stable address before
calling the driver, and its `finish` callback joins and releases outstanding
jobs before that storage is freed. On success the same allocation transfers to
SpiderMonkey for tier-2 compilation. Module IDs come from a relaxed atomic
counter that rejects exhaustion instead of wrapping. Its environment, code, and
tail allocations are the `Source` regions directly.

### Proof plan

The proof has three layers: a batch invariant tying validation progress to
successful core entry validations; a scheduler contract preserving legitimately
issued batches; and driver invariants covering every function exactly once
before acceptance. A returned batch must be reachable from its own submission
through batch operations. Assuming a returned batch is already validated would
reopen the original gap. Private Rust fields do not constrain arbitrary
extracted Lean callbacks, so the contracts must be explicit.

The driver proof composes the existing environment, entry, tail and
module-region theorems, stated over the concatenated regions of a coherent
source, one whose code reads are slices of a single code region. The
contiguous theorem then discharges the source and visitor contracts for the
slice split and `SyncVisitor`, exposing no scheduler assumptions to callers.
Termination additionally needs returning callbacks; completeness needs a
coherent source split as `Source` describes, available bytes, and accepting
callbacks. Function-body and
opcode-visitor proofs are reused. Once this covers the driver, `validate_module`
can switch to it and the old whole-module orchestration can go.

### Tests

`tests/stream.rs` compares the specification corpus against the existing
validator over both a contiguous and a split source, and exercises bounded
out-of-order completion, parallel workers, foreign batches, sticky errors,
truncation, region boundaries and misplaced splits.

Firefox's `testWasmEncodeBasic` JSAPI test is not adapted yet: it calls
`ModuleGenerator` directly without an environment or framed code bytes, so
passing the Wasm jit-tests does not mean the whole JSAPI suite passes.

## Archived Rocq version

The annotated `rocq-baseline` tag preserves the pre-port revision, including
sources, dependency pins, patches and build instructions. Reproduce it in a
separate checkout using that version's DEVELOPMENT.md. The active tree retains
revision/assumption records and the explicit guarantee comparison; see
[lean/baseline/VALIDATION.md](lean/baseline/VALIDATION.md).
