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

## Experimental streaming API

The opt-in `stream` Cargo feature adds
`stream::validate(module_id, source, host, env)`. With this feature,
`validate_module` is a synchronous adapter for that same driver. Both paths are
extracted and checked separately, but have no whole-module correctness proof
yet. Builds without the feature and the normal extraction/proof targets retain
the existing implementation until its proof is migrated.

Start an audit with `src/stream.rs`: `validate` decodes the environment into
caller-provided storage and directly calls `validate_remaining`. The latter
checks code framing, dispatches bounded batches, validates the tail at EOF, and
consumes all pending completions. The host cannot replace these phases or supply
a module-success certificate. The implementation reuses the core LEB reader and
module validators.

- `Source` exposes a prefix containing the environment, reads at absolute module
  offsets, and a suffix available at EOF. The prefix may contain more than the
  environment: `SliceSource` simply supplies the entire module. The driver
  discovers the code boundaries itself. Reads publish initialized immutable
  bytes, overlapping views must agree, and every requested batch is contiguous.
  Header reads may stop at EOF or an allocation boundary; body reads must return
  their exact requested range. The suffix contains every remaining byte.
- `env` is output storage for the decoded environment, not a prevalidated input.
  Batches borrow it and the source bytes with ordinary Rust lifetimes. Callers
  keep that storage alive until their workers finish, including after errors.
  Only a successful return from `validate` certifies module acceptance.
- `Host` receives owned batches and returns completed batches in any order. Each
  batch holds private module/batch IDs, its environment and byte range, dispatch
  and validation cursors, and the first actual `Error`. `Batch::validate_func`
  alone advances validation. The driver registers a batch before submission,
  checks both IDs on completion, and consumes each outstanding ID exactly once.
  Outstanding IDs are bounded by `Config::max_batches`, with no per-function
  ledger, reference counts, or code copies in the driver.
- `module_id` must be unique among invocations whose batches can reach the same
  host. The Firefox FFI generates it with one relaxed atomic allocation per
  invocation and rejects exhaustion instead of wrapping. This allocation is
  outside extraction; identity uniqueness is an explicit embedding obligation.
- `Visitor` selects the region and its absolute base for custom-section offsets.
  Environment and tail callbacks translate metadata for the embedding; worker
  opcode visitors drive compilation as before. A compiler failure also rejects
  the module, even if its validation would otherwise succeed.

The Firefox adapter allocates stable environment storage before calling the
Rust driver. Its `finish` callback joins and releases remaining jobs before that
storage can be freed, including on errors. On success, ownership of the same
allocation transfers to SM for retained tier-2 compilation. The callback performs
cleanup; it cannot make validation succeed. Batch handles transfer exclusive
ownership on submission and completion. Returning a live foreign-module batch
is rejected, but invalid/freed pointers and concurrent handle access remain FFI
contract violations.

Firefox's source translates absolute requests into its environment, code, and
tail allocations. The physical code length bounds readable storage; it does not
replace the driver's parsing of the section header. The adapter checks that the
discovered code range agrees with that allocation. Without code, the entire
module resides in the environment allocation, including any data/custom tail.

For contiguous validation, `SliceSource` borrows the original bytes and a private
`InlineHost` validates each submitted batch immediately using `validate_func`.
It retains at most one completed batch. No worker threads, module-ID allocator,
or code copies are needed. This host never exchanges tokens with another
invocation, so its constant ID is sufficient. The old visiting/decomposed APIs
remain available during migration and provide a differential test oracle.
The driver's explicit `'data: 'host` bound states that storage outlives the
mutable host borrow. Aeneas needs this relation in the generic signature to
return updated host/environment state in the same order at concrete calls whose
host stores borrowed batches. `extract-stream` compiles that concrete adapter as
well as the generic driver, so it checks this boundary too.

The intended proof has three layers: a batch invariant tying validation progress
to successful core entry validations; a scheduler contract preserving legitimately
issued batches through those operations; and driver invariants covering every
function exactly once before acceptance. Private Rust fields do not by themselves
restrict arbitrary extracted Lean callbacks. Byte coherence, unique module IDs,
and faithful FFI ownership/publication must be justified at the embedding
boundary. Extraction alone establishes none of these correctness claims.

The proof migration should establish source coherence and batch reachability
once for the shared driver, composing the existing environment, entry, tail,
and module-region theorems. A completed batch must be reachable from its actual
submission through batch API operations; assuming that a returned batch has
already validated everything would leave the original gap. The contiguous
theorem then discharges the source and host contracts for `SliceSource` and
`InlineHost`, with no scheduler assumptions exposed to its callers. Termination
additionally needs returning source/host callbacks; completeness needs available
bytes and accepting callbacks. Once these proofs cover the shared path, remove
the feature switch and old whole-module orchestration. Function-body proofs and
their opcode-visitor guarantees are reused, not duplicated.

```sh
cargo test --features stream
cargo test --no-default-features --features stream
just extract-stream
```

`extract-stream` translates the actual feature and its core dependencies, checks
that only the two existing concrete `Vec` models are required, and compiles the
generated Lean. Output goes to a temporary directory outside the proof sources.
`python3 lean/scripts/check_stream.py --output /tmp/itasca-stream` keeps it at a
chosen location for inspection. No generated proof input is replaced and no
external template is imported. Tests compare the full specification corpus and
exercise bounded out-of-order work, parallel workers, foreign-module completion,
sticky errors, truncation, and region boundaries.

The Firefox `testWasmEncodeBasic` embedding test is not yet adapted: it builds
metadata and calls `ModuleGenerator` directly without supplying an Itasca
environment or framed code bytes. It reaches the standalone entry API with a
null environment, bypassing this driver entirely. This limitation predates the
shared-driver changes; passing the Wasm jit-test suite or the seven Wasm ABI
helper tests does not establish that the entire JSAPI suite passes.

## Archived Rocq version

The annotated `rocq-baseline` tag preserves the pre-port revision, including
sources, dependency pins, patches and build instructions. Reproduce it in a
separate checkout using that version's DEVELOPMENT.md. The active tree retains
revision/assumption records and the explicit guarantee comparison; see
[lean/baseline/VALIDATION.md](lean/baseline/VALIDATION.md).
