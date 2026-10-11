# Development

The active pipeline is Rust → Charon → Aeneas → Lean. The proofs target
SpecTec's generated declarative typing judgments with an independent binary
grammar and explicit version-profile restrictions. Read the
[public guarantees](README.md#formal-verification),
[Lean architecture/setup](lean/README.md), and [Rocq comparison](lean/PARITY.md).

## Layout

| Path | Purpose |
| --- | --- |
| `src/module.rs` | Shared environment, entry and tail validation, custom visitor, and whole-module wrapper. |
| `src/code.rs` | Streaming body validator and opcode dispatch. |
| `src/stream.rs` | Sole module driver, batches, source protocol, and private synchronous slice adapter. |
| `src/reader.rs`, `types.rs`, `limits.rs`, `error.rs` | Byte readers, API types, implementation bounds and errors. |
| `lean/Itasca/Generated/Types.lean`, `Funs.lean` | Committed Aeneas extraction; never edit by hand. |
| `lean/Itasca/Generated/FunsExternal.lean` | Handwritten concrete models of `Vec.pop` and `Vec.is_empty`. |
| `lean/Itasca/Binary/` | Independent grammars, byte readers, and structured-body/module decoding uniqueness. |
| `lean/Itasca/Body/`, `Visitor/` | Body typing, completeness, shared dispatch, and callback proofs. |
| `lean/Itasca/Profile/` | Shared profile predicates, body/entry certificates, and implementation adapters. |
| `lean/Itasca/MultiValue/` | Multi-value signature/control semantics, grammar, body proofs, and visitor adapters. |
| `lean/Itasca/Module/` | Shared parsing/typing, independent module certificates, metadata, and whole-module corollaries. |
| `lean/Itasca/Stream/` | Source contracts, actual worker/driver proofs, and concrete adapter proofs. |
| `lean/Itasca/Examples/`, `Support/` | Checked regression examples and common proof helpers. |
| `lean/Itasca/*.lean` | Stable public entry modules, specification checks, and the transitive audit of all local declarations. |
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
just check Itasca.Module.ModuleValidation # One module and dependencies
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

A module/custom hook changes `ModuleTail.HooksTotal`, `HooksAccept`, visitor
transfers, and preservation of scheduler invariants. A streaming callback changes
`StreamScheduler.CallbacksTotal`, `Provenance`, and
`StreamAcceptingScheduler.Accepts`, together with its concrete adapter proofs.
Termination, provenance, and acceptance are separate obligations: a submitted
batch may remain outstanding while tail or custom callbacks run. Every callback
must preserve the scheduler relation used by the soundness theorem. Keep actual
`next_entry`/`validate_func` histories as the basis of worker provenance; do not
replace them with assumed validation counters or successful finish checks.

New `Env` fields need exact representation/cache correspondence. Preserve
imported and defined index spaces and original byte provenance, including when
consumers use separate buffers.

## Implementation limits and consumers

Implementation limits follow SpiderMonkey and the JavaScript embedding where
appropriate. Every cap must be checked before allocation when the encoded count
is available, and must appear in completeness hypotheses. The experimental
multi-value profile permits up to 1000 parameters and 1000 results per signature;
Wasm 1.0 retains its existing single-result restriction and parameter behavior.
Do not silently tighten Wasm 1.0 acceptance while adding the new profile.

`MAX_LOCALS` bounds declared locals, excluding parameters.
`MAX_FUNCTION_BYTES` bounds actual body bytes including final `end`, excluding
local declarations. Consumers enforce tighter limits while building metadata.

`cargo run --release --example multi_value_bench` compares repeated empty and
single-result blocks across the two profiles, then measures 2-, 16-, and
1000-result blocks. Encoding is outside the measured region. This is a control
signature microbenchmark, not a whole-application performance claim.

Error values do not carry byte positions. Adding positions throughout the
validator changes many extracted branches and proofs. Body callback traces
identify observed operators and stopping behavior; general module/entry error
traces are not currently proved. Keep this boundary clear in embedding APIs.

C ABIs must validate pointers and caller-supplied indices separately from Wasm
validation. Preserve buffer identity and offsets when dispatching workers:
separate-buffer proofs require exact concatenation of validated regions.
Consumer allocation and execution are outside these proofs.

## Streaming API

`stream::validate_streaming` is the sole module orchestrator for both profiles.
The caller supplies an explicit `ValidationProfile`, which is threaded through
the shared environment parser, code entries, tail parser, and immutable issued
batches. `validate_module(bytes, profile)` supplies a private contiguous slice
adapter and synchronous worker. `validate_module_with_profile` is an alias to
that same entry point. `multi_value.rs` contains the shared profile-parameterized
body loop and signature/control helpers; it has no separate module driver.
Both historical body entry points delegate to that loop. Initialization and
control dispatch select the profile; scalar operators use the existing shared
dispatcher.

Both profiles use the existing visitor callbacks. Control hooks expose
`signature::BlockType`, and branch hooks expose `signature::ResultType`.
`OpIterState.ctrls` stores each frame's height, kind, and full signature for
both profiles. Multi-value state has no parallel signature vector. Keep the
profile-specific control behavior, including branch-table callback order and
the function-end stack, explicit when refactoring handlers. The generic driver and
adapter have shared soundness, totality, and independent completeness proofs
for either selected profile. The public theorem families use `profile_*` names;
existing `wasm_*` names specialize them to Wasm 1.0.

### Extending profiles

Keep feature-specific semantics behind the contracts in `Itasca/Profile/`.
`FuncType` and `Instructions` express language restrictions;
`FuncTypeWithinLimits` and `EnvironmentWithinLimits` express allocation caps.
`Body` and `Entry` connect exact independent bytes to generated declarative
typing using the actual selected type index. Their execution adapters supply
totality, acceptance soundness, and completeness with accepting visitor hooks.
Shared entry framing, module assembly, and streaming proofs consume these
contracts without a second module proof tree.

A feature can change binary grammar outside function bodies. The current
multi-value profile uses Core 2 active-segment flags 0 and 2, including the
explicit element-kind byte; Wasm 1.0 keeps its original segment indices.
`ElementEncodingFor`, `DataEncodingFor`, and `ModuleEncodingWith` select this
grammar with the same profile as the parser. New sections, index spaces, or
initializer rules also require updating their independent grammar and shared
environment/assembly invariants. Do not assume a body adapter alone proves a
new module feature.

Extend these contracts and their implementation adapters as features arrive,
then reuse the module/streaming composition. Preserve old profile behavior and
keep resource limits as separate completeness hypotheses:
`ModuleEncodingWithinLimits` bounds bytes and declared locals, while
`ModuleSignaturesWithinLimits` bounds signatures. Add regressions for the new
feature and for behavior that must remain different between profiles. Future
Wasm 3.0 work also requires reviewing the pinned generated specification and
its source patches; selecting a new runtime profile does not establish
correspondence with a newer specification.

### Design

Start an audit with `src/stream.rs`; its rustdoc states each contract. The
driver owns phase order and acceptance:

1. Decode the environment from `Source::environment` into caller-provided
   storage.
2. Read the code section header, then frame its entries into `CodeBatch`es of
   about `Config::batch_bytes` entry-content bytes (including locals) and submit each to the
   `StreamingVisitor`.
3. Validate the tail from `Source::tail` at EOF.
4. Retire every outstanding batch, accepting each exactly once.

The visitor schedules work and may return batches in any order, but cannot skip
a phase or certify success. A batch carries private module and batch IDs, its selected profile,
environment and bytes, independent dispatch and validation cursors, and its
first error. Only `CodeBatch::validate_func` advances validation. The driver
keeps one ID per outstanding batch, bounded by `Config::max_batches`: no
per-function ledger, reference counts, or code copies. A visitor that returns a
foreign, duplicate or unfinished batch, or requests no batches, gets
`Error::Host`.

The private slice adapter splits the buffer by framing section headers and
uses `SyncVisitor` to validate each batch as it is submitted. It holds at most
one batch and never shares it, so a constant module ID suffices. Environment,
entry, body, and tail functions remain shared components. Running one component
alone does not establish whole-module validity or advance a batch validation
cursor.

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
  batch borrows them. Rust borrows protect an individual view from mutation;
  they do not force separate `Source::code` calls to return slices of the same
  logical region. Source coherence is an explicit embedding obligation, even
  for a safe Rust implementation. An FFI must also uphold the borrow rules.
- `module_id` is unique among invocations whose batches can reach the same
  visitor.
- The environment and source outlive every worker, including after an error.
  Only `Ok` from `validate_streaming` certifies acceptance.
- FFI handles are valid, exclusively owned, and not accessed concurrently.

A worker's compiler failure also rejects the module, even if the bytes are
valid.

An external engine adapter must arrange stable environment storage, join or
cancel workers before releasing their borrows, and avoid reusing module IDs
while old batches can reach its scheduler. The experimental Firefox integration
is maintained separately; this repository's API migration does not update or
verify that external checkout.

### Proof contracts and API migration

The [streaming proof plan](STREAMING_PROOF_PLAN.md) records the implementation
sequence and verification gates. The proof hierarchy now composes shared
semantic certificates directly; streaming correctness does not replay the
removed module/code-section driver.

| Contract | Obligation |
| --- | --- |
| `StreamSource.Coherent` | Successful views and code length agree with fixed logical environment/code/tail bytes; bounded code views are exact slices. Soundness allows read errors and does not require a canonical split. |
| `StreamSource.CallbacksTotal` and `StreamScheduler.CallbacksTotal` | Source and visitor calls return ordinary modeled results. Submit totality is required for legitimate bounded seeds. Polls may return malformed or unfinished workers. |
| `StreamScheduler.Provenance` | Every historical matching worker is reachable from its issued seed through actual batch operations, and every callback preserves that relation. Successful finish and pending membership are checked by the driver. |
| `StreamSource.CanonicalAvailable` | The canonical split of independent input bytes is available to all needed source reads; this is a completeness premise. |
| `StreamAcceptingScheduler.Accepts` | Callbacks accept and preserve the queue, positive configuration bounds outstanding work, and polls return queued results of actual `validate_all` executions in any order. Independent typed byte encodings imply those workers finish successfully. |

The concrete `SliceSource` and private `SyncVisitor` discharge these obligations
for `validate_module`. Its completeness premises remain independent module
encoding and signature bounds, elaboration, generated typing, and the selected
profile. The current `MultiValue` profile does not claim full Wasm 2.0 support.
No parser-success or prevalidated-body assumptions were added, and the trust
base is unchanged.

Removed public APIs are `validate_module_with`, `validate_code_with`,
`validate_code`, `CodeVisitor`, `ValidatingCodeVisitor`, and
`code_section`/`CodeSection`; the internal legacy code-entry walk is gone too.
Callers use `StreamingVisitor` or the synchronous `validate_module` wrapper.
`ModuleVisitor` remains the custom-section hook and `OpVisitor` remains the
entry/body hook. Old deferred-code and whole-module callback-trace contracts
were retired with the old APIs. Preserve the retained body/entry trace theorems
when changing their shared implementation; old module callback order and byte
requests are not compatibility requirements of the streaming API.

### Tests

`tests/stream.rs` checks contiguous and split sources against specification corpus
expectations, and exercises bounded out-of-order completion, parallel workers,
foreign and unfinished batches, repeated validation, sticky errors, truncation,
and region boundaries. The kernel-checked `StreamExamples.replay_rejected`
regression covers rejection of a batch whose ID is no longer pending. `validate_module` and its slice adapter share a driver, so agreement
between them is not independent differential coverage. The wasmparser fuzz
oracle remains independent.

External Firefox tests and API migration are outside this repository's proof
and test results. In particular, passing a subset of engine tests does not
certify an external adapter's lifetime, scheduling, or FFI obligations.

## Archived Rocq version

The annotated `rocq-baseline` tag preserves the pre-port revision, including
sources, dependency pins, patches and build instructions. Reproduce it in a
separate checkout using that version's DEVELOPMENT.md. The active tree retains
revision/assumption records and the explicit guarantee comparison; see
[lean/baseline/VALIDATION.md](lean/baseline/VALIDATION.md).
