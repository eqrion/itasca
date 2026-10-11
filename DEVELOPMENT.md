# Development

itasca uses one pipeline: Rust → Charon → Aeneas → Lean. Read the
[public guarantees and trust boundary](README.md#formal-verification) before
changing validation behavior, and follow the [Lean setup](lean/README.md#setup)
to install the pinned tools.

## Source layout

| Path | Responsibility |
| --- | --- |
| `src/lib.rs` | Explicit consumer exports and profile selection. |
| `src/stream.rs` | Module orchestration, source/scheduler contracts, issued batches, and the private contiguous adapter. |
| `src/module.rs` | Read-only module metadata and internal environment, entry, and tail validation. |
| `src/code.rs` | Shared body execution, both profiles' control handlers, scalar instructions, operator callbacks, and opcode tables. |
| `src/signature.rs` | Allocation-free block and result descriptors. |
| `src/types.rs`, `error.rs` | Shared metadata and error vocabulary. |
| `src/reader.rs`, `limits.rs` | Byte readers, specification bounds, and resource caps. |
| `lean/Itasca/` | Extracted models, proof layers, checked examples, and axiom audit. |
| `lean/SpecTec/` | Committed generated specification. |
| `lean/scripts/` | Audit-import and concrete external-model checks, with their shared Lean tokenizer. |
| `vendor/`, `patches/` | Pinned tool/specification sources and reproducible source repairs. |
| `tests/spec_tests.rs`, `tests/spec2_tests.rs` | End-to-end specification corpus and metadata checks. |
| `tests/support/`, `examples/wast_extract.rs` | Fixture normalization and generation. |
| `fuzz/` | Differential fuzzers against wasmparser. |

The internal Rust modules follow the implementation and proof boundaries. Keep
those boundaries unless a change improves the implementation enough to justify
renaming extracted declarations and their proof references. Only explicit crate
root exports form the public API; `stream` remains an internal implementation
module. Raw component validators remain internal proof entry points; their local
`dead_code` annotations preserve those proof checkpoints without exposing APIs
with extensive caller preconditions.

## Build and verification

Choose commands for the files you changed; this is a command reference, not a
sequence to repeat after every edit.

```sh
cargo test
cargo test --no-default-features
just extract          # Refresh committed Rust models after source changes
just extract-check    # Regenerate separately and compare
just check Itasca.Module.ModuleValidation
just profile Itasca.MultiValue.ScalarContext  # Re-elaborate one module with timings
just prove            # Build all proofs and check audit coverage and axioms
just trust            # Rerun the transitive axiom report
just spec-check       # Regenerate and compare the specification
just regressions      # Run patched Aeneas extraction regressions
just verify           # Run the complete verification sequence
```

| Change | Required checks |
| --- | --- |
| Handwritten Lean proofs or adapters | `just prove` |
| Rust or extraction inputs, including source documentation | Both Cargo test configurations, `just extract`, `just extract-check`, and `just prove` |
| Aeneas source patch or pin | Rust/extraction checks plus `just regressions` |
| SpecTec source, patch, or pin | `just spec-update`, `just spec-check`, and `just prove` |
| Documentation outside extraction inputs | Check links and `git diff --check` |

Generated source locations change when Rust lines move. Inspect generated diffs;
never repair `Types.lean` or `Funs.lean` by hand. `FunsExternal.lean` is handwritten,
and the generated external template is ignored and must never be imported.
Specification changes belong in source or generator patches, followed by
regeneration. Consistency checks write to ignored build directories and fail on
stale committed output.

Use `just check Itasca.ModuleName` while iterating. Preserve `lean/.lake/` and
`lean/.build/`; `just clean` removes only this project's compiled Lean artifacts.
Scratch files belong in `$TMPDIR`, outside the proof tree. Use the committed Lake
manifest during ordinary builds; `lake update` is for intentional dependency
changes. `lean-extract` and `lean-prove` remain command aliases.

`just check` accepts multiple module names in one Lake invocation. It rebuilds
changed dependencies and reuses the rest. `just profile Itasca.ModuleName` builds
the imports, then re-elaborates that module with Lean's profiler; it is a
diagnostic command, not an additional verification requirement. Compare timings
with warm dependencies and without another build competing for resources.

For a proof-only change, use targeted checks until the proof works, then run
`just prove` once for integration. Extraction, specification regeneration, and
toolchain regressions are required when their inputs change, as listed above;
they add no new evidence about an edit confined to handwritten proofs.
`just prove` already checks transitive axioms, so `just trust` is optional unless
you want the per-declaration report. Ordinary builds print the audit summary.
`just verify` retains every full-pipeline check and uses its final integrated
build to compile the compared specification and `Itasca.SpecChecks`.

## Rust extraction constraints

The implementation stays within the verified extraction subset:

- Use safe Rust, `core`, and `alloc::vec::Vec`.
- Pass byte slices and cursors explicitly. Check extraction and proof effects
  before adding stored borrows or new indexing patterns.
- Use explicit counters instead of iterators, closures, labeled control flow,
  or returns from nested loops.
- Preserve arithmetic LEB decoding. Bitwise operations change the extracted
  primitives and their proof obligations.
- Store names as checked UTF-8 bytes. Introducing `String` changes the model.
- Use explicit copy helpers instead of `.clone()`. Extraction excludes Clone
  and Copy implementations.

Rust enums already represent profiles, value types, control kinds, signatures,
imports, exports, and errors. The current Lean backend also handles fieldless
enums with explicit discriminants, decoding matches, and casts. Remaining
opcode/section constants represent wire bytes; resource constants represent
bounds. Keep raw-byte dispatch where it avoids a second decoding layer. Enum
changes should improve the representation, not merely rename byte constants.

Charon reads Cargo metadata; the Makefile supplies `cfg(charon)`, Clone/Copy
exclusions, and `--sysroot=default` explicitly. Debug and convenience derives
are disabled during extraction when their implementations are outside the model.

## API and documentation

Consumers validate complete modules or operate on batches issued by the driver.
Keep validation state private and expose shared metadata views. A consumer must
not be able to alter a validated environment or construct an accepted `Module`.
Streaming metadata is provisional until the driver succeeds.

Use one documentation style throughout the crate: start with a short sentence
stating what an item represents or does, then describe meaningful inputs,
results, coordinate systems, error behavior, and caller obligations. Keep
proof limitations precise. Implementation rationale belongs beside the code;
public docs should describe the consumer's contract.

The four guides have separate responsibilities: `README.md` describes usage and
public guarantees; this guide describes changes and integration;
`lean/README.md` describes tool setup and proof contracts; `AGENTS.md` records
mandatory editing and verification rules. Historical migration records are not
sources of current API or toolchain requirements.

## Streaming contract

The driver owns phase order and acceptance. It decodes the environment, frames
and submits code batches, validates the tail, and drains all outstanding work.
Each batch fixes its profile, environment, bytes, and module/batch identity.
Dispatch and validation have independent cursors; a framed entry is not yet
validated. The first validation error remains stored. Only successful
`validate_func` calls advance validation, and the driver checks the returned
batch's pending identity and successful finish.

A source exposes environment, code, and tail regions. The canonical split is
at the first section with ID at least 10: the code region is that section when
it is code, otherwise empty. The environment precedes it and the tail follows
it. No such section means the complete input is environment. Successful views
must agree with fixed logical bytes, including overlapping code reads. The
driver checks framing; an incorrect split may reject otherwise valid input.

The embedding must ensure:

- Invocation IDs are unique among batches that can reach the same scheduler.
- Returned workers derive from their issued batches through actual batch
  operations. They may complete in any order.
- Source and environment storage outlive every worker, including on error.
- Callbacks return normally for termination. Accepting callbacks and available
  canonical regions are additionally needed for completeness.
- Any FFI handles, pointers, and concurrent accesses satisfy their own safety
  and ownership rules.

`CodeEntry` offsets refer to the complete code region. Function-start bounds
refer to `CodeBatch::code`; `OpIterState::pos` is relative to the instruction body
starting at that callback's `body_begin`. Custom-section bounds refer to the
region selected by `custom_region`. Preserve these coordinate systems in
compiler metadata and separate-buffer adapters.

A compiler callback failure rejects the module even if its bytes are valid.
Successful validation does not prove the consumer's IR, compilation, scheduling,
or FFI implementation correct. External engine integrations are maintained and
validated separately.

## Extending validation and proofs

An opcode hook affects the extracted trait, total/accepting visitor contracts,
callback events and recording, and dispatch/trace proofs. Transcribe callback
meaning independently of dispatch so correspondence checks can detect wrong
mappings. Module and streaming callbacks also affect scheduler invariants;
every callback must preserve the relation between issued and returned workers.

Keep language restrictions and implementation limits separate in
`Itasca/Profile/`. Shared body and entry certificates connect independent bytes
to generated typing; module and streaming proofs compose those certificates.
Changes to sections, index spaces, initializers, or segment encodings also need
independent module-grammar and elaboration updates. A new body feature alone
does not establish a new module profile.

Check encoded counts before allocation where available. `MAX_LOCALS` excludes
parameters; `MAX_FUNCTION_BYTES` includes the final `end` and excludes local
declarations. Multi-value signatures have at most 1000 parameters and results.
Do not tighten Wasm 1.0's parameter behavior as a side effect of another profile.

Every new proof module must be reachable from `Itasca.Audit`. The audit checks
all local declarations and rejects axioms beyond the three documented logical
foundations. New proof-bearing adapters receive the same scrutiny as exported
theorems. Report changes to the trust boundary explicitly.
