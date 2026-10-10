# Lean verification

This is itasca's active verification pipeline, implementing the
[Lean port plan](../LEAN_PORT.md). The Rocq version is archived under
`rocq-baseline`. See the [guarantee comparison](PARITY.md),
[final validation record](baseline/VALIDATION.md), and
[upstream change tracker](../UPSTREAM.md).

The whole-module claims below cover builds without the experimental `stream`
feature. With that feature, `validate_module` uses the shared streaming driver,
which is extracted separately but not yet proved. See the
[shared-driver migration](../DEVELOPMENT.md#experimental-streaming-api).

The full Rust extraction and freshly regenerated SpecTec definitions compile
together. Local source patches fix Aeneas naming and indentation bugs and work
around SpecTec's loss of optional mutability and ambiguous import projections,
and correct its four-byte UTF-8 upper bound. Tool builds and regeneration apply
the patches automatically; see [upstream/](upstream/README.md) for their scope
and regressions.

The full Wasm 1.0 function-body proof is checked in
[`Itasca/WasmSoundness.lean`](Itasca/WasmSoundness.lean) and
[`Itasca/VisitorBodyErasure.lean`](Itasca/VisitorBodyErasure.lean), with completeness
in [`Itasca/WasmComplete.lean`](Itasca/WasmComplete.lean) and
[`Itasca/VisitorBodyComplete.lean`](Itasca/VisitorBodyComplete.lean), and visitor traces
in [`Itasca/VisitorBodyTrace.lean`](Itasca/VisitorBodyTrace.lean). It covers the
**actual extracted public `validate_body` and `validate_body_with` functions**,
including their size guard, initialization, streaming loop, final `end`,
trailing-byte check, and visitor dispatch.

The proof covers all Wasm 1.0 instruction families: scalar constants and the
123 numeric opcodes, select/drop, structured control, branches and branch
tables, locals/globals, direct/indirect calls, and memory operations. Block and
function results retain the implementation's zero-or-one-result restriction.
Nested blocks, result-carrying branches, and mixed concrete/polymorphic operand
stacks are included.

| Theorem | Checked claim |
| --- | --- |
| `code.validate_body.wasm_total` | Every byte sequence and caller-supplied environment/context returns an ordinary success/error result without modeled panic or divergence. |
| `code.validate_body.wasm_sound` | Acceptance implies exact Wasm 1.0 binary provenance and a generated SpecTec `Instrs_ok` body typing derivation. |
| `code.validate_body.wasm1_sound` / `code.validate_body_with.wasm1_sound` | Acceptance also establishes the independent recursive Wasm 1.0 profile for the same instruction tree, including identical branch-table target signatures. |
| `code.validate_body.wasm_complete` | Independent byte encoding, generated declarative typing, and the explicit Wasm 1.0 profile imply acceptance within the existing API limits. |
| `code.validate_body.wasm_complete_of_typing` | The same completeness result with the encoded instruction tree and its typing/profile premises supplied explicitly. |
| `code.validate_body_with.wasm_total` | The visiting API terminates when its hooks terminate; hooks may reject and change visitor state. |
| `code.validate_body_with.wasm_sound` | Acceptance has the same soundness guarantee for an arbitrary visitor, with no hook-termination premise. |
| `code.validate_body_with.wasm_complete` | The same body completeness guarantee for a visitor whose hooks always terminate and accept. |
| `code.validate_body_with.accepted_lift` | Any body accepted by the non-visiting API is accepted with such a visitor, for arbitrary environments and result vectors. |
| `code.validate_body_with.trace` | Every ordinary returned execution of a recording visitor has independently encoded callback provenance, including a partial final branch table on error. |
| `code.validate_body_with.trace_sound` | An accepted recording visitor reports exactly the tokens of the same independently encoded, SpecTec-typed body as the soundness theorem. |
| `code.validate_body_with.trace_complete` | Independent Wasm 1.0 encoding and typing force acceptance and a complete trace for an accepting recording visitor. |
| `code.validate_body_with.trace_rejection_last` / `trace_no_function_start` | An observed rejecting callback is last and matches the result; body traces contain no function-start event. |
| `code.validate_body_with.recorder_projection_sound` / `recorder_projection_complete` | Projecting the concrete log reconstructs a complete independently encoded, typed body with no pending table labels. |
| `code.validate_body_with.instrument_iff` / `instrument_trace` | Wrapping any visitor with a recorder preserves its ordinary result and final underlying state in both directions, and certifies the added trace. |
| `code.validate_body_with.recorder_total` / `recorder_complete` | The concrete recorder terminates on arbitrary bytes and produces a complete typed trace on independently valid Wasm 1.0 bodies. |
| `code.validate_body.wasm_spec` / `code.validate_body_with.wasm_spec` | Combined termination and acceptance contracts; the visiting contract requires terminating hooks. |

There is **no `Core.Profile` or valid-immediate premise** on termination or
acceptance soundness. Completeness starts from an independently encoded, typed body.
Malformed/truncated LEBs and floating-point payloads, invalid block types,
unknown opcodes/indices/labels, bad reserved bytes, operand mismatches, unbalanced
control, and trailing bytes are covered by the actual validator's error paths.
Oversized bodies return `BodyTooLarge`. The size guard also supplies the stack
capacity bounds used by the Aeneas vector model.

Soundness requires the declared function results to match a Wasm 1.0 block
type (zero or one value). Termination has no such premise: initialization is
modeled exactly even for an arbitrary caller-supplied result vector. Inputs are
raw instruction bodies, with local declarations already removed, as required
by the Rust body API.

`Wasm.Validated` states a handwritten binary-encoding relation and generated
SpecTec declarative body typing. The binary relation is independent of validator
execution because the pinned SpecTec Lean output has no generated binary-format
judgment. No executable specification checker or abstract step-preservation
assumption is required by the public theorems.

`EnvTranslation.context` uses the actual stored type tables: `env.types` for
indirect calls, cached `env.func_types` for direct calls, and the global/table/
memory types and function locals/results. The body theorem does not certify
module parsing or that cached function signatures agree with a module's type
indices. Those obligations belong to module verification.

Completeness requires `Wasm1.Environment env` (zero or one result in every
stored direct-call and indirect-call signature), the API's zero-or-one function
result shape, and `data.length ≤ MAX_FUNCTION_BYTES`. `Wasm1.Body` combines the
same independent binary relation and generated typing with a recursive
branch-table target-equality condition. These premises do not mention validator
execution, a local checker, or assumed step success. Visiting completeness adds
`FullVisitor.Accepts visitor`: each of the 174 hooks returns an ordinary `Ok`,
with an arbitrary updated visitor state. Merely terminating hooks may reject,
so `FullVisitor.Total` alone cannot imply acceptance. Forward acceptance transfer
and the existing erasure theorem give both directions when hooks always accept;
the trace theorems additionally identify the callbacks and their arguments.

The target-equality condition matters: Wasm 2.0 accepts some differently typed
branch-table targets in unreachable code through a common `BOT` subtype;
Wasm 1.0 requires identical signatures. Merely restricting the bytes to 1.0
opcodes does not remove that difference. The kernel-checked
[`WasmCompletenessBoundary`](Itasca/WasmCompletenessBoundary.lean) example proves
generated 2.0 typing and actual `TypeMismatch` rejection for the same 11 bytes.
The profile preserves existing Wasm 1.0 behavior without changing Rust or the
upstream specification.

Whole-module soundness and arbitrary-byte termination now cover the actual
public API in [`ModuleValidation`](Itasca/ModuleValidation.lean):

| Theorem | Checked claim |
| --- | --- |
| `module.validate_module.wasm_spec` | Every input returns an ordinary result; successful results satisfy the complete module certificate. |
| `module.validate_module.wasm_total` | No input bytes cause modeled panic or divergence. |
| `module.validate_module.wasm_sound` | Acceptance establishes `ModuleSound.Validated` without abstract parser, environment, or body-validation assumptions. |

`ModuleSound.Validated` supplies one raw module whose independent
`ModuleBinary.ModuleEncoding` accounts for the whole input. `Elaborates`
connects that same module to generated SpecTec syntax, excluding out-of-range
function-type fallback and truncated function/code pairing. The generated
`Module_ok` derivation uses imported and defined index spaces in their actual
order. `Profile` additionally establishes unique decoded export names,
Wasm 1.0 table/memory/result limits, and the recursive body profile.

The certificate also identifies the returned environment and data segments,
proves cache coherence, and proves that the actual `import_types` and
`export_types` functions succeed and report the same module's types in order.
Names retain strict Unicode scalar encoding, including four-byte scalars.
Initializers see only immutable imported globals; bodies see the full global
space. Element/data segments and start functions are covered. There is no
executable-specification-checker premise.

Whole-module completeness is checked in
[`ModuleCompleteness`](Itasca/ModuleCompleteness.lean).
`module.validate_module.wasm_complete` starts from the same independent raw
module, generated `Module_ok`, `Elaborates`, `Profile`, and
`ModuleEncodingWithinLimits`. It proves actual public acceptance and exact
correspondence with returned declarations/data. The metadata variant also
proves success and correspondence of the public import/export type accessors.
No parser-success, decoded-cache, or prevalidated-entry premise is exposed.
The limits constrain the actual module bytes, the encoded instruction body
including its final `end`, and declared locals excluding parameters.

`ModuleCodeEntry`, `ModuleCode`, `ModuleEnvSemantics`, and `ModuleTail` expose
the component contracts used in this composition. `ModuleRegions` proves the
complete module certificate for both adjacent calls on one buffer and exact
concatenations of independently validated environment/code/tail buffers.
`ModuleDecomposed` derives per-entry bounds and arity from an actual accepted
environment decode, including when the entry bytes are in another buffer.
`ModuleEntryVisitor`, `ModuleCustomVisitor`, and `ModuleVisitorTransfer`
preserve acceptance under callback replacement. Accepted custom/opcode
visitors need no termination premise for erasure; overriding a code-entry
callback requires its own validation guarantee. Accepting callbacks preserve
module completeness. `ModuleCodeTotal` and `ModuleVisitorValidation` prove
termination separately, even for callbacks that defer entry validation.
`ModuleDeferredValidation` composes the recorded worker obligations with both
same-buffer and separate-buffer modules. For a whole-module visitor's final
state, custom callbacks must preserve the work observation; this prevents the
tail from erasing an unvalidated entry. `ModuleEntryOrder` proves exactly one
recorded obligation per defined function, in index order. The concrete recorder
only dispatches work; its successful return alone does not certify a body.

| Consumer interface | Main theorem |
| --- | --- |
| Separate entry after decoding the environment | `module.validate_code_entry.spec_of_env` |
| Accepted entry with original callback trace | `module.validate_code_entry_with.trace_sound` |
| Accepted validating whole-module visitor | `module.validate_module_with.wasm_sound` |
| Accepted whole-module callback trace | `module.validate_module_with.trace` / `trace_sound` |
| Whole-module trace after deferred workers finish | `module.validate_module_with.deferred_trace_sound` |
| Independently valid module with accepting recording callbacks | `module.validate_module_with.trace_complete` |
| Concrete validating recorder for any accepted module | `module.validate_module.recorded` |
| Whole-module callback termination | `module.validate_module_with.total_with_hooks` |
| Deferred code walk after workers finish | `module.validate_code_with.deferred_erase` |
| Deferred whole-module visitor with preserved final work list | `module.validate_module_with.deferred_wasm_sound` |
| Separate buffers with deferred workers | `module.validate_module.regions_deferred_wasm_sound` |

Entry traces cover accepted entries and include the function-start event and
exact body operators, with the body start tied to that entry's encoded locals.
[`ModuleTraceValidation`](Itasca/ModuleTraceValidation.lean) certifies accepted
whole-module callbacks against independent section framing: custom-section
metadata, byte-readiness requests, and each code-entry handoff with its index
and offsets. [`ModuleCustomRanges`](Itasca/ModuleCustomRanges.lean) identifies
the exact UTF-8 name bytes before `payload_start` and bounds both name and
payload intervals in the original buffer. Readiness requests may extend beyond
EOF; the trace records the requested position rather than asserting its
availability. A trace alone does not certify overridden entry validation;
`trace_sound` requires validating hooks, while `deferred_trace_sound` discharges
the recorded entries through completed workers. General module/entry rejection
traces are not claimed; the body API separately covers rejection traces.
These results are validation guarantees, not execution semantics. Production
Rust behavior is unchanged; the archived Rocq baseline remains reproducible.

Kernel-checked module regressions cover imported and defined functions,
locals/calls, imported immutable globals, initializers, exports/start, active
element/data segments, Unicode/custom sections, and malformed modules.
Consumer regressions exercise separate buffers, work-list preservation, exact
custom/readiness callbacks, and a deferred walk that dispatches an invalid body
whose worker then rejects it.
The final 2026-10-05 overnight integration passed `just lean-prove` with 1,981
build jobs and audited 7,312 Itasca theorem declarations plus 55 adapters.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. All 266
handwritten/generated implementation proof modules are reachable from the
audit; the unused external-model template is intentionally excluded.
The earlier `CoreSoundness` theorem family remains checked as a smaller
proof checkpoint.

`VisitorTrace.Event` identifies all 174 hooks by name and retains the actual
state snapshot and arguments, including signed integer values, raw floating
bits, memory alignment/offset, label depths, and derived control/stack metadata.
`Records` appends both accepting and rejecting callbacks. `instrument` supplies
this contract for any existing visitor without changing its returned result or
underlying state; `recorder` always accepts and `rejectAt` supplies a checked
rejection fixture. Numeric and memory callback meanings are transcribed from
hook mnemonics independently of the extracted dispatcher.

`Chunk`, `Completed`, and `PartialTable` relate the observations to independent
instruction bytes. The semantic token projection removes runtime snapshots and
derived metadata; the original observations retain them. `WasmBinaryUnique`
proves unique token/cursor decoding, so an accepted trace spells the same typed
body rather than an unrelated syntax witness. Nested delimiters are explicit:
a bare if has no synthetic else, and the final body end is recorded. The body
API never calls `on_function_start`; that callback belongs to code entries.

An error trace consists of complete instruction chunks and possibly the
observed prefix of one final branch table. Each table label is decoded and
bounds checked before its callback; target-signature merging follows that
callback. Therefore a label whose target causes a mismatch is already observed.
The default target has no label callback, and the closing table callback follows
all operand checks. An observed rejecting callback is included, carries the
returned visitor error, and is last. These statements describe callback
provenance and stopping; they do not classify every validator error or its
silent failure cursor. They quantify ordinary returned runs; no global hook
termination premise is needed, and no returned trace is asserted for a diverging
or panicking visitor.

The 2026-10-05 visitor-trace integration passed `just lean-prove` (1,843 build
jobs). The audit checked 4,277 imported Itasca theorem declarations, including
generated auxiliaries, plus 24 specification/visitor adapters. All dependencies were limited
to `propext`, `Classical.choice`, and `Quot.sound`; no project theorem depended
on an upstream unfinished lemma or domain axiom. Public regression examples
cover constants and malformed immediates, nonempty branch tables, polymorphic
select, locals, cached calls, memory size, reserved bytes, immutable globals,
unknown opcodes, and trailing bytes. New completeness regressions build independent
encoding, typing, and profile derivations for a nested block/if with an I32 result,
a homogeneous result-carrying branch table, and memory size feeding a direct call;
each derives actual public acceptance through `wasm_complete`. Thirteen new
visitor regressions prove exact public callback logs for signed zero, NaN
payloads, nested bare/explicit-else ifs, final end before trailing bytes,
rejected hooks, malformed/unknown table labels, target mismatch after a label
callback, default-target ordering, and raw loop-branch metadata. Rust, generated
models, and dependency pins were unchanged for this milestone, so the saved
Rocq baseline was reused.

## Proof architecture

| Files | Role |
| --- | --- |
| `ReadByte`, `Leb128`, `SignedLeb`, `SignedLeb64`, `FloatBits` | Total readers, exact bytes/cursors, completeness, and malformed-input errors. |
| `WasmSyntax`, `WasmBinary`, `WasmBinaryLabels` | Independent Wasm 1.0 opcode/immediate encoding and consumed byte prefixes, with no assumption about the unread suffix. |
| `StackSemantics`, `ScalarConst`, `NumericMeaning`, `AllNumeric`, `Select` | Mixed concrete/polymorphic operands, all constants and numeric effects, and independent numeric table agreement. |
| `EnvTranslation`, `EnvReaders`, `EnvOps`, `EnvCalls`, `MemoryMeaning`, `MemoryTyping`, `EnvMemory` | Actual environment lookup, call restrictions, reserved immediates, memory alignment, and generated typing rules. |
| `RawControl`, `CoreBranch`, `BrTable`, `WasmControlFlow` | Arbitrary-input control handlers and common-target branch-table checking. |
| `Sequence`, `WasmFrames`, `WasmInvariant` | Declarative prefix typing for active/suspended frames, nested syntax reconstruction, and byte-based stack bounds. |
| `FullVisitor`, `EnvDispatch`, `WasmStepScalar`, `WasmStepEnv`, `WasmStepControl`, `WasmStepBranch`, `WasmStep` | Actual dispatch and all successful-step preservation cases. |
| `Body`, `WasmBody`, `WasmSoundness` | Induction over remaining bytes and public termination/soundness theorems. |
| `VisitorErasure`, `BrTableErasure`, `VisitorStepErasure`, `VisitorBodyErasure` | Successful execution transfers to the empty visitor without assuming arbitrary hooks terminate. |
| `Wasm1Profile`, `WasmCompletenessBoundary` | Independent Wasm 1.0 semantic restrictions and a checked witness of the 1.0/2.0 branch-table difference. |
| `WasmBinaryComplete`, `WasmSyntaxComplete`, `DeclarativeComplete` | Reverse decoding, instruction boundaries, and normalization of generated declarative typing. |
| `StackComplete`, `ScalarComplete`, `BrTableComplete`, `ControlComplete`, `EnvComplete*` | Compatible declarative operands and exact bytes force actual handlers to succeed. |
| `ScalarStepComplete`, `BrTableStepComplete`, `ControlDispatchComplete`, `EnvStepComplete`, `CompletenessStep` | Actual dispatcher completeness for every leaf instruction. |
| `WasmExecution`, `CompletenessFrame`, `CompletenessProgram`, `StructuredProgram`, `BodyProgramComplete`, `WasmComplete` | Compose actual executions through nested syntax and close the public body completeness theorem. |
| `FullVisitorAccept`, `VisitorComplete`, `VisitorBodyComplete` | Accepting hooks preserve successful steps, including branch-table label callbacks, and lift public body acceptance/completeness to visitors. |
| `VisitorEvents`, `VisitorEventMeaning`, `VisitorEventTables` | Hook identities, exact arguments, independent semantic maps, and exhaustive dispatcher agreement. |
| `VisitorRecording`, `VisitorRunTrace`, `VisitorRefinement`, `VisitorTableRefinement`, `VisitorStepRefinement`, `VisitorBodyRefinement` | Concrete recorders, ordinary callback outcomes, and two-way instrumentation preservation through the actual API. |
| `VisitorTraceBytes`, `BrTableTrace`, `VisitorSingleTrace`, `VisitorStepLeaves`, `VisitorControlTrace`, `VisitorStepTrace` | Independent complete/partial trace relations and all instruction-level trace proofs. |
| `VisitorBodyTraceGeneric`, `WasmBinaryUnique`, `VisitorBodyTrace`, `VisitorTraceProperties`, `VisitorTraceCorollaries` | Whole-body composition, unique decoding, public trace soundness/completeness, projection, and stopping properties. |
| `VisitorTraceExamples`, `BrTableTraceExamples` | Public recording-visitor regressions for raw bits, nested control, branch-table ordering, and callback rejection. |
| `CoreExamples`, `WasmExamples`, `WasmScalarExamples`, `BrTableExamples` | Kernel-checked public acceptance/rejection examples and applications of soundness. |
| `CompletenessExamples` | Independent encoding/typing/profile derivations imply actual acceptance for nested control, result-carrying branch tables, and memory/calls. |
| `Audit` | Transitive axiom checks for every imported public Itasca theorem, including generated auxiliary declarations. |

## Dependencies

The parent repository pins `vendor/aeneas-lean` and `vendor/spectec` as source
submodules. The Aeneas checkout uses the Lean source patch in
`patches/aeneas-lean-extraction.patch`. The old Aeneas and WasmCert-Coq
dependencies are preserved only in the archived Rocq revision.

| Component | Pinned selection |
| --- | --- |
| Aeneas | `557eff83ecef5083b98a52a94ca7fae63d6c1dab` |
| Charon | `c8f15d7d658c86a95658f71ad99cddd4be002e04`, from Aeneas's `charon-pin` |
| Rust for Charon | `nightly-2026-09-17` |
| Lean and Mathlib | `v4.31.0` |
| SpecTec | `edc84f7ec81f927f3fdb952a82ecd38fed8e4f29`, from `lean-backend` |
| OCaml and Dune | `5.2.0` and `3.23.1`, in the `itasca-lean` opam switch |

The SpecTec checkpoint's own Lake project selects Lean 4.32. This project
compiles regenerated definitions and the upstream equality helper on Lean 4.31,
together with Aeneas. It does not use upstream's committed compiled Lean files.
Dune 3.24 rejects SpecTec's nested legacy `(using coq ...)` project, even when
building the generator; Dune 3.23.1 builds it without a source patch.

## Setup

Initialize the two submodules from the repository root:

```sh
git submodule update --init vendor/aeneas-lean vendor/spectec
```

Create the pinned OCaml switch:

```sh
opam switch create itasca-lean ocaml-base-compiler.5.2.0 --no-switch -y
opam install --switch=itasca-lean -y dune.3.23.1 dune-build-info.3.23.1 \
  ocamlformat.0.27.0 calendar core_unix \
  domainslib easy_logging menhir ocamlgraph ppx_deriving ppx_deriving_yojson \
  progress unionFind visitors yojson zarith pprint
```

Clone Charon at the exact commit in `vendor/aeneas-lean/charon-pin`, then install
its Rust compiler and the shared Lean version:

```sh
git clone https://github.com/AeneasVerif/charon.git vendor/aeneas-lean/charon
git -C vendor/aeneas-lean/charon checkout "$(tail -n 1 vendor/aeneas-lean/charon-pin)"
rustup toolchain install nightly-2026-09-17 --profile minimal \
  --component rustc-dev,rust-src,llvm-tools
elan toolchain install leanprover/lean4:v4.31.0
make -C lean tools
cd lean
lake exe cache get
```

The committed `lake-manifest.json` pins transitive Lean dependencies. Lake
fetches missing packages using that manifest. Reserve `lake update` for an
intentional dependency update; normal builds use `lake build`.

## Commands

From the repository root:

```sh
just extract            # Rust -> LLBC -> generated Lean
just extract-check      # Regenerate separately and reject stale models
just prove              # Build all proofs, check audit coverage and axioms
just trust              # Rerun the transitive axiom report
just verify             # Rust tests, regeneration, regressions and proofs
just lean-spec          # Build SpecTec and regenerate Wasm 2.0 into lean/.build/
just lean-spec-repro    # Regenerate the optional-mutability reproducer
make -C lean checkpoint # Check the spec and external models independently
make -C lean spec-check # Check regeneration matches committed output and compiles
make -C lean spec-update # Refresh committed spec after a reviewed source change
make -C lean regressions # Extract and check the Aeneas regression cases
```

`make -C lean tools` builds the pinned Aeneas and Charon executables.
`OPAM_SWITCH` can select another compatible switch. Charon's Cargo target
directory and LLBC output are separate from ordinary Rust builds.
Current Charon reads `[package.metadata.charon]` rather than `Charon.toml`.
The Lean Makefile therefore passes the existing `cfg(charon)` and Clone/Copy
exclusions explicitly. `--sysroot=default` uses distributed standard-library
MIR; the missing `Vec.pop` and `Vec.is_empty` operations have concrete models
in the handwritten `Itasca/Generated/FunsExternal.lean`.

For proof iteration, run `lake build Itasca.Branch` (or the changed module) from
`lean/`; this updates its dependencies without building unrelated proof modules.
Run `just prove` when integrating changes so audit coverage and axiom checks run.
The `lean-extract` and `lean-prove` names remain compatibility aliases.
Keep `.lake/` and `.build/` between runs. Proof-only changes do not require Rust
tests or another `just trust`; see the
[change-specific check policy](../AGENTS.md#before-saying-you-are-done) and
[parallel work plan](../LEAN_PORT.md#iteration-and-parallel-work).

## Specification sources

The `SpecTecGenerated` Lake library reads the committed, locally generated
`SpecTec/wasm2.0.lean`. The `SpecTecSupport` library reads upstream's handwritten
`ExtendedDeriveDecEq.lean` helper directly. Neither uses upstream's committed
compiled Lean files.

`just lean-spec` regenerates definitions with `--lean --single-pattern-match
--wf-state all`. Output stays in `.build/wasm2.0.lean` so regeneration cannot
overwrite the committed generated specification. `make -C lean spec-update` copies this
output to the committed local source; `spec-check` checks it byte for byte.
The original checkpoint remains available in the SpecTec checkout for comparison.

`Itasca/SpecChecks.lean` exercises generated typing judgments, including both
global mutabilities. `TypeTranslation.lean` connects the extracted types to
these definitions. The proof architecture above connects those judgments to the
public body and module validators. Earlier focused modules (`Block`, `End`, `Numeric`,
`EndTyping`) retain their independent handler contracts and examples.

`scripts/check_audit.py` checks that every implementation/proof source module
is reachable from the audit and rejects importing the external-model template.
`Audit.lean` automatically discovers public theorems in the `Itasca` namespace
from its imports and checks their transitive dependencies. Private helpers are
covered through their callers. It rejects every axiom except `propext`,
`Classical.choice`, and `Quot.sound`; new proof modules must be imported into the
audit. It also checks the numeric/memory opcode maps, floating-point translation,
environment context, and final validity predicate directly. This prevents new
exported theorems from being omitted accidentally from a manually maintained list.

The regenerated specification still contains unfinished upstream lemmas and
opaque execution models. The local theorems must not depend on `sorryAx` or
unreviewed domain assumptions. Compiling all definitions is not evidence of
whole-module validator correctness or of a complete upstream formalization.

## Rocq baseline

[baseline/revisions.json](baseline/revisions.json) records the starting revisions.
[baseline/rocq-trust.txt](baseline/rocq-trust.txt) records all 121 declarations
reported by `just trust`, with zero kernel bypasses.

At the start of this port, `cargo test`, `just extract-check`, `just prove`, and
`just trust` all passed. The Rust suite reported 294 tests and one doctest.
The four reference counts are:

| Theorem | Rocq assumptions |
| --- | ---: |
| `validate_body_with_typed` | 41 |
| `validate_module_no_panic` | 48 |
| `validate_module_typed` | 51 |
| `validate_module_typechecked` | 52 |

Neither Rust nor the generated Rocq theories changed during this baseline.
Lean assumption reports must identify their dependencies explicitly; raw counts
are not comparable between the provers.
