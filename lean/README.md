# Lean verification

This is itasca's active verification pipeline, implementing the
[Lean port plan](../LEAN_PORT.md). The Rocq version is archived under
`rocq-baseline`. See the [guarantee comparison](PARITY.md),
[final validation record](baseline/VALIDATION.md), and
[upstream change tracker](../UPSTREAM.md).

Multi-value body and whole-module verification is complete for the supported
subset. Both profiles use the same Rust streaming module driver and shared
profile-parameterized module proofs. `Itasca/Binary/SignedLeb33.lean` proves the
signed block-index reader; `Itasca/MultiValue/` connects block decoding to
generated `Blocktype_ok` and provides the following checked contracts:

| Module | Checked multi-value claim |
| --- | --- |
| [SignatureEquality](Itasca/MultiValue/SignatureEquality.lean) | Descriptor comparison terminates and decides equality of the resolved type vectors, including distinct indices with equal signatures. |
| [StackSemantics](Itasca/MultiValue/StackSemantics.lean) | Descriptor pops preserve stack interpretation and accept compatible operands; pops and guarded pushes terminate on structurally bounded stacks. |
| [SuffixTyping](Itasca/MultiValue/SuffixTyping.lean) | `check_suffix.wasm_spec` combines totality with acceptance exactly when independent stack realization and generated `Resulttype_sub` hold. Equal-arity targets share a common subtype, including `BOT`. |
| [Calls](Itasca/MultiValue/Calls.lean) | Applying a function signature terminates, consumes all parameters, and appends all results; compatible operands imply acceptance within signature and capacity limits. |
| [ControlTotal](Itasca/MultiValue/ControlTotal.lean), [EndTotal](Itasca/MultiValue/EndTotal.lean) | Entry, branches, branch tables, calls, and frame closing preserve structural bounds without moving the cursor backward, including their error paths. Entry additionally requires room for a frame. |
| [ScalarTotal](Itasca/MultiValue/ScalarTotal.lean) | The shared scalar dispatcher terminates on structurally bounded multi-value frames with room for one operand, preserving control depth and cursor progress. |
| [BodyTotal](Itasca/MultiValue/BodyTotal.lean) | `multi_value.validate_body.wasm_total` proves that every byte sequence, environment, locals vector, and type index returns an ordinary success/error result without modeled panic or divergence. The actual extracted loop uses cursor progress and a control-depth bound derived from consumed bytes. |
| [Syntax](Itasca/MultiValue/Syntax.lean), [Binary](Itasca/MultiValue/Binary.lean) | Independent structured body grammar with indexed block signatures, nonminimal signed s33 indices, shared scalar immediates, and exact consumption including the final `end`. Block byte spans are equivalent to `BlockDecoded`; encoding does not assume that indices resolve. |
| [Prefix](Itasca/MultiValue/Prefix.lean), [Frames](Itasca/MultiValue/Frames.lean) | Semantic control invariant with arbitrary block parameters/results, saved parent arguments, generated label correspondence, and signatures projected from the shared control stack. Entry, child closing, else reset, and function closing preserve the ghost typing derivations. An omitted else uses equal resolved parameter/result vectors, including nonempty ones. |
| [Invariant](Itasca/MultiValue/Invariant.lean) | Consumed-byte invariant, exact extracted initialization, and completion certificate combining independent encoding with generated body typing. The selected function signature supplies return types; function parameters remain locals. |
| [Soundness](Itasca/MultiValue/Soundness.lean) | `multi_value.validate_body.wasm_sound` proves that acceptance by the actual extracted public body validator yields `MultiValue.Validated`: independent binary provenance and generated SpecTec body typing. `wasm_spec` combines this with termination. Neither theorem assumes valid bytes, an environment profile, or a valid type index. |
| [Complete](Itasca/MultiValue/Complete.lean) | `multi_value.validate_body.wasm_complete` derives acceptance from `MultiValue.Validated`, the body-byte limit, and `EnvironmentWithinLimits`. `wasm_complete_of_typing` exposes the instruction tree; `wasm_accepts_iff` gives the equivalence within those limits. No handler-success, execution, or abstract preservation premise is exposed. |

Whole-body proofs cover the actual extracted `multi_value.validate_body`,
including initialization, all opcode arms, final `end`, and exact byte consumption.
Completeness follows independent declarative derivations through parameterized
blocks and loops, both binary forms of `if`, calls, returns, and branch tables
with a common `BOT` subtype. `EnvironmentWithinLimits` requires at most 1000
parameters and 1000 results per stored type and direct-call signature; the body
must fit `MAX_FUNCTION_BYTES`. A byte-based operand bound discharges vector
capacity checks on both 32-bit and 64-bit platforms. The grammar reuses scalar
instruction encodings and does not cover other Wasm 2.0 proposals.

[Grammar and control regressions](Itasca/Examples/MultiValueGrammar.lean) cover
padded type indices and a multi-value identity if without an explicit else.
[Whole-body regressions](Itasca/Examples/MultiValueBody.lean) derive public
acceptance from independent encoding and typing for two-result identity blocks,
omitted else arms, branches to loop parameters, and differently typed branch-table
targets sharing a `BOT` subtype. A [whole-module regression](Itasca/Examples/MultiValueModule.lean)
derives acceptance and metadata for a two-result function from the shared
module completeness theorem, then proves the same bytes are rejected under
Wasm 1.0.
Both profiles execute the visiting body loop in `src/multi_value.rs`, with one
control stack storing full signatures. Profile dispatch preserves their
different control rules and callback order. There is no separate multi-value
module driver. [Checked loop refinement](Itasca/Body/SharedLoop.lean) connects
the shared runtime to the existing Wasm 1.0 proofs, using a
[proof-only execution model](Itasca/Body/LegacyExecution.lean); multi-value
adapters connect the same runtime to its semantic body proofs.
The [shared body/entry contracts](Itasca/Profile/Body.lean) connect both
specializations to one module proof chain. [Visitor adapters](Itasca/Profile/BodyVisitor.lean)
provide termination, soundness, and accepting-hook completeness for both. All
multi-value proof modules, including proof-bearing adapters, are covered by
`Itasca.Audit`; the trust base is unchanged.

The whole-module claims cover the actual streaming driver and its synchronous
`validate_module` wrapper for either explicit profile, with shared environment,
entry, and tail composition. `MultiValue` does not include other Wasm 2.0 proposals. Generic streaming theorems separate source coherence, callback
returning behavior, worker provenance, and accepting scheduler premises. See the
[embedding obligations](../DEVELOPMENT.md#embedding-obligations).

The full Rust extraction and freshly regenerated SpecTec definitions compile
together. Local source patches fix Aeneas naming and indentation bugs and work
around SpecTec's loss of optional mutability and ambiguous import projections,
and correct its four-byte UTF-8 upper bound. Tool builds and regeneration apply
the patches automatically; see [upstream/](upstream/README.md) for their scope
and regressions.

The full Wasm 1.0 function-body proof is checked in
[`Itasca/Body/WasmSoundness.lean`](Itasca/Body/WasmSoundness.lean) and
[`Itasca/Visitor/VisitorBodyErasure.lean`](Itasca/Visitor/VisitorBodyErasure.lean), with completeness
in [`Itasca/Body/WasmComplete.lean`](Itasca/Body/WasmComplete.lean) and
[`Itasca/Visitor/VisitorBodyComplete.lean`](Itasca/Visitor/VisitorBodyComplete.lean), and visitor traces
in [`Itasca/Visitor/VisitorBodyTrace.lean`](Itasca/Visitor/VisitorBodyTrace.lean). It covers the
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
[`WasmCompletenessBoundary`](Itasca/Examples/WasmCompletenessBoundary.lean) example proves
generated 2.0 typing and actual `TypeMismatch` rejection for the same 11 bytes.
The profile preserves existing Wasm 1.0 behavior without changing Rust or the
upstream specification.

The public whole-module API is a synchronous wrapper over the sole module
driver, `stream.validate_streaming`. The `profile_*` theorems quantify over
`ValidationProfile`; the existing `wasm_*` names remain Wasm 1.0 specializations
with their prior premises. Both are corollaries of the concrete slice and
synchronous-worker proofs:

| Theorem | Checked claim |
| --- | --- |
| [`module.validate_module.profile_spec`, `profile_total`, `profile_sound`](Itasca/Module/ModuleValidation.lean) | Every input returns an ordinary result; acceptance establishes the complete module certificate without source, scheduler, or body-validation assumptions. |
| [`module.validate_module.profile_complete`, `profile_complete_with_metadata`](Itasca/Module/ModuleCompleteness.lean) | Independent module encoding within limits, elaboration, generated typing, signature caps, and the selected profile imply acceptance and exact returned metadata. |
| [`stream.validate_streaming.profile_sound`](Itasca/Stream/StreamValidation.lean) | An accepted run, coherent source views, and worker provenance establish `ModuleSound.Validated` for the concatenated bytes, returned environment, and exact tail from the actual `tail_ready` call. |
| [`stream.validate_streaming.profile_total`](Itasca/Stream/StreamDriverTotal.lean) | Returning source and scheduler callbacks imply an ordinary result on arbitrary bytes. Unfinished or malformed returned batches need no provenance premise. |
| [`stream.validate_streaming.profile_complete`](Itasca/Stream/StreamDriverComplete.lean) | The same independent valid-module premises, canonical available source regions, and an accepting scheduler policy imply actual acceptance and metadata for that same raw module. |
| [`stream.validate_module_slice.profile_total`, `profile_sound`, `profile_spec`](Itasca/Stream/StreamSlice.lean) | The private contiguous adapter discharges source coherence, callback totality, and worker provenance. |
| [`stream.validate_module_slice.profile_complete`, `profile_complete_with_metadata`](Itasca/Stream/StreamSliceCompleteness.lean) | The concrete source and synchronous worker discharge generic completeness obligations, returning the exact environment/tail pair. |

`ModuleSound.Validated data decoded profile` supplies one raw module whose
independent `ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile)`
uses the same profile to account for the whole input. `Elaborates`
connects that same module to generated SpecTec syntax, excluding out-of-range
function-type fallback and truncated function/code pairing. The generated
`Module_ok` derivation uses imported and defined index spaces in their actual
order. `ModuleElaboration.Profile raw profile` additionally establishes unique
decoded export names, the supported table/memory counts, and the selected
signature and instruction restrictions. The independent byte grammar selects
Wasm 1.0 or multi-value control forms and active-segment encodings.

The certificate identifies the decoded environment and data segments, proves
cache coherence, and proves that the actual `import_types` and `export_types`
functions succeed and report the same module's types in order. Names retain
strict Unicode scalar encoding, including four-byte scalars. Initializers see
only immutable imported globals; bodies see the full global space. Element/data
segments and start functions are covered. The generic API returns an environment
and `()`, so its `StreamRun.Accepted` witness records the actual delivered tail;
it does not assume arbitrary visitor state stores that tail. The concrete
synchronous adapter proves its returned `Module` contains exactly that pair.

Completeness starts from `ModuleEncodingWithinLimits raw bytes profile`,
`ModuleSignaturesWithinLimits raw profile`, `Elaborates`, generated `Module_ok`,
and `ModuleElaboration.Profile raw profile` for the same independent raw module. No parser-success,
decoded-cache, local checker, or prevalidated-entry premise is exposed. Limits
constrain actual module bytes, encoded instruction bodies including their final
`end`, and declared locals excluding parameters. Nonminimal valid LEB encodings,
empty/absent code sections, strict UTF-8, and exact input consumption remain part
of the binary grammar and framing proofs. Multi-value signature caps require at
most 1000 parameters and 1000 results; the corresponding Wasm 1.0 bound predicate
is `True`, preserving its prior parameter behavior. Caps do not redefine
`ModuleConditions` or language validity.

The streaming assumptions deliberately separate three claims:

- `StreamSource.Coherent` relates successful environment/tail views, code length,
  and bounded code reads to fixed logical bytes. Soundness permits read errors
  and does not assume a canonical split or valid bytes.
- `StreamSource.CallbacksTotal` and `StreamScheduler.CallbacksTotal` require
  ordinary callback results. They do not require source coherence, worker
  provenance, successful finish, or rejection of every malformed worker.
- Completeness uses `StreamSource.CanonicalAvailable` and
  `StreamAcceptingScheduler.Accepts`: positive batch settings, accepting hooks,
  preserved queue state, and returned queued results of actual `validate_all`
  executions, in any order. `StreamBatchComplete` derives their successful finish
  from independent typed entry encodings. This is one sufficient accepting worker
  policy, not an exhaustive classification of worker implementations.

`StreamScheduler.Provenance` connects historical issued descriptors to worker
states through `StreamBatch.Reachable`, the closure of actual `next_entry` and
`validate_func` calls. Dispatch and validation have independent cursors. Stored
errors remain sticky. A successful `finish` derives ordered typed entry encoding
and exact byte coverage; it is not a provenance premise. The driver validates
module IDs, pending IDs, and finish results, removes each accepted pending ID,
and drains all remaining work. Every callback preserves the scheduler relation,
including custom sections and tail delivery. Actual OS scheduling, network
progress, FFI safety, and compiler IR correctness remain embedding obligations.

`ModuleCodeEntry`, `ModuleEnvSemantics`, `ModuleTail`, `ModuleCodeSemantic`, and
`ModuleSoundness` provide shared component facts and driver-independent certificate
assembly. `Profile/Types`, `Profile/Body`, and `Profile/CodeEntry` separate
language restrictions, resource bounds, independent encodings, and generated
typing. `ModuleEnv.profile_accepted_entry_conditions` derives per-entry
bounds, `Profile.Environment`, and `Profile.EnvironmentWithinLimits` from an
actual accepted environment decode, including entries in another buffer.
`ModuleEntryVisitor` and `ModuleCustomVisitor` preserve acceptance under callback
replacement. Successful custom/opcode visitor erasure has no termination premise
for unrelated callback executions. `Profile/EntryComplete` derives actual entry acceptance from independent typed
bounded encodings for either profile; `ModuleCodeEntryComplete` retains the
Wasm 1.0 wrapper.

The legacy `validate_module_with`, `validate_code_with`, `validate_code`,
`CodeVisitor`, `ValidatingCodeVisitor`, and `code_section`/`CodeSection` APIs and
their orchestration-specific proofs have been removed. Their deferred-code and
whole-module callback-trace contracts were retired; they are not claims about
`StreamingVisitor`. The shared `ModuleVisitor` custom hooks and `OpVisitor`
entry/body hooks remain. Body and entry callback traces retain their guarantees:

| Consumer interface | Retained theorem |
| --- | --- |
| Separate entry after decoding the environment, either profile | `module.validate_code_entry.profile_spec_of_env` |
| Accepted entry with original callback trace | `module.validate_code_entry_with.trace_sound` |
| Arbitrary accepted opcode visitor | `code.validate_body_with.wasm_sound` |
| Accepted body with exact callbacks | `code.validate_body_with.trace_sound` |
| Independently valid body with accepting callbacks | `code.validate_body_with.trace_complete` |
| Rejecting body callback is last and matches the result | `code.validate_body_with.trace_rejection_last` |

[Entry traces](Itasca/Module/ModuleEntryTrace.lean) include the function-start event and
exact body operators, with the body start tied to the entry's encoded locals.
[Custom ranges](Itasca/Module/ModuleCustomRanges.lean) identify exact UTF-8 name bytes
before `payload_start` and bound both name and payload intervals in their input
buffer. A general trace specification for rejected module/entry runs is not
claimed; the body API separately covers rejection traces.

Kernel-checked regressions retain shared body/module acceptance, metadata, and
malformed-input examples and add actual batch protocol and streaming cases.
The audit permits only `propext`, `Classical.choice`, and `Quot.sound`; no
project-specific axioms or kernel bypasses were added. New proof modules and
proof-bearing adapters are reachable from `Audit`. Run `just prove` for current
coverage and dependency counts. The earlier `CoreSoundness` family remains
checked as a smaller proof checkpoint.

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
proves unique token/cursor and structured-body decoding, so an accepted trace
spells the same typed body. `ModuleBinaryUnique` proves unique raw-module
decoding, including custom sections and omitted standard sections. Both
uniqueness results are independent of typing and implementation-size limits. Nested delimiters are explicit:
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

Implementations are grouped by proof layer. The root `Itasca` directory retains
public entry modules such as `WasmSoundness`, `ModuleValidation`, and
`StreamValidation`; existing imports and exported theorem names remain available.
Internal imports use the directories below.

| Directory | Main responsibilities |
| --- | --- |
| `Binary/` | Independent body/module grammars; unsigned and signed LEB, floating bits and UTF-8; prefix, structured-body and raw-module uniqueness. `SignedLebGeneric` supplies one signed-reader proof specialized by `SignedLeb` and `SignedLeb64`. |
| `Body/` | Stack/control/environment semantics, generated typing, the recursive Wasm 1.0 profile, soundness and completeness. `WasmFrames`, `WasmInvariant`, and `WasmStep*` share the stronger profile-preserving invariant; both public soundness contracts project from this proof. |
| `Profile/` | Shared language/resource predicates and body/entry certificates; adapters connect both implementations to the same module/streaming proof chain. |
| `MultiValue/` | Indexed signatures, stack/control semantics, independent multi-value grammar, body totality/soundness/completeness, and visitor adapters. |
| `Visitor/` | Total/accepting hooks, erasure, instrumentation, and exact callback traces. `OpDispatch` supplies common dispatcher equations to erasure, completeness, and trace proofs. |
| `Module/` | Environment/entry/tail parsing, elaboration, index spaces, metadata, independent module certificates, and public whole-module corollaries. |
| `Stream/` | Source contracts, framing, worker provenance, scheduler policy, the driver, and concrete synchronous slice adapters. |
| `Examples/` | Kernel-checked acceptance/rejection, trace, completeness, Unicode, streaming, and Wasm 1.0/2.0 boundary regressions. |
| `Support/` | Common result inversion and extracted-to-SpecTec type translation. |
| `Generated/` | Committed extracted types/functions and handwritten external models. |
| `Audit.lean` | Transitive axiom checks for every declaration originating in a local module, across namespaces and declaration kinds. |


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

For proof iteration, run `lake build Itasca.Body.Branch` (or the changed module) from
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
`Audit.lean` selects every declaration whose originating module is under
`Itasca`, irrespective of its namespace or declaration kind. This directly
checks private helpers, definitions with proof fields, generated auxiliaries,
semantic adapters, and external models as well as public theorems. It rejects
every transitive axiom except `propext`, `Classical.choice`, and `Quot.sound`.
New proof modules must be reachable from the audit; new adapters need no
separately maintained list of roots.

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
