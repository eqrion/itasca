# Execution proofs

Start with the [execution boundary](../README.md#execution-boundary) for
guarantees and premises. This guide explains how the proofs are assembled.
The [Lean guide](../README.md) covers tool setup and the independent validator.

## Canonical public constructions

The headline modules are the roots listed in
[`scripts/reachability.lean`](../scripts/reachability.lean); `just dead`
reports declarations they do not reach.

Evolving-world invocation is constructed in
[PublicExecutableWorldResources](Theorems/Invocation/PublicExecutableWorldResources.lean).
It establishes correspondence, exact recording, the retained invariant and
resource causes together. Shared
[outcomes and erasure](Theorems/Invocation/ExecutableWorldOutcomes.lean) sit below
that construction; ordinary invocation is a short projection. Generic weaker
contracts remain available when capacities or recording-head evidence are absent.

Evolving-world instantiation correspondence is constructed by
[recorded source execution](Theorems/Instantiation/InstantiateExecutableWorldRecordedSource.lean).
The actual-API recording adapter supplies ordinary correspondence by erasure.
The [compiled package erasure](Theorems/Instantiation/InstantiateExecutableWorldRecordedCompiled.lean)
is shared by accepted and all-input ordinary wrappers. Resource causes remain a
supporting construction below the combined recording/resource theorem, avoiding
a cycle back through ordinary source correspondence.

## Dependency layers

Each layer may use earlier foundations. The extracted model and the abstract
source machine are independent branches; representation certificates join them.
`lean/scripts/check_audit.py` enforces the library boundaries and integration
stages. `Exec.Audit` checks every reachable declaration, including definitions
with proof fields, against the standard logical axiom allowlist.

| Layer | Responsibility |
| --- | --- |
| `SpecExt/`, `Exec/Spec/` | Handwritten source semantics, generated-rule lemmas, numeric and store semantics. |
| `Exec/Abs/` | Abstract source machine, typing, ownership, simulation, and progress; no extracted runtime dependency. |
| `Exec/Generated/` | Extracted runtime and handwritten external adapters; only the adapters directly reuse validator generated modules. |
| `Exec/Platform/` | Allocation, memory, floating-point, callback, and recording contracts. |
| `Exec/Representation/` | Slot layout, encoding, store decoding, type/function tables, and source capacity certificates. No compiler, interpreter, or store-construction proof imports. |
| `Exec/Code/` | Compiler correctness, from individual operations to complete-module certificates. |
| `Exec/Interp/` | Concrete interpreter operations, machine preservation, source correspondence, and invocation. |
| `Exec/Store/` | Issued-object API, linking, preparation, publication, initialization, and instantiation. |
| `Exec/Theorems/` | Public API composition and specialized corollaries. |

Store decoding and capacity contracts belong to `Representation`, below both
interpreter and store proofs. Their definitions describe data and independently
validated source capacities. Compiler proofs establish the certificates;
interpreter proofs consume them. The representation layer never assumes the
execution theorem it is used to prove.

Declaration namespaces retain their semantic owners (`Exec.Code`, `Exec.Interp`,
and `Exec.Store`), while module paths express dependency layers. For example,
`Exec.Store.decodeStore` is defined in `Exec.Representation.Store` because both
interpreter and store construction need it.

## Compiler stages

`Code/Local/` proves facts about individual compiler operations and emitted
fragments. Its subdirectories separate source traces, relations, callbacks,
lowering, capacities, and initializers.

`Code/Body/` composes reader steps and control scopes into body and entry
certificates. Topic directories distinguish scalar, float, memory, table,
control, and SIMD arguments. Helpers that depend on the body fold live here,
even when their conclusion concerns one callback or one capacity bound.

`Code/Module/` assembles entries, scheduling, finalization, and complete-module
results. The audit forbids Local → Body/Module and Body → Module imports.
The compiler theorem constructs one independently encoded source module and
its metadata, function, initializer, and capacity certificates.

## Interpreter and store

Interpreter `Relations/` describes frames, slots, stores, and operation inputs.
`Numeric/`, `Memory/`, `State/`, `Simd/`, `Control/`, and `Calls/` prove individual
runtime operations. `StructuredMachine/` supplies common machine machinery;
`Core/`, `FloatCore/`, `Cumulative/`, and `Machines/` contain specialized
relations and their adapters. A specialization should apply a generic lemma
when its premises match, rather than repeat the structural proof.

`Interp/Invocation/` composes setup, loop behavior, readback, errors, recording,
and divergence. Other interpreter modules cannot import this integration stage.

Store `Invariant/` establishes retained metadata and code properties. `Api/`
proves issued-object operations, `Linking/` resolves imports, `Preparation/`
stages allocations, and `Initialization/` handles initializers and segments.
`Store/Instantiation/` joins these operations with publication and start
execution. Lower store modules cannot import this integration stage.

Instantiation distinguishes failure before publication, which rolls back, from
failure after publication, which retains initialization/start effects. Host
callbacks may extend the ghost code interpretation; old issued keys retain
their meaning. These distinctions must remain visible in theorem statements.

## Source store typing

[`ExecutableInv.source_typed`](Theorems/Api/ExecutableInv.lean) and
[`CertifiedApiStore.source_typed`](Theorems/Api/CertifiedApi.lean) derive the
generated `Store_ok` judgment. Their bridge uses the existing certificates below;
it does not assume store typing or execution correctness as another field.

| Source obligation | Retained evidence and construction |
| --- | --- |
| Global values, memories, tables and reference membership | `Shape` and the object lemmas in [Invariant/Typing](Store/Invariant/Typing.lean). |
| Data and element segments | `SegmentBounds`, reference shape, and the same object-typing lemmas. |
| Wasm bodies and module environments | `CoreFunctionsTyped` retains `Func_ok` under the exact canonical `ModuleBindings`. [Abs/StoreTyping](Abs/StoreTyping.lean) recovers generated module-instance typing. |
| Export membership and unique source names | `ExportBounds` retains descriptor bounds and decoded-name uniqueness, constructed from validator `ModuleEnv.Valid`. Completed instance maps resolve each export into its own module namespace. |
| Host functions | The repaired generated host `Funcinst_ok` rule types signatures without Wasm bodies; the decoder's empty module environment is well formed. |

[Invariant/SourceStoreTyping](Store/Invariant/SourceStoreTyping.lean) assembles
these facts. Existing API preservation theorems retain their certificates on
success and error, including committed effects and evolving code interpretations.
Intermediate preparation states need typing only where that invariant is
established. Atomic host return and trap require post-call `Store_ok`.
`Platform.HostSound.of_invariant` derives this obligation from invariant
preservation and its checked source-typing projection. Recorded, resource-cause,
and divergence proofs retain the stronger host target.
[Typing/HostStepPreservation](Spec/Typing/HostStepPreservation.lean) proves configuration
preservation for every generated Wasm step, host step, evaluation context, and
finite reduction sequence.

## Source choices and open execution

`Spec/Typing/` proves source configuration typing, value/stack inversion, and
preservation. `Spec/Choices/` defines admissible scalar, SIMD, growth, and
completed-host choices, their coverage, erasure, and outcome agreement.
`Spec/Open/` adds suspended Wasm continuations, host control, expanded histories,
and finite or infinite combined execution. These directories are source-only;
they cannot depend on the extracted runtime.

The choice proofs distinguish a selected outcome from global determinism.
[Choices/Determinism](Spec/Choices/Determinism.lean) establishes fixed-policy
one-step uniqueness outside active trap cleanup.
[Choices/TrapNormalization](Spec/Choices/TrapNormalization.lean) proves that
cleanup terminates with the same state and events, despite overlapping steps.
[Choices/ChosenOutcomes](Spec/Choices/ChosenOutcomes.lean) combines the two to
establish terminal outcome agreement and exclude infinite execution under a
policy with a terminating run. `Abs/` and interpreter chosen adapters retain
these policies through the existing simulations.

## Compiler completeness

The compiler uses the same Local → Body → Module stages for soundness and
acceptance. The additional local directories separate the maintained evidence:

| Directory | Responsibility |
| --- | --- |
| `Code/Local/Demand/` | Independent source demand and recorded stack/control peaks. |
| `Code/Local/Capacity/` | Counter accounting, allocation availability, and accepting callbacks. |
| `Code/Local/Coordinates/` | Source offsets, target bounds, and callback coordinate preservation. |
| `Code/Local/Publication/` | Open/closed control maps and final published ranges/header. |
| `Code/Local/Checking/` | Stored-instruction checks, pending forward branches, and exit-slot bounds. |

`Code/Local/Source/` retains the underlying source/compiler relations and typed
source traces. These relations describe the source independently of compiler
success. Shared lemmas belong at the lowest stage their imports permit.

`Code/Body/Reader/` keeps opcode-family adapters in `Control/`, `Calls/`,
`Memory/`, `Table/`, `Float/`, and `Simd/`. Cross-family composition uses:

| Directory | Responsibility |
| --- | --- |
| `Acceptance/` | Successful reader/callback replay from source prefixes and resource demand. |
| `Checking/` | Complete-profile instruction-check and exit-slot invariants. |
| `Publication/` | Source coordinates and control maps through complete reader steps. |
| `Replay/` | Single-callback loop and profile replay. |
| `Source/` | Source opcode classification and whole-body advance/step composition. |
| `Common/` | Shared reader/compiler relations used by the topic adapters. |

`Code/Body/Relations/Common/BodyAcceptanceWasm1` and `BodyAcceptanceWasm2`
construct actual body success. `BodyPublicationWasm1/Wasm2` retain coordinates
and maps; `BodyCheckedWasm1/Wasm2` establish the checker premises at root close.
These are complementary invariants, not alternative versions of the body proof.

`Code/Module/EntryFinishAvailable` composes entry parsing, body compilation,
and actual finishing. Module demand envelopes account for metadata, functions,
initializers, scheduling, collection, output counters, and temporary reserves.
[CompilationComplete](Theorems/CompilationComplete.lean) constructs successful
compilation and the existing certificate for both complete profiles from
independent source validity, conservative source-only `CompileEligible`,
allocator correctness, and bounded allocation availability. It assumes neither
compiler success nor a completed callback trace. Uniform source maxima can
exclude modules whose actual output would fit exactly at a configured limit.

## Host composition

The atomic host-call proofs remain directly in `Theorems/Host/`. The additions
are grouped by the interfaces they build on:

| Directory | Responsibility |
| --- | --- |
| `Theorems/Host/Callbacks/` | Executable checked action languages, independent effects, finite callback contracts, and host-local control. |
| `Theorems/Host/Chosen/` | Selected atomic host outcomes and primitive choice compatibility. |
| `Theorems/Host/Reentrant/` | Returning callback packages, depth-staged nested calls, and no-start publication. |
| `Theorems/Host/Open/Driver/` | Combined executable driver, continuation stack, guards, effects, and root adapters. |
| `Theorems/Host/Open/Native/` | Partial native execution and finite invocation correspondence. |
| `Theorems/Host/Open/Erasure/` | Erasing combined ticks and histories into synchronous native execution. |
| `Theorems/Host/Open/Source/` | State representation, Wasm/control transitions, and selected source simulation. |
| `Theorems/Host/Open/Completeness/` | Reference-prefix alignment and selected combined outcomes. |
| `Examples/Host/` | Checked publication, finite reentry, and productive-divergence examples. |

The groups build in the order Callbacks → Chosen → Reentrant → Open. The audit
permits imports of earlier groups and rejects imports of later groups. Within `Open/Source/`, `State/` holds representation and
prefix invariants, `Wasm/` native preparation and Wasm steps, `Control/` host/API
transitions, and `Chosen/` the selected-policy adapters. These are topic groups;
imports between them follow the actual proof dependencies.

`Open/Driver/ReentrantControl` implements the synchronous driver using explicit
continuations and fresh nested executions. Its ticks preserve the full store
invariant and expanded history, including effects before divergence.
`Open/Erasure/` and `Open/Native/` connect those same ticks to the native
routines. `Open/Source/` establishes combined source correspondence.
[ChosenSourceCompleteness](Theorems/Host/Open/Completeness/ChosenSourceCompleteness.lean)
matches a terminating selected combined run; source-prefix capacities,
allocation availability, and numeric/vector/growth/API/publication compatibility
remain explicit premises. Reference Wasm segments retain the reference suffix's
choice index across differing trap-cleanup lengths.
[ReturningRecovery](Theorems/Host/Open/Completeness/ReturningRecovery.lean)
recovers the ordinary returning callback package for the finite action subclass.

These callback implementations are Lean models of the interface. Arbitrary
Rust callbacks still need a refinement contract. Concrete publication currently
supports modules with empty imports and no start function.

## Reading and extending the proofs

1. Read the relevant public theorem and its explicit platform contracts.
2. Follow its certificates into `Representation` and the compiler module result.
3. Follow execution into invocation, machine steps, and operation lemmas.
4. Check the source correspondence in `Abs` and `Spec`.

Names such as `Core`, `FloatCore`, `Cumulative`, and `Executable` distinguish
instruction grammars and theorem premises. They are not interchangeable proof
versions. A module imported only by the audit can still expose an independent
result or regression theorem; lack of downstream imports alone does not make
it dead code.

Shared slice lookup and list transport lemmas live in
[Representation/Collection.lean](Representation/Collection.lean). Start-wrapper
specializations use [Theorems/Instantiation/StartEquation.lean](Theorems/Instantiation/StartEquation.lean).
Keep shared helpers at the lowest layer supported by their actual dependencies.

Run `just check Exec.Module` while iterating, `just audit-imports` after file
moves, and both `just prove` and `just prove-exec` for integration. Rust changes
also require both Cargo test configurations and extraction/regeneration checks,
as specified in [DEVELOPMENT.md](../../DEVELOPMENT.md). Preserve build caches.
