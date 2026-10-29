# Execution proofs

Start with [Main](../Main.lean): it lists every headline theorem, each stated in
full under [Results/](../Results), and [Contracts](Contracts.lean) lists every
premise an embedder must discharge. The
[execution boundary](../../README.md#execution-boundary) summarizes the guarantees.
This guide explains how the proofs are assembled. The [Lean guide](../../README.md)
covers tool setup and the independent validator.

## Canonical public constructions

[Main](../Main.lean) and [Results/](../Results) expose the public theorems;
[`scripts/reachability.lean`](../../scripts/reachability.lean) lists their
reachability roots. Each result projects an internal construction:

| Public result | Construction |
| --- | --- |
| Compilation soundness and completeness | [Compilation/Certificate](Integration/Compilation/Certificate.lean) and [Compilation/Complete](Integration/Compilation/Complete.lean) |
| Invocation behavior, termination and no spurious errors | [Invocation/Behaves](Integration/Invocation/Behaves.lean), using [Resources](Integration/Invocation/Resources.lean) and [Outcomes](Integration/Invocation/Outcomes.lean) |
| Total instantiation and its source outcome | [Instantiation/InstantiateSource](Integration/Instantiation/InstantiateSource.lean) |

Invocation retains exact recorded host events, resource causes, the final code
interpretation, and the full store invariant. Divergence means an infinite
source run or a reachable diverging host callback. Instantiation runs no host
callback or start function: it links, allocates, initializes, and returns the
resolved start function for a separate invocation.

## Dependency layers

The extracted program and the source machine are independent foundations;
representation certificates connect them. [The audit checker](../../scripts/check_audit.py)
enforces library boundaries, compiler stages, and acyclic imports.
[Itasca.Audit](../Audit.lean) checks all declarations, including proof-bearing
adapters, against the standard logical axiom allowlist.

| Area | Responsibility and boundary |
| --- | --- |
| `SpecExt/`, `Spec/` | Source semantics, generated-rule algebra, typing, numeric and store semantics; no extracted runtime dependency. |
| `SourceMachine/` | Flat source states, decoding, transitions, typing, ownership, simulation and progress; independent of the extracted runtime. |
| `Equations` | Shared equation lemmas; the sole runtime gateway to `Itasca.Generated.Funs`. |
| `Platform/` | Allocator, memory, floating-point, callback, recording and divergence contracts. |
| `Representation/` | Slot layout, encoding, store decoding, function tables and source capacity certificates; no compiler, interpreter or store-construction imports. |
| `Compiler/` | Per-operation emission, body construction, then complete-module certificates. |
| `Interp/` | Concrete operations, machine relations and preservation, then invocation. |
| `Store/` | Issued-object APIs, invariants, linking, preparation, initialization and instantiation. |
| `Integration/` | API certificates and constructions joining compilation, execution, hosts and instantiation. |
| `Contracts` | Embedder obligations, including `Platform.Laws` and `HostLaws`; its only integration dependency is the exact [Api/ExecutableInv](Integration/Api/ExecutableInv.lean) module. |
| `../Results/`, `../Main` | Public statements shared with the validator; only `Main` and examples import runtime results. |

Module paths express dependency placement; namespaces express semantic
ownership. Handwritten compiler declarations belong to `Itasca.Runtime.Compiler`
and the flat source model to `Itasca.Runtime.SourceMachine`. Machine adapters
use `Interp.Machine`, and joined constructions use `Integration`. For example,
`Store.decodeStore` belongs to `Store` but lives in
[Representation/Store](Representation/Store.lean), below its interpreter and
store-construction consumers.

The source model retains its `astep` transition system. Moving a proof to
`SourceMachine` does not identify compiled code with a unique source program:
`CodeInterpretation` remains explicit, including interpretation changes made by
host publication.

## Compiler stages

The audit enforces Local → Body → Module: Local cannot import Body or Module,
and Body cannot import Module.

- `Compiler/Local/` proves emission, callbacks, lowering, source relations and
  per-operation bounds. Its relation families distinguish emission, layout,
  control, function and operation certificates; control maps and published
  segments have their own subjects.
- `Compiler/Body/` combines reader replay and structured control into body and
  entry certificates. `Relations/` separates checking, replay, stacks, entry,
  calls, control, executable syntax and branch-table contracts. A lemma that
  depends on the body fold belongs here even if it concerns one callback.
- `Compiler/Module/` assembles entry parsing, scheduling, finishing and complete
  modules. The final certificate relates one independently encoded source
  module to its metadata, functions, initializers and frame capacities.

Shared certificates stay below their constructions. In particular,
`Representation` describes source capacities independently of compiler success;
compiler proofs establish these certificates and interpreter proofs consume them.

## Interpreter, execution integration and store

`Interp/Relations/` holds shared frame, slot, argument and store contracts.
`Numeric/`, `Memory/`, `State/`, `Simd/`, `Control/` and `Calls/` prove concrete
runtime operations. `Interp/Machine/` connects these operations to source states:

| Machine subject | What to follow |
| --- | --- |
| `Constants/`, `Local/`, `Global/`, `Select/`, `Simd/` | Instruction fetch and operands through capacity, execution and ownership. |
| `Control/`, `Frames/`, `Calls/` | Branch targets, labels, saved frames, returns and call entry. |
| `Coverage/`, `Emission/`, `Normalization/` | Supported source heads, emitted instructions and administrative steps. |
| `Retention/`, `Mutation/`, `Resources/` | Ownership/code bounds, store footprints and resource failures. |
| `Progress/`, `Simulation/`, `History/` | Machine advance, source correspondence, decreasing measures and finite histories. |
| `Execution`, `Point`, `Functions/` | Shared machine state, program positions and compiled-function certificates. |

`Interp/Invocation/` combines setup, execution loops, readback, recording and
divergence. Other interpreter modules cannot import this final stage.

`Integration/Execution/` assembles the operation proofs while keeping their
premises visible:

| Execution subject | Responsibility |
| --- | --- |
| `Ownership/` | Certified stores, references, frame type bounds and publication. |
| `Mutation/` | Store footprints, metadata retention and the resulting certificates. |
| `Dispatch/` | Instruction-family outcomes, entry, normalization and host-call sites. |
| `History/` | Recorded prefixes and fixed-interpretation execution histories. |
| `World/` | Evolving interpretations, actual recorded steps and loops, and source productivity. |
| `Resources/` | Source demand, boundary causes, invocation errors and resource accounting through loops. |
| `MemoryFill`, `MemoryCopy`, `MemoryInit`, `TableFill`, `TableCopy`, `TableInit` | Complete per-operation effect, source-step and dispatch arguments. |

`Integration/Api/` owns the retained public store certificates;
`Compilation/`, `Invocation/`, `Instantiation/` and `Host/` combine them with
operation and execution proofs. The contract entry point does not import these
constructions merely because it uses `ExecutableInv`.

Store `Invariant/` establishes retained metadata and code properties. `Api/`
proves issued-object operations, `Linking/` resolves imports, `Preparation/`
stages allocations, and `Initialization/` handles initializers and segments.
`Store/Instantiation/` joins these with publication and start-function resolution;
lower store modules cannot import that final stage.

Instantiation rolls back failure before publication. Failure after publication
retains initialization effects. Success reaches the source call of the returned
start function, before its execution. The embedder invokes that function with
`invoke_with`, whose theorem then accounts for its execution and any host effects.
Previously issued keys retain their source interpretation through publication.

## Source store typing

[`ExecutableInv.source_typed`](Integration/Api/ExecutableInv.lean) and
[`CertifiedApiStore.source_typed`](Integration/Api/CertifiedApi.lean) derive the
generated `Store_ok` judgment. Their bridge uses the existing certificates below;
it does not assume store typing or execution correctness as another field.

| Source obligation | Retained evidence and construction |
| --- | --- |
| Global values, memories, tables and reference membership | `Shape` and the object lemmas in [Invariant/Typing](Store/Invariant/Typing.lean). |
| Data and element segments | `SegmentBounds`, reference shape, and the same object-typing lemmas. |
| Wasm bodies and module environments | `CoreFunctionsTyped` retains `Func_ok` under the exact canonical `ModuleBindings`. [SourceMachine/StoreTyping](SourceMachine/StoreTyping.lean) recovers generated module-instance typing. |
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

## Source typing

`Spec/Typing/` proves source configuration typing, value/stack inversion, and
preservation. It is source-only and cannot depend on the extracted runtime.

## Compiler completeness

The compiler uses the same Local → Body → Module stages for soundness and
acceptance. The additional local directories separate the maintained evidence:

| Directory | Responsibility |
| --- | --- |
| `Compiler/Local/Demand/` | Independent source demand and recorded stack/control peaks. |
| `Compiler/Local/Capacity/` | Counter accounting, allocation availability, and accepting callbacks. |
| `Compiler/Local/Coordinates/` | Source offsets, target bounds, and callback coordinate preservation. |
| `Compiler/Local/Publication/` | Open/closed control maps and final published ranges/header. |
| `Compiler/Local/Checking/` | Stored-instruction checks, pending forward branches, and exit-slot bounds. |

`Compiler/Local/Source/` retains the underlying source/compiler relations and typed
source traces. These relations describe the source independently of compiler
success. Shared lemmas belong at the lowest stage their imports permit.

`Compiler/Body/Reader/` groups opcode adapters under `Scalar/`, `Float/`,
`Local/`, `Global/`, `References/`, `Memory/`, `Calls/`, `Control/` and `Simd/`.
`Stateful/` joins table, segment and bulk operation evidence. Branch-table
selection, label/control maps and dormant scopes belong to `Control/`; they
are distinct from Wasm table storage operations.

The call family illustrates the direction of each argument:
[Calls/Instructions](Compiler/Body/Reader/Calls/Instructions.lean) inverts
accepted direct and indirect reader steps,
[Calls/Compilation](Compiler/Body/Reader/Calls/Compilation.lean) relates their
compiler effects, and [Calls/Acceptance](Compiler/Body/Reader/Calls/Acceptance.lean)
constructs successful replay from independent source and allocation premises.
Cross-family composition uses:

| Reader subject | Responsibility |
| --- | --- |
| `Stacks/` | Shared source values and reader/compiler stack relations. |
| `Safety/` | Operation and profile bounds needed for normal return. |
| `Acceptance/` | Successful callback replay from source prefixes and demand. |
| `Checking/` | Instruction-check and exit-slot invariants. |
| `Publication/` | Source coordinates and published control maps. |
| `Replay/` | Callback/profile agreement, reader folds and whole-body preservation. |
| `Source/` | Source opcode families and independent source demand. |

Both profiles use the Wasm 2.0 reader proofs. A valid Wasm 1.0 body has the same
run under both profiles (`code.validate_body_with.wasm1_of_body`).
[Checking/BodyCheckedWasm2](Compiler/Body/Relations/Checking/BodyCheckedWasm2.lean)
constructs actual body success with the checker premises at root close.

[EntryFinishAvailable](Compiler/Module/EntryFinishAvailable.lean) composes entry
parsing, body compilation and actual finishing. Module demand envelopes account
for metadata, functions, initializers, scheduling, collection, output counters
and temporary reserves. [Compilation/Complete](Integration/Compilation/Complete.lean)
constructs successful compilation and the existing certificate for both complete
profiles from independent source validity, conservative source-only
`CompileEligible`, allocator correctness and bounded allocation availability.
It assumes neither compiler success nor a completed callback trace. Uniform
source maxima can exclude modules whose actual output fits exactly at a limit.

## Host composition

The atomic host-call proofs live directly in `Integration/Host/`. They take the
per-host `HostRetention` laws of [Contracts](Contracts.lean) as premises and
never model a particular callback; the world layers above take `HostLaws`.
Callbacks may diverge, so these proofs conclude `DivSpec (HostDiverges hooks
store)` ([Platform/DivSpec](Platform/DivSpec.lean)): each step returns with its
outcome or diverges in a callback called from the current store. [Examples/TrapHost](../Examples/TrapHost.lean) shows the laws
are satisfiable: a trapping callback, continuing interrupts and a granting
allocator discharge every host, interrupt and allocator premise of
`no_spurious_errors`.

## Reading paths

Each path starts with a public statement, follows its construction, then reaches
the foundational certificates. The listed files are the argument's main stops,
not every transitive import.

### Compilation

1. [Results/Compile](../Results/Compile.lean) states soundness, normal return
   and completeness for both profiles.
2. [Compilation/Certificate](Integration/Compilation/Certificate.lean) constructs
   `CompilationCertificate` and `ModuleCodeRel`;
   [Compilation/Complete](Integration/Compilation/Complete.lean) combines the
   certificate with an actual successful compilation.
3. [CompilationAvailable](Compiler/Module/CompilationAvailable.lean) assembles
   module acceptance. [EntryFinishAvailable](Compiler/Module/EntryFinishAvailable.lean)
   joins entry reading, [BodyCheckedWasm2](Compiler/Body/Relations/Checking/BodyCheckedWasm2.lean)
   and finishing.
4. [FunctionCapacity](Representation/FunctionCapacity.lean) and
   [StackLayout](Representation/StackLayout.lean) describe independent source
   demand and slot layout, which the compiler certificate supplies to execution.

### Invocation

1. [Results/Invoke](../Results/Invoke.lean) states `behaves`, `terminates` and
   `no_spurious_errors`; [Contracts](Contracts.lean) lists platform and host laws.
2. [Invocation/Behaves](Integration/Invocation/Behaves.lean) joins recorded
   returns, divergence and exclusion of spurious errors.
   [Resources](Integration/Invocation/Resources.lean) supplies actual returned
   outcomes and resource causes; [Outcomes](Integration/Invocation/Outcomes.lean)
   defines the retained store interpretation and certificates.
3. [Invocation/Recording](Interp/Invocation/Recording.lean) fixes events to
   actual callback arguments and replies. [World/RecordedLoop](Integration/Execution/World/RecordedLoop.lean)
   and [World/Infinite](Integration/Execution/World/Infinite.lean) connect machine
   histories to finite or infinite source execution.
4. [ExecutableInv](Integration/Api/ExecutableInv.lean),
   [Store](Representation/Store.lean) and [StoreCapacity](Representation/StoreCapacity.lean)
   provide the store invariant, decoding and source resource demand.

For one concrete operation, read
[Execution/MemoryFill](Integration/Execution/MemoryFill.lean), then
[Store/Api/MemoryFill](Store/Api/MemoryFill.lean) and
[Spec/MemoryFill](Spec/MemoryFill.lean). These three proof units follow dispatch,
store mutation and source meaning. For scalar execution,
[Constants/IntegerConstant](Interp/Machine/Constants/IntegerConstant.lean)
contains fetch inversion, capacity, the step and ownership preservation in order;
[FloatConstant](Interp/Machine/Constants/FloatConstant.lean) retains the separate
floating-point premises.

### Instantiation

1. [Results/Instantiate](../Results/Instantiate.lean) states totality, rollback,
   the retained invariant, source correspondence and resource causes.
2. [InstantiateSource](Integration/Instantiation/InstantiateSource.lean)
   distinguishes prepublication rejection from published initialization.
   `StartResolved` identifies the returned function; `InitializedSource` stops
   at its source call, before execution.
3. [Precommit](Store/Instantiation/Precommit.lean) combines staging-error origins
   and resource causes. [PreparedSourceInstantiation](Store/Instantiation/PreparedSourceInstantiation.lean)
   constructs source allocation and instantiation;
   [SegmentInitializeSource](Store/Initialization/SegmentInitializeSource.lean)
   supplies initialization steps and traps.
4. [InstantiationCode](Store/Invariant/InstantiationCode.lean) records staged
   type/function tables; [FunctionTables](Store/Invariant/FunctionTables.lean)
   defines `installCode` at the new instance key. [Rollback](Store/Invariant/Rollback.lean)
   preserves the old store before publication. Their common decoding contract
   is [Representation/Store](Representation/Store.lean).

## Naming and extending the proofs

Module paths describe dependency placement; declaration namespaces describe
semantic ownership: `Compiler` for handwritten compiler concepts,
`SourceMachine` for the flat source model, `Interp.Machine` for machine proofs
and `Integration` for joined constructions. Extracted Rust names and SpecTec
names retain their spelling. A decoder can belong to `Store` while living in
`Representation`.

Modules, types, structures, inductives, and named predicates use
`UpperCamelCase`; computations use `lowerCamelCase`, as in `decodeStore`;
theorem basenames use `snake_case`, as in `memory_fill_decodes` and
`step_integer32_core_forward`. Theorem names state their conclusion. Facts
about extracted functions remain under their Rust path, including the public
`runtime.interp.invoke_with.behaves`; Wasm spellings such as `br_if` and
`call_indirect` remain intact. The [proof guide](../../PROOF_GUIDE.md#names-and-proof-units)
gives the complete conventions.

A consolidated module should answer one question: memory-fill effect,
mutation, and decoded source meaning form an argument; integer-constant fetch,
capacity, step preservation, and ownership form another. Keep independently
consumed contracts below their constructions. Start each new or consolidated
module with a docstring explaining that question and its consumers, and use
section comments to mark the argument's stages.

Names such as `Core`, `FloatCore`, `Cumulative`, and `Executable` distinguish
instruction grammars and theorem premises. They are not interchangeable proof
versions. In particular:

| Retained name | Distinction to preserve when reorganizing its proofs |
| --- | --- |
| `CoreHead`, `ScalarHead` | `CoreHead` adds constants, select, globals, and scalar memory operations to the pure transition heads; `ScalarHead` also admits scalar float operations. |
| `SupportedState` | Active frame code, label continuations, and Wasm function bodies satisfy `BinaryInstr`, independently of concrete emission or current values. |
| `FloatCoreTrap` | The scalar trap cases: unreachable, integer division by zero/overflow, memory bounds, and invalid float-to-integer conversion. |
| `CumulativeStoreMutation` | A dispatch mutation retains metadata, externs, shape, segment bounds/counts and limits, with decoded source-store extension. |
| `EventfulTransition` | A fixed code interpretation, the actual dispatch equation, and source simulation labeled by the actual host events. |
| `EventfulWorldTransition` | The interpretation may evolve; previously issued keys retain their meaning through `CodeAgreesOn`. |
| `ExecutableInv` | The public API store certificate together with segment accounting and function-capacity certificates; host freedom is not a field. |

Every module is reachable from [Main](../Main.lean) or `Examples/`;
`just prove` runs `just dead --check`, which rejects unused modules outside
the short allowlist in [`scripts/reachability.lean`](../../scripts/reachability.lean).

Shared slice lookup and list transport lemmas live in
[Representation/Collection.lean](Representation/Collection.lean).
Keep shared helpers at the lowest layer supported by their actual dependencies.

Run `just check Itasca.Runtime.Store.Api.MemoryFill` while iterating, `just audit-imports`
after file moves, and `just prove` for integration. Rust changes
also require both Cargo test configurations and extraction/regeneration checks,
as specified in [DEVELOPMENT.md](../../../DEVELOPMENT.md). Preserve build caches.
