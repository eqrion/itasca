# Execution proof constructions

Start with the [definition reading map](../Results/Definitions/README.md) and
[public audit guide](../Results/README.md) to determine each statement's meaning.
This guide follows the implementation proofs that construct those guarantees.
Public vocabulary belongs to Interface; these proofs never become an additional
premise merely because they share a namespace with a definition.

## Dependency layers

| Area | Responsibility |
| --- | --- |
| [Spec](Spec/README.md) | Source typing, numeric operations, memory and segment algebra over the pinned rules. |
| [SourceMachine](SourceMachine/README.md) | Flat source transitions, invariants, simulation and progress. |
| [Equations](Equations/README.md) | Equations over extracted runtime functions. |
| [Platform](Platform/README.md) | Law preservation, recording erasure and satisfiable example implementations. |
| [Representation](Representation/README.md) | Concrete/source value, slot, store and capacity correspondence. |
| [Compiler](Compiler/README.md) | Local emission, body traversal and complete-module constructions. |
| [Interp](Interp/README.md) | Operation effects, machine simulation and invocation. |
| [Store](Store/README.md) | API effects, linking, preparation, initialization and publication. |
| [Integration](Integration/README.md) | Joined compilation, store, invocation and instantiation guarantees. |

The extracted program and independent source semantics are named foundations.
[SpecExt](../../SpecExt/README.md) supplies host-aware source reduction independently
of extracted runtime code. Public definitions may use these foundations and
remain independent of handwritten implementation modules. Compiler Local → Body
→ Module stages apply to definitions and proofs. Compiler declarations stay
independent of interpreter operations, and validator declarations stay independent
of runtime operations, runtime implementation proofs and SpecExt.

## Compiler stages

[Local](Compiler/Local/README.md) establishes individual callback/lowering effects,
source relations, resource bounds, instruction checks and publication coordinates.
[Body](Compiler/Body/README.md) composes reader replay and structured source control
into function and initializer certificates. [Module](Compiler/Module/README.md)
assembles environment parsing, entries, scheduling, finishing and collection.

Read [Results/Compile](../Results/Compile.lean), then
[Compilation/Complete](Integration/Compilation.lean).
[CompilationAvailable](Compiler/Module/BatchLoopAvailable.lean) constructs
acceptance from independent source validity and demand;
[BatchLoopAvailable](Compiler/Module/BatchLoopAvailable.lean) joins entry reading,
[BodyChecked](Compiler/Body/Relations/Checking/BodyChecked.lean) and finishing.
[ExecutableFunctionCapacity](Compiler/Body/ExecutableFunctionCapacity.lean)
constructs the source-frame capacities retained by the result.

Reader proofs share exact source-prefix certificates with validation in
[Body/Scalar/IndexReader](../Body/Scalar/Readers.lean). Preservation projects
Pending.After; compiler inversion retains the decoded operands, callback state
and source frame. Reader families separate scalar, float, local/global, memory,
reference, SIMD, stateful, control and call cases. For a representative family,
[Calls/Instructions](Compiler/Body/Reader/Calls/Instructions.lean) inverts the reader,
[Calls/Safety](Compiler/Body/Reader/Calls/Safety.lean) establishes its compiler bounds,
and [Calls/Acceptance](Compiler/Body/Reader/Calls/Acceptance.lean) constructs replay.
[AcceptedTable](../Body/Visitor/ReachedTableLoop.lean) retains repeated label callbacks
and the distinct final branch-table callback, including a rejected partial table.

Completeness constructs an actual compiler run and the syntactic certificate;
it assumes neither a successful compiler trace nor execution correctness.
Source maxima and numerical demand remain conservative: eligibility can exclude
an input whose actual output happens to fit at a configured limit.

## Interpreter execution, integration and store

Operation proofs connect concrete words, frames and store effects to independent
source transitions. Interp.Machine joins them into the active/suspended frame
relation. SourceMachine.decode reconstructs specification evaluation contexts;
the [cumulative source transition](SourceMachine/TransitionAndHostPreparation.lean) simulates
the host-aware source reduction SpecExt.StepsH.

For invocation, read [Results/Invoke](../Results/Invoke.lean), then
[Invocation/Behaves](Integration/Invocation/Behaves.lean).
[Callback observations](../Results/Definitions/Host.lean) match actual
embedding exchanges to source events. Internal [recording definitions](Interp/Recording.lean)
and [observation correspondence](Interp/Invocation/Recording.lean) connect
the simulation's event writer to the actual extracted invocation.
[World/RecordedLoop](Integration/Execution/World/NonhostStep.lean) and
[World/NonhostStep](Integration/Execution/World/NonhostStep.lean) connect the recorded
machine history to finite or infinite source execution. Evolving code worlds
retain source interpretations for every previously issued instance key while
allowing callbacks to publish new modules.

Keep distinct the concrete dispatch, source simulation, exact event recording,
store extension and reached resource cause. Internal theorems retain all of them; the public contract projects source
outcomes, actual host observations, preservation and divergence. Fixed-code and event-erased intermediate lemmas alone do not provide that
guarantee. Resource adequacy ranges over all relevant source runs and typed host
replies; a single terminating source run cannot establish termination.

A concrete operation can be followed through
[Execution/MemoryOperations](Integration/Execution/MemoryOperations.lean),
[Api/MemoryCopyAndFill](Store/Api/BulkCopiesAndFill.lean) and
[Spec/BulkOperations](Spec/BulkOperations.lean): dispatch, concrete mutation and
source meaning. [IntegerConstant](Interp/Machine/Constants/EncodingAndFloat.lean)
contains the scalar fetch/capacity/execution/ownership argument;
[EncodingAndFloat](Interp/Machine/Constants/EncodingAndFloat.lean) retains the
separate floating-point premises.

Store Invariant establishes metadata, ownership and code properties. Api proves
issued-object operations, Linking resolves imports, Preparation stages objects,
and Initialization runs initializers and segment programs. Instantiation joins
those stages. Lower store modules cannot import final instantiation; lower
interpreter modules cannot import final invocation.

## Source store typing

[ExecutableInv.source_typed and CertifiedApiStore.source_typed](Integration/Api/CreationAndGrowth.lean)
derive the generated Store_ok judgment from retained certificates. Source store
typing and execution correctness are not additional invariant fields.

| Source obligation | Evidence and construction |
| --- | --- |
| Globals, memories, tables and references | Shape and object lemmas in [Invariant/Typing](Store/Invariant/Typing.lean). |
| Data and element segments | SegmentBounds, reference shape and those same object lemmas. |
| Wasm functions and environments | CoreFunctionsTyped under the exact ModuleBindings; [EntryAndBranchTables](SourceMachine/EntryAndBranchTables.lean) recovers module-instance typing. |
| Exports | ExportBounds retains descriptor bounds and decoded-name uniqueness; instance maps resolve each export in its own namespace. |
| Host functions | The generated host rule types signatures without Wasm bodies; the decoder supplies a well-formed empty module environment. |

[OwnedInitializerErrors](Store/Invariant/CoreInstantiationSource.lean) assembles the
object facts. Atomic host return and trap require a source-typed post-call store;
Platform.HostSound.of_invariant derives that obligation from retained certificates.
Raw metadata retention remains a separate host obligation.

## Instantiation and host composition

Read [Results/Instantiate](../Results/Instantiate.lean), then
[InstantiateSource](Integration/Instantiation/InstantiateSource.lean).
[Precommit](Store/Instantiation/NoStart.lean) joins staged-error origins and
resource causes; [NoStart](Store/Instantiation/NoStart.lean) constructs source
allocation and instantiation. [InitializerResourceCauses](Store/Initialization/InitializerResourceCauses.lean)
accounts for segment setup, effects and traps.

Before publication, failure rolls back the old store. After publication, segment
traps retain completed writes and allocations. Success returns the resolved start
handle, stopping before its execution. Instantiation invokes neither host callbacks
nor the start function; a separate invoke_with call accounts for that execution.

Atomic [host proofs](Integration/Host) consume HostRetention from
[HostContracts](../Results/Definitions/Runtime.lean); world proofs consume
HostLaws. Returning or diverging callbacks remain distinct. Native identity
issuance, allocation, memory and floating-point wrappers retain the explicit
[trust boundary](../../../README.md#trust-boundary). Example implementations show
premises are satisfiable; they do not discharge them for arbitrary embeddings.

## Abstract runtime protocol

[RuntimeContract](Integration/RuntimeContract.lean) constructs the public protocol
from the internal executable invariant. The existence theorem in
[Results/Store](../Results/Store.lean) exports `∃ Inv, RuntimeContract view Inv`.
Its semantic fields cover fresh stores, definitions, reads, writes, instantiation,
invocation and divergence. Resource causes remain in the implementation proofs. The client chooses a single predicate
and uses these laws to preserve it, including in host callbacks. The witness's
implementation is not part of the public statement vocabulary.

The [private definitions](Integration/Definitions.lean) retain the old executable
invariant for the simulation proof. Local emission, completed function and module
certificates live in the corresponding compiler `Definitions` modules. Private
representation shape and capacities live in
[Representation/Definitions](Representation/Definitions.lean). These are proof
construction tools; moving them is justified by the changed public statements.

The one-call and fixed-platform behavioral experiments have been replaced by this
protocol. The verified protocol quantifies platform dictionaries at each operation,
preserves stores across external API mutations and instantiation, and retains the
invocation source behavior and divergence guarantees. The same final code
interpretation explains both the source outcome and the retained predicate.

[Runtime examples](../Examples/Runtime.lean) choose the existential predicate and
compose fresh-store creation, host definition and invocation, and compilation
with instantiation. Their client proofs do not name the internal executable
invariant. Host soundness uses the protocol's explicit source typing and
well-formedness fields; native/platform laws remain separate obligations.

## Naming and iteration

Module paths identify dependency owners; namespaces identify semantic subjects.
Core, Scalar, Cumulative, Supported and Executable denote the actual relations
and premises documented at their definitions, not versions of a proof effort.
The scalar decomposition is internal and no runtime profile is modeled.

Follow the [proof engineering guide](../../PROOF_ENGINEERING.md) for naming,
contracts and validation. Iterate with the language server or a targeted command,
for example `just check Itasca.Runtime.Store.Api.MemoryCopyAndFill`. Bundle source
changes before integration, preserve caches, and run `just audit` at the
completed checkpoint.
