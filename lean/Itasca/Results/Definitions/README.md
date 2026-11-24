# The public proof interface

This directory contains the complete handwritten vocabulary needed to understand the
[public Results](../README.md), above the named foundations listed below.
It is organized into **19 semantic reading units**. Implementation proofs build
these certificates and establish their properties elsewhere; moving a definition
out of this directory is not a way to hide an assumption.

Start with the relevant result, read its premises and conclusion, then follow the
referenced definitions, including their bodies and the types of fields and constructors.
A short theorem can describe a substantial contract: the referenced vocabulary
is part of what must be understood.

## Choose a reading path

Start with the theorem for the guarantee you need. Follow its definition files;
implementation proofs are not prerequisites for understanding the statement.

| Guarantee | Definition reading path |
| --- | --- |
| Validation, uniqueness | Foundations → Binary → Validation |
| Callback traces | Visitor → Observations → Validation |
| Streaming and worker batches | Validation → Streaming |
| Compilation | Compiler/Compilation → Compiler/Source and Validation |
| Store operations | Representation → Store/State → Store/Read or Store/Mutation |
| Instantiation | Store/State → Compiler/Source → Instantiation |
| Invocation | Store/State → Host → SourceMachine → Invocation |
| Invocation resource completeness | Invocation → Resources |
| Runtime composition | Runtime → the relevant operation laws and Platform |

For runtime use, obtain `∃ Inv, RuntimeContract view Inv` once, then use the same
predicate for operations and host callbacks. [Runtime](Runtime.lean) lists the
capabilities; it contains no additional execution assumptions.

## Definition owners

| File | Meaning |
| --- | --- |
| [Foundations](Foundations.lean) | Shared source translations and Rust-result postconditions. |
| [Binary](Binary.lean) | Independent encoding, opcode tables and module framing. |
| [Visitor](Visitor.lean) | Validation callbacks, acceptance, normal return and recording. |
| [Observations](Observations.lean) | Instruction and byte meaning of validation callbacks. |
| [Validation](Validation.lean) | Body validity, module elaboration, limits and returned metadata. |
| [Streaming](Streaming.lean) | Coherent regions, issued workers and scheduler contracts. |
| [Platform](Platform.lean) | Embedding laws for memory, allocation, floats and interrupts. |
| [Representation](Representation.lean) | Decoding runtime values, instances and stores. |
| [Compiler/Source](Compiler/Source.lean) | Source function bodies installed by instantiation. |
| [Compiler/Compilation](Compiler/Compilation.lean) | Compilation validity, budgets and source association. |
| [Store/State](Store/State.lean) | Issued objects, identity retention and decoded store effects. |
| [Store/Read](Store/Read.lean) | Read and export-lookup operation laws. |
| [Store/Mutation](Store/Mutation.lean) | Construction, write and growth operation laws. |
| [Host](Host.lean) | Callback observations, return obligations and reachable divergence. |
| [SourceMachine](SourceMachine.lean) | Finite and infinite SpecTec reductions with host events. |
| [Instantiation](Instantiation.lean) | Linking, publication, initialization and start handles. |
| [Invocation](Invocation.lean) | Returned outcomes, divergence and resource-completeness laws. |
| [Resources](Resources.lean) | Conservative source storage and call-depth budgets. |
| [Runtime](Runtime.lean) | Capability bundles over one shared store predicate. |

Names describe semantic subjects; organizational directories add no namespace
prefixes. See the [namespace policy](../../../NAMESPACES.md). `MetadataPreserved`
means the store identity and function/type/instance tables are unchanged;
`MetadataExtended` permits appended entries while preserving existing ones.

Public definitions import only other public definitions and named foundations.
Compiler source interpretation remains below compilation eligibility and excludes
the extracted interpreter. Validator, streaming and callback vocabulary excludes
runtime execution and SpecExt. Only Main, examples and external consumers use the
full `Itasca.Results.Definitions` umbrella. Import checks enforce these boundaries.

## Meaning, rather than proof machinery

Intermediate parser records, framing witnesses, compiler layout calculations and
SIMD typing helpers belong to their implementation proof modules. Their names
remain available there, but importing public definitions alone does not expose them.
Mutually recursive source definitions remain together even when Lean reaches one
branch through a generated helper rather than its original declaration name.

Binary decoding maps scalar and SIMD opcodes directly to SpecTec instructions.
It does not require a typed operation certificate to say what bytes mean.
Implementation classifiers and their typing proofs live in Binary. Checked
correspondence lemmas connect those proof tools to the independent tables.
The tables remain handwritten because the pinned SpecTec-to-Lean translation
does not yet translate SpecTec's binary grammar.

Callback normal return and acceptance quantify over the event vocabulary once.
Every callback input is included, even if a particular run never reaches it.
Hook-specific facts are derived in implementation proofs. `Total` permits ordinary
visitor rejection; `Accepts` excludes rejection as well as modeled divergence and
panic. Exact callback recording concerns returning computations, including a final
rejecting callback. Function offsets are relative to the issued batch; operator
positions are relative to the instruction body. The public statements take an
arbitrary observation function satisfying `Records`. Event-to-callback dispatch
remains public because it defines that obligation; the reverse adapter, logging
wrapper and concrete recorder are implementation conveniences in Visitor.

Runtime clients obtain `∃ Inv, RuntimeContract view Inv` from the checked
`Integration.runtime_verified` theorem. They choose that predicate once and keep
it for the lifetime of the store. The contract combines separate read, mutation, instantiation and invocation
capabilities over that one predicate; its existence is proved,
not an embedding assumption. `HostLaws` uses one returned-callback postcondition, `HostReturn`. It preserves
the chosen predicate and existing code meanings, requires a typed source-store
extension, retains the store identity and old function/type/instance entries,
and keeps old external references and returned values issued. Source extension
and concrete identity retention are distinct obligations within that one
postcondition. They apply to ordinary host errors as well as successful replies.
Callbacks may diverge; callback termination and resource availability remain
separate premises.

Invocation uses the actual extracted `invoke_with` with `Platform.observing`.
The wrapper forwards callbacks and records their actual arguments, host identity,
before/after stores and raw replies. `HostObservation.Matches` relates that log,
in order, to the events of the source execution. A successful host reply may still
be rejected for the wrong arity, value types or reference ownership; the relation
accounts for that rejection as well as explicit host traps.

Source execution supplies Wasm function addresses. The observation supplies the
embedding's host identity, so aliases of the same host identity are intentionally
indistinguishable at this boundary. The public statement does not select bytecode
call sites or recover callback arguments from interpreter scratch buffers. The
old recorder remains an internal simulation tool, with a checked correspondence
to the platform observations. Erasing observations recovers the original
computation, including its failures and divergence.

`CompilationSource` gives the independently encoded, typed source and matching
public metadata. Actual compilation acceptance connects the returned module to
the protocol's instantiation law. That law preserves the predicate needed for
invocation, so no emission certificate is exposed to clients. `StoreMutation`
retains observable source extension, ownership metadata and limits without
requiring callers to inspect the internal representation shape.

Store reads expose decoded globals, references, bytes and function signatures.
Writes identify the exact source object that changes and preserve every other
source object. Memory and table growth use SpecTec's `fun_growmemory` and
`fun_growtable` judgments, return the original size, and bound the resulting
source byte/reference totals by the configured quota. Refused growth preserves
the decoded store; opaque memory buffers may change representation without
changing their bytes. Raw word encodings, vector updates and staging certificates
are private construction evidence.

Export lookup matches exact name bytes and returns an owned handle with the
corresponding source export address. Exact bytes are necessary even though
source export names are decoded: an arbitrary malformed query can lose bytes
when decoded. The contract does not describe the search loop.

`InvocationOutcome` first states preservation and source reachability shared by
all returned cases, then matches the actual result. Success reaches returned
source values; input errors leave all API state unchanged and emit no host events;
traps reach a source trap; exhaustion and interruption retain the reached store.
Link and internal errors are excluded. The trap case does not identify the
concrete trap reason. `InvocationBehavior` separately accounts for divergence
and matches actual callback observations to the source events. These contracts
do not specify a private reservation order or interpreter frame layout. The separate
`resource_complete` law excludes resource errors and interruption under
`Spec.Resources.Fits` and `Integration.ResourceAvailability`. Detailed capacity
and refusal witnesses remain internal. Compiler completeness retains its explicit,
conservative numerical eligibility conditions.

Compiler completeness uses `compilationBudget bytes.length raw`, computed from
an independently decoded module. It gives one requirement per configured limit
and one allocation allowance. `CompileEligible` compares those requirements to
the configuration and checks the intrinsic 32-bit frame and machine-sized
reservation bounds. The allocator must grant requests up to the computed
allocation allowance; callers choose no auxiliary maxima or metadata witnesses.

The estimates remain conservative: each defined body is charged the smaller of
the module byte length and the body-size cap; local preparation allows the largest
parameter list in the source type table plus the supported declared-local cap;
operands allow 500 values per body byte. An empty function section has zero
body/local/operand demand. Initializer charges are unchanged. The allocation
allowance uses the maximum of the table, preparation, initializer and fixed small
requirements; imported-function storage is conservatively bounded by all imports.
These bounds are sufficient, not measurements of actual output or stack peaks.

The internal adapter derives metadata-cache, signature-width, segment-length and
reservation obligations. Those detailed demand records live in Runtime/Compiler
and do not enter the public premise. Source validity and resource eligibility
remain separate conditions.

## Interpreter resource completeness

[Resources](Resources.lean) supplies one conservative source model. Choose a callee
allowance covering every function signature and independently encoded body in the
initial and reachable stores. Every reachable SpecTec configuration must leave that
allowance beyond its source storage charge and stay below the configured frame
limit. The charge includes two words per local and per ordinary administrative
instruction/value; label and frame contents are traversed recursively. It ignores
inactive label continuations. Defined-function allowances use two words per
parameter/local plus 1000 words per instruction-body byte. These are sufficient
bounds, not predicted allocation sizes or exact operand-stack peaks.

The conditions quantify over all source runs, including permitted host replies
and store extensions. They are deliberately stronger than a bound for one chosen
execution. In particular, a uniform allowance is not available when the source
semantics permits unbounded publication of new code by hosts.

`ResourceAvailability` separately requires grants for every representable vector
reservation, continuing interrupts, callbacks that retain the configured limits,
and no callback-reported stack exhaustion. Together with owned, source-typed
arguments, these premises exclude every interpreter error except a source trap.
Divergence remains possible; combine `resource_complete` with `terminates` when
all source runs and reachable callbacks terminate. No resource completeness is
claimed for instantiation by this invocation law.

## Read the premises precisely

Soundness, normal return and completeness have different obligations. Streaming
soundness requires coherent source views and reachable issued workers. Normal
return requires total callbacks. Completeness additionally needs accepting
callbacks, canonical regions, within-limit inputs and the stated scheduler
availability. `Source.Describes` ties the source regions to one module byte string without
requiring a canonical split for soundness. `Scheduler.Provenance` tracks issued
history and permits only actual worker operations for matching identities.
`Scheduler.Accepts` instead tracks outstanding work: accept bounded submissions,
return their actual `validate_all` results in any order, and preserve the queue
across other callbacks. It assumes neither valid batch encodings nor successful
worker finishing; the completeness proof derives those facts from module validity.
The synchronous adapter satisfies this contract even for invalid work. The embedding retains storage lifetimes and Rust
ownership duties.

Instantiation returns a start handle without executing it. Failure before
publication rolls back; segment traps can retain already committed writes and
allocated objects. Invocation relates the actual host log and evolving store to
source behavior. It may diverge, including through a diverging host call. Resource exhaustion and interruption are ordinary runtime outcomes unless the
separate resource-completeness premises hold.

## Foundations and audit

The named foundations are:

- The extracted [Types](../../Generated/Types.lean),
  [FunsValidator](../../Generated/FunsValidator.lean), and narrow runtime partitions
  `FunsRuntimeCommon`, `FunsCompiler`, `FunsStore`, `FunsInterp`, `FunsInstantiate`.
- The handwritten trusted [FunsExternal model](../../Generated/FunsExternal.lean).
- Generated [SpecTec judgments](../../../SpecTec/wasm2.0.lean), the pinned builtin
  patches and SpecTecSupport.
- The [SpecExt host/source extension](../../../SpecExt/Host.lean) and its support.
- Lean, Aeneas and their pinned upstream libraries.

The [public trust boundary](../../../../README.md#formal-verification) distinguishes
these foundations from checked construction proofs. Native identity issuance,
allocation, memory and floating-point wrappers are not proved to satisfy the
generic platform laws. Host callbacks retain their own obligations. The Lean
execution model is sequential; worker provenance and concurrent Rust use remain
part of the embedding contract.

`just audit` checks every registered result, allowed axioms, semantic ownership
and generated audit artifacts. It checks artifacts without rewriting them;
`just audit --update` explicitly refreshes them. `just lint` checks import isolation,
links and proof-health metrics. The migration manifest retains definition provenance separately from the
reader-facing layout. File moves do not count as removing proof obligations.

For construction proofs, see the [Lean guide](../../../README.md#proof-architecture)
and [runtime guide](../../Runtime/README.md). Those proofs are required for verification
but their proof bodies are not part of interpreting a public theorem statement.
