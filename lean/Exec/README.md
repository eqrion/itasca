# Execution proofs

Start with the [public theorem map](../../docs/EXECUTION_VERIFICATION.md#public-theorem-map)
for guarantees and premises. This guide explains how the proofs are assembled.
The [Lean guide](../README.md) covers tool setup and the independent validator.

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
