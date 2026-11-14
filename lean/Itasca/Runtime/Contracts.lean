import Itasca.Runtime.Platform.Laws
import Itasca.Runtime.Store.Api.DefineTable
import Itasca.Runtime.Store.Invariant.HostSignature
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Integration.Api.InvocationEntryResources

/-!
# Embedding contracts

The obligations that the runtime headline theorems in `Itasca/Results/` place on an embedding.
Every premise of a headline theorem is either a fact about the inputs (an accepted compilation, an
issued handle, a source invocation) or one of the contracts below. None of them assumes that the
runtime succeeds, terminates or agrees with the source semantics.

This file holds definitions only. `HostLaws` and the host contracts live here; the platform,
compiler and source-resource contracts stay with their constructions. All are listed here.

## Platform operations

[`Platform.Laws`](Platform/Laws.lean) bundles the float, allocator, interrupt and memory laws.

| Contract | Obligation |
| --- | --- |
| [`Platform.AllocCorrect`](Platform/Laws.lean) | `reserve` returns normally and preserves vector contents; it may refuse. |
| [`Platform.AllocationAvailable`](Platform/Laws.lean) | `reserve` succeeds for every request within a fixed bound. `no_spurious_errors` only. |
| [`Platform.FloatOpsCorrect`](Platform/Laws.lean) | The 27 rounding operations return a value the source semantics permits, NaN sets included. |
| [`Platform.MemoryLaws`](Platform/Laws.lean) | The memory buffer reads, writes, allocates and grows exactly the bytes `view` decodes. |
| interrupts, `∀ p, hooks.interrupt p ⦃ _ => True ⦄` | The interrupt hook returns normally. `no_spurious_errors` also requires it never to answer `.Terminate`. |

## Host callbacks

A host callback may publish fresh code. Each call receives the current ghost code
interpretation and chooses the next one, agreeing on previously issued keys. `HostLaws` bundles
`HostWorldSound` with `HostRetention`, the frame, extern and issued-result laws below.

| Contract | Obligation |
| --- | --- |
| `HostWorldSound` | Each call that returns preserves the invariant, extends the decoded source store and leaves it typed (`Store_ok`). |
| frame retention, [`Interp.FrameStorePrefix`](Interp/Relations/StackPreservation.lean) | A call keeps the raw store identity and the existing function, type and instance entries. |
| extern retention | A call never shrinks `store.externs`. |
| issued results, [`Store.IssuedValue`](Store/Invariant/HostSignature.lean) | Every value a call returns is issued by the post-call store. |
| limit retention | A call keeps `store.limits`. `no_spurious_errors` only. |
| `NoHostStackOverflow` | No call reports stack exhaustion. `no_spurious_errors` only. |

The raw retention laws are separate premises: they do not follow from decoded source-store
extension.

## Compiler

| Contract | Obligation |
| --- | --- |
| [`Compiler.ValidCompilationSource`](Compiler/Module/CompilationAvailable.lean) | The bytes independently encode a valid, elaborated, profile-restricted module within the binary and signature limits. |
| [`Compiler.CompileEligible`](Compiler/Module/CompilationAvailable.lean) | Source-only size and demand bounds fit the configured limits and the allocation bound. |

## Source resources

`no_spurious_errors` assumes the source program itself stays within the store limits.

| Contract | Obligation |
| --- | --- |
| [`SourceResourcesFit`](Integration/Invocation/SourceDemand.lean) | Every source run of the invocation, over all typed host replies, fits the value and frame limits. |
| [`Interp.SourceCanonicalFunctionCapacity`](Interp/Relations/ArgumentRejectionKind.lean) | The canonical slot demand of a source function, used by `SourceResourcesFit`. |

## Store state

[`Results/Store`](../Results/Store.lean) states the generic store API guarantees.
`with_identity` establishes `ExecutableInv` (in `Integration/Api/`) when its
identity is positive. Mutating operations preserve that invariant under their
individual premises; instantiation and invocation preserve it under their
existing premises. Read contracts relate results to decoded objects or raw store
values. Allocation-backed definitions and table growth require
`Platform.AllocCorrect`. Memory definition, access, writeback and growth require
`Platform.MemoryLaws`; `memory_mut` additionally requires same-length write-back.
Operations that take handles or values require the stated issued-handle and
issued-value premises. Value-type checks reject incompatible inputs without
changing the store.

These are contracts for the generic extracted operations. They do not prove
that the native identity counter, allocator, memory buffer or floating-point
wrapper satisfies its contract. An embedding may establish `HostWorldSound` for
its callbacks by composing the store API theorems when the callback behavior
meets their premises. This does not establish `HostWorldSound` for arbitrary
callbacks, and [`HostRetention`](#host-callbacks) remains a separate obligation.
The relevant handle and value predicates are [`Store.ExternalIssued`](Store/Linking/LinkedOwners.lean),
[`Store.IssuedValue`](Store/Invariant/HostSignature.lean) and
[`Store.ValueInStore`](Store/Invariant/Typing.lean).
-/

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt

/-- The callback contract carries its current ghost interpretation explicitly. A call may
diverge; when it returns, its interpretation agrees on previously issued keys and fresh keys are
chosen by publication. Raw metadata retention remains a separate hypothesis. -/
def HostWorldSound {M P : Type} (hooks : runtime.platform.Platform P M)
    (view : M → Slice U8) (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ code store, Inv code store → ∀ platform host args results,
    hooks.call_host platform store host args results ⦃ (result, nextPlatform, after, returned) => ∃ afterCode,
      Store.CodeAgreesOn store code afterCode ∧ Inv afterCode after ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode after) ∧
        Store_ok (Store.decodeStore view afterCode after) ⦄div

/-- Some callback diverges when called on `store`. -/
def HostDiverges {M P : Type} (hooks : runtime.platform.Platform P M) (store : runtime.store.Store M) : Prop :=
  ∃ platform host args results, hooks.call_host platform store host args results = .div

/-- Raw retention by every call of `host` from `store`. These laws do not follow from decoded
source-store extension. -/
structure HostRetention {M P : Type} (hooks : runtime.platform.Platform P M)
    (store : runtime.store.Store M) (host : U64) : Prop where
  framePrefix : ∀ p args results result nextPlatform after returned,
    hooks.call_host p store host args results = .ok (result, nextPlatform, after, returned) → Interp.FrameStorePrefix store after
  externs : ∀ p args results result nextPlatform after returned,
    hooks.call_host p store host args results = .ok (result, nextPlatform, after, returned) → store.externs.length ≤ after.externs.length
  issued : ∀ p args results result nextPlatform after returned,
    hooks.call_host p store host args results = .ok (result, nextPlatform, after, returned) →
      ∀ value ∈ returned.val, Store.IssuedValue after value

/-- The callback laws over stores satisfying `Inv`. -/
structure HostLaws {M P : Type} (hooks : runtime.platform.Platform P M) (view : M → Slice U8)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop) : Prop where
  sound : HostWorldSound hooks view Inv
  retains : ∀ code store, Inv code store → ∀ host, HostRetention hooks store host

/-- Explicitly rule out callback-reported stack exhaustion. Normal host traps
and invalid dynamically checked results remain source trap outcomes. -/
def NoHostStackOverflow {M P : Type} (hooks : runtime.platform.Platform P M)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ code store,Inv code store → ∀ p identity args defaults nextPlatform after returned,
    hooks.call_host p store identity args defaults≠.ok (.Err .StackOverflow,nextPlatform,after,returned)

end Itasca.Runtime.Integration
