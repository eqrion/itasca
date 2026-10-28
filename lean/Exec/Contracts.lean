import Exec.Platform.Laws
import Exec.Store.Api.Grow
import Exec.Store.Invariant.IssuedArguments
import Exec.Interp.Relations.FrameStorePrefix
import Exec.Theorems.Api.ExecutableInv

/-!
# Embedding contracts

The obligations that the execution headline theorems in `Exec/Results/` place on an embedding.
Every premise of a headline theorem is either a fact about the inputs (an accepted compilation, an
issued handle, a source invocation) or one of the contracts below. None of them assumes that the
runtime succeeds, terminates or agrees with the source semantics.

This file holds definitions only. `HostLaws` and the host contracts live here; the platform,
compiler and source-resource contracts stay with their constructions. All are listed here.

## Platform operations

[`Platform.Laws`](Platform/Laws.lean) bundles the float, allocator, interrupt and memory laws.

| Contract | Obligation |
| --- | --- |
| [`Platform.AllocCorrect`](Platform/Alloc.lean) | `reserve` returns normally and preserves vector contents; it may refuse. |
| [`Platform.AllocationAvailable`](Platform/Alloc.lean) | `reserve` succeeds for every request within a fixed bound. `no_spurious_errors` only. |
| [`Platform.FloatOpsCorrect`](Platform/Float.lean) | The 27 rounding operations return a value the source semantics permits, NaN sets included. |
| [`Platform.MemoryLaws`](Platform/Memory.lean) | The memory buffer reads, writes, allocates and grows exactly the bytes `view` decodes. |
| interrupts, `∀ p, hooks.interrupt p ⦃ _ => True ⦄` | The interrupt hook returns normally. `no_spurious_errors` also requires it never to answer `.Terminate`. |

## Host callbacks

A host callback may publish fresh code. Each call receives the current ghost code
interpretation and chooses the next one, agreeing on previously issued keys. `HostLaws` bundles
`HostWorldSound` with `HostRetention`, the frame, extern and issued-result laws below.

| Contract | Obligation |
| --- | --- |
| `HostWorldSound` | Each call returns normally, preserves the invariant, extends the decoded source store and leaves it typed (`Store_ok`). |
| frame retention, [`Interp.FrameStorePrefix`](Interp/Relations/FrameStorePrefix.lean) | A call keeps the raw store identity and the existing function, type and instance entries. |
| extern retention | A call never shrinks `store.externs`. |
| issued results, [`Store.IssuedValue`](Store/Invariant/IssuedValues.lean) | Every value a call returns is issued by the post-call store. |
| limit retention | A call keeps `store.limits`. `no_spurious_errors` only. |
| `NoHostStackOverflow` | No call reports stack exhaustion. `no_spurious_errors` only. |

The raw retention laws are separate premises: they do not follow from decoded source-store
extension.

## Compiler

| Contract | Obligation |
| --- | --- |
| [`Code.ValidCompilationSource`](Code/Module/CompilationAvailable.lean) | The bytes independently encode a valid, elaborated, profile-restricted module within the binary and signature limits. |
| [`Code.CompileEligible`](Code/Module/CompilationAvailable.lean) | Source-only size and demand bounds fit the configured limits and the allocation bound. |

## Source resources

`no_spurious_errors` assumes the source program itself stays within the store limits.

| Contract | Obligation |
| --- | --- |
| [`SourceResourcesFit`](Theorems/Invocation/SourceResources.lean) | Every source run of the invocation, over all typed host replies, fits the value and frame limits. |
| [`Interp.SourceCanonicalFunctionCapacity`](Interp/Relations/SourceCanonicalCapacity.lean) | The canonical slot demand of a source function, used by `SourceResourcesFit`. |

## Store state

The invariant `ExecutableInv` (in `Theorems/Api/`) is established by instantiation and preserved
by every result; it is a certificate, not an embedder obligation.
Handles and arguments must be issued by the store: [`Store.ExternalIssued`](Store/Linking/LinkEffects.lean),
[`Store.IssuedValue`](Store/Invariant/IssuedValues.lean) and
[`Store.ValueInStore`](Store/Invariant/ValueShape.lean).
-/

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- The callback contract carries its current ghost interpretation explicitly.
Its returned interpretation agrees on previously issued keys; fresh keys are
chosen by publication. Raw metadata retention remains a separate hypothesis. -/
def HostWorldSound {M P : Type} (hooks : runtime.platform.Platform P M)
    (view : M → Slice U8) (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ code store, Inv code store → ∀ platform host args results,
    hooks.call_host platform store host args results ⦃ answer => ∃ afterCode,
      Store.CodeAgreesOn store code afterCode ∧ Inv afterCode answer.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode answer.2.2.1) ∧
        Store_ok (Store.decodeStore view afterCode answer.2.2.1) ⦄

/-- Raw retention by every call of `host` from `store`. These laws do not follow from decoded
source-store extension. -/
structure HostRetention {M P : Type} (hooks : runtime.platform.Platform P M)
    (store : runtime.store.Store M) (host : U64) : Prop where
  framePrefix : ∀ p args results answer,
    hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1
  externs : ∀ p args results answer,
    hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length
  issued : ∀ p args results answer,
    hooks.call_host p store host args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value

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

end Exec.Theorems
