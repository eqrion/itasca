import Exec.Platform.Float
import Exec.Platform.Memory
import Exec.Spec.Choices.Steps
import Exec.Store.Api.Grow
import Exec.Store.Invariant.IssuedArguments
import Exec.Interp.Relations.FrameStorePrefix
import Exec.Theorems.Api.ExecutableInv
import Exec.Theorems.Host.Chosen.HostChoiceMatching

/-!
# Embedding contracts

The obligations that the execution headline theorems in `Exec/Results/` place on an embedding.
Every premise of a headline theorem is either a fact about the inputs (an accepted compilation, an
issued handle, a source invocation) or one of the contracts below. None of them assumes that the
runtime succeeds, terminates or agrees with the source semantics.

This file holds definitions only. The host contracts that headline statements use and that were
defined beside their proofs live here; the platform contracts stay in `Platform/` and the compiler
and source-choice contracts stay with their constructions until later phases bundle them. All are
listed here.

## Platform operations

| Contract | Obligation |
| --- | --- |
| [`Platform.AllocCorrect`](Platform/Alloc.lean) | `reserve` returns normally and preserves vector contents; it may refuse. |
| [`Platform.AllocationAvailable`](Platform/Alloc.lean) | `reserve` succeeds for every request within a fixed bound. Completeness only. |
| [`Platform.FloatOpsCorrect`](Platform/Float.lean) | The 27 rounding operations return a value the source semantics permits, NaN sets included. |
| [`Platform.MemoryLaws`](Platform/Memory.lean) | The memory buffer reads, writes, allocates and grows exactly the bytes `view` decodes. |
| interrupts, `∀ p, hooks.interrupt p ⦃ _ => True ⦄` | The interrupt hook returns normally. Completeness also requires it never to answer `.Terminate`. |

## Host callbacks

A host callback may publish fresh code. Each call receives the current ghost code
interpretation and chooses the next one, agreeing on previously issued keys.

| Contract | Obligation |
| --- | --- |
| `HostWorldSound` | Each call returns normally, preserves the invariant, extends the decoded source store and leaves it typed (`Store_ok`). |
| frame retention, [`Interp.FrameStorePrefix`](Interp/Relations/FrameStorePrefix.lean) | A call keeps the raw store identity and the existing function, type and instance entries. |
| extern retention | A call never shrinks `store.externs`. |
| issued results, [`Store.IssuedValue`](Store/Invariant/IssuedValues.lean) | Every value a call returns is issued by the post-call store. |
| `WorldInvocationLaws` | The platform laws and the four host laws above, bundled. |
| `HostWorldChosenSound` | `HostWorldSound`, and each reply matches the preselected source host choice. Chosen completeness only. |
| `NoHostStackOverflow` | No call reports stack exhaustion. Chosen completeness only. |

The raw retention laws are separate premises: they do not follow from decoded source-store
extension.

## Compiler

| Contract | Obligation |
| --- | --- |
| [`Code.ValidCompilationSource`](Code/Module/CompilationAvailable.lean) | The bytes independently encode a valid, elaborated, profile-restricted module within the binary and signature limits. |
| [`Code.CompileEligible`](Code/Module/CompilationAvailable.lean) | Source-only size and demand bounds fit the configured limits and the allocation bound. |

## Chosen-run completeness

Completeness matches one preselected terminating source run, so the source policies and the
actual platform must agree at every choice point.

| Contract | Obligation |
| --- | --- |
| [`Spec.SourceChoices.Admissible`](Spec/Choices/Steps.lean) | Each host, numeric, vector and growth policy chooses an outcome the source semantics permits. |
| `GrowthChoicesCompatible` | Actual memory and table growth replies equal the chosen source growth replies. |
| [`ChosenWorldResources`](Theorems/Composition/World/ChosenWorldResourceBounds.lean) | Every chosen source prefix fits the value and frame limits. |
| [`Interp.SourceCanonicalFunctionCapacity`](Interp/Relations/SourceCanonicalCapacity.lean) | The entry function's canonical slot demand, bounded by the value limit. |
| [`SourceOperationChoices.Admissible`](Theorems/Host/Open/Source/Chosen/ControlChoices.lean) | Combined Wasm, host-control and API policies are admissible. Host driver only. |
| [`SourceAPIChoicesCompatible`](Theorems/Host/Open/Source/Chosen/APIChoiceMatching.lean) | Actual API replies equal the chosen API replies. Host driver only. |
| [`SourcePublicationChoicesCompatible`](Theorems/Host/Open/Source/Chosen/PublicationChoiceMatching.lean) | Actual compilation and publication replies equal the chosen ones. Host driver only. |
| [`ChosenSourceResources`](Theorems/Host/Open/Completeness/ChosenSourceResources.lean) | Every chosen combined source prefix fits the initial store limits. Host driver only. |

## Store state

The invariants `ExecutableInv` and `ExecutableResourceInv` (in `Theorems/Api/`) are established by
instantiation and preserved by every result; they are certificates, not embedder obligations.
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

/-- Exactly the existing platform and callback premises of public invocation.
Construct with `⟨correct,allocation,interrupts,memory,sound,frames,externs,results⟩`;
the named projections recover every original premise independently. -/
structure WorldInvocationLaws {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) : Prop where
  float_correct : Platform.FloatOpsCorrect floats
  allocation : Platform.AllocCorrect allocator
  interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄
  memory_laws : Platform.MemoryLaws memory view
  host_sound : HostWorldSound hooks view (ExecutableInv view)
  frames : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
    hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1
  externs : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
    hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length
  results : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
    hooks.call_host p store host args results = .ok answer →
    ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value

/-- Returning callbacks choose their post-world and match the preselected
source reply at each occurrence. Matching concerns one primitive callback and
its actual dynamic result check, independently of an invocation trace. -/
def HostWorldChosenSound {M P : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (view : M → Slice U8)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop) (choices : Spec.SourceChoices) : Prop :=
  ∀ occurrence code store, Inv code store → ∀ platform identity args defaults,
    hooks.call_host platform store identity args defaults ⦃ answer => ∃ afterCode,
      Store.CodeAgreesOn store code afterCode ∧ Inv afterCode answer.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode answer.2.2.1) ∧
      Store_ok (Store.decodeStore view afterCode answer.2.2.1) ∧
      ∀ (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType),
        store.funcs.val[address.index.val]?=some function → function.code=.Host identity →
        store.types.val[function.signature.val]?=some signature →
        choices.host occurrence (Store.decodeStore view code store) address.index.val identity.val
          (signature.params.val.map Interp.sourceType) (signature.results.val.map Interp.sourceType)
          (args.val.map Interp.sourceValue)=
            checkedHostReply memory view afterCode answer.2.2.1 signature ⟨answer.2.2.2⟩ answer.1 ⦄

/-- Explicitly rule out callback-reported stack exhaustion. Normal host traps
and invalid dynamically checked results remain source trap outcomes. -/
def NoHostStackOverflow {M P : Type} (hooks : runtime.platform.Platform P M)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop) : Prop :=
  ∀ code store,Inv code store → ∀ p identity args defaults nextPlatform after returned,
    hooks.call_host p store identity args defaults≠.ok (.Err .StackOverflow,nextPlatform,after,returned)

/-- The observable Wasm reply uses the failure sentinel, independently of a
buffer's opaque representation changes on refusal. -/
def memoryGrowthReply {M : Type} (view : M → Slice U8) (index : Usize)
    (out : U32 × runtime.store.Store M) : Option meminst :=
  if out.1.val=2^32-1 then none else (out.2.memories.val[index.val]?).map (Store.decodeMemory view)

def tableGrowthReply {M : Type} (index : Usize)
    (out : U32 × runtime.store.Store M) : Option tableinst :=
  if out.1.val=2^32-1 then none else (out.2.tables.val[index.val]?).map Store.decodeTable

/-- Primitive growth compatibility is a law of actual API replies on concrete
objects. It assumes no invocation result, source trace, or exhaustion exclusion. -/
structure GrowthChoicesCompatible {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (view : M → Slice U8) (choices : Spec.SourceChoices) : Prop where
  memoryReply : ∀ occurrence (store : runtime.store.Store M) index delta object out,
    store.memories.val[index.val]?=some object →
    runtime.store.Store.grow_memory_index memory store index delta=.ok out →
    choices.memory occurrence (Store.decodeMemory view object) delta.val=memoryGrowthReply view index out
  tableReply : ∀ occurrence (store : runtime.store.Store M) index delta value object out,
    store.tables.val[index.val]?=some object →
    runtime.store.Store.grow_table_index memory allocator store index delta value=.ok out →
    choices.table occurrence (Store.decodeTable object) delta.val (Store.decodeRef object.ty value)=tableGrowthReply index out

end Exec.Theorems
