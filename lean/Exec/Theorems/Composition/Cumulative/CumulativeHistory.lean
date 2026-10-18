import Exec.Theorems.Composition.Certified.CertifiedCumulative
import Exec.Theorems.Composition.Core.CoreHostFree
import Exec.Interp.Cumulative.Machine
import Exec.Interp.Relations.ExecutionLoop
import Exec.Interp.Machines.Slice.SliceHistory
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- All data needed to continue a defined-only mutable invocation. The current
store is part of the state, so writes retain their concrete and source effects. -/
structure CumulativeMachine (M P : Type) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (expected : List valtype) where
  store : runtime.store.Store M
  exec : runtime.interp.Execution
  platform : P
  source : Abs.AState
  pc : Nat
  pending : Bool
  invariant : Cumulative.Execution view code store exec source expected pc pending
  certified : CertifiedCumulativeStore view code store
  owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source
  hostFree : CoreHostFree store

def CumulativeTransition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (before : CumulativeMachine M P view code expected) (events : List SpecExt.HostEvent)
    (after : CumulativeMachine M P view code expected) : Prop :=
  events = [] ∧ runtime.interp.step memory hooks floats allocator before.exec before.store before.platform =
    .ok (.Ok (),after.exec,after.store,after.platform) ∧
  ConcreteSim U32.max before.pc after.pc before.pending after.pending before.source after.source ∧
  Extend_store (Store.decodeStore view code before.store) (Store.decodeStore view code after.store) ∧
  FrameStoreMetadata before.store after.store ∧ after.source.ambient = before.source.ambient ∧
  (∀ bound, Abs.CodeBound bound before.source → Abs.CodeBound bound after.source)

theorem CumulativeMachine.history_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : CumulativeMachine M P view code expected} {n : Nat} {events : List SpecExt.HostEvent}
    (history : Spec.Iterations (CumulativeTransition memory hooks floats allocator) n before events after) :
    events = [] ∧ ∃ count, Spec.StepsHN count (Abs.decode before.source) [] (Abs.decode after.source) := by
  induction history with
  | refl state => exact ⟨rfl,0,.refl state.invariant.typed.typed.decode_wf⟩
  | cons edge rest ih =>
    obtain ⟨rfl,actual,simulation,extension,metadata,ambient,bounded⟩ := edge
    obtain ⟨rfl,count,reductions⟩ := ih
    refine ⟨rfl,?_⟩
    rcases simulation with ⟨same,decrease⟩ | ⟨first,positive,steps⟩
    · exact ⟨count,by simpa only [same] using reductions⟩
    · exact ⟨first+count,by simpa using steps.trans reductions⟩

theorem CumulativeMachine.history_metadata {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : CumulativeMachine M P view code expected} {n : Nat} {events : List SpecExt.HostEvent}
    (history : Spec.Iterations (CumulativeTransition memory hooks floats allocator) n before events after) :
    Extend_store (Store.decodeStore view code before.store) (Store.decodeStore view code after.store) ∧
      FrameStoreMetadata before.store after.store ∧ after.source.ambient = before.source.ambient := by
  induction history with
  | refl state => exact ⟨Spec.extend_store_refl _ (Store.decodeStore_wf view code _ state.certified.shape state.certified.storeSyntax),.refl _,rfl⟩
  | cons edge rest ih =>
    exact ⟨Spec.extend_store_trans edge.2.2.2.1 ih.1,edge.2.2.2.2.1.trans ih.2.1,ih.2.2.trans edge.2.2.2.2.2.1⟩

theorem cumulative_execution_finished {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution} {source : Abs.AState}
    {expected : List valtype} {pc : Nat} {pending : Bool}
    (invariant : Cumulative.Execution view code store exec source expected pc pending) (empty : exec.frames.val = []) :
    source.frames = [] ∧ SpecExt.ResultsTyped source.store expected source.results ∧
      ValuesAt exec.slots.val 0 source.results := by
  have sourceEmpty : source.frames = [] := by
    cases frames : source.frames with
    | nil => rfl
    | cons f rest =>
      have stack := invariant.stack
      rw [frames] at stack
      cases stack with
      | active concrete top saved => simp [empty] at concrete
  refine ⟨sourceEmpty,?_,?_⟩
  · simpa only [Abs.InvocationResult,sourceEmpty] using invariant.result
  · have cursor := invariant.cursor
    simp only [StructuredMachine.ExecutionCursor,sourceEmpty] at cursor
    exact cursor.2.2
end Exec.Theorems
