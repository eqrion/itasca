import Exec.Theorems.Composition.Supported.SupportedHistory
import Exec.Interp.Relations.EventfulControl
import Exec.Interp.Relations.FrameStorePrefix
import Exec.Spec.EventfulInfinite

namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- An execution state with a current certificate and reference ownership.
Host callbacks may extend the store, so neither host-freedom nor a fixed bound
on the initial source store is a field of this carrier. -/
structure EventfulMachine (emission : StructuredMachine.FunctionEmission) (allowed : instr → Prop)
    (M P : Type) (view : M → Slice U8) (code : Store.CodeInterpretation) (expected : List valtype) where
  store : runtime.store.Store M
  exec : runtime.interp.Execution
  platform : P
  source : Abs.AState
  pc : Nat
  pending : Bool
  invariant : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec source expected pc pending
  certified : CertifiedSupportedStore emission allowed view code store
  owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) source

def SupportedMachine.eventful {M P view code expected}
    (machine : SupportedMachine emission allowed M P view code expected) :
    EventfulMachine emission allowed M P view code expected :=
  ⟨machine.store,machine.exec,machine.platform,machine.source,machine.pc,machine.pending,
    machine.invariant,machine.certified,machine.owned⟩

/-- History edges retain the actual extracted dispatch equation. The labeled
simulation and raw metadata retention must be supplied by checked dispatch
lemmas; declaring this relation alone does not discharge those obligations. -/
structure EventfulTransition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (before : EventfulMachine emission allowed M P view code expected) (events : List SpecExt.HostEvent)
    (after : EventfulMachine emission allowed M P view code expected) : Prop where
  actual : runtime.interp.step memory hooks floats allocator before.exec before.store before.platform =
    .ok (.Ok (),after.exec,after.store,after.platform)
  simulation : EventfulConcreteSim U32.max before.pc after.pc before.pending after.pending before.source after.source events
  extension : Extend_store (Store.decodeStore view code before.store) (Store.decodeStore view code after.store)
  metadata : FrameStorePrefix before.store after.store
  ambient : after.source.ambient = before.source.ambient

theorem SupportedTransition.eventful {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : SupportedMachine emission allowed M P view code expected} {events : List SpecExt.HostEvent}
    (edge : SupportedTransition memory hooks floats allocator before events after) :
    EventfulTransition memory hooks floats allocator before.eventful events after.eventful := by
  obtain ⟨rfl,actual,simulation,extension,metadata,ambient,rest⟩ := edge
  exact ⟨actual,simulation.eventful,extension,metadata.prefix,ambient⟩

theorem EventfulMachine.history_source {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected} {n : Nat} {events : List SpecExt.HostEvent}
    (history : Spec.Iterations (EventfulTransition memory hooks floats allocator) n before events after) :
    ∃ count, Spec.StepsHN count (Abs.decode before.source) events (Abs.decode after.source) := by
  induction history with
  | refl state => exact ⟨0,.refl state.invariant.typed.typed.decode_wf⟩
  | @cons n first middle last events rest edge tail ih =>
    obtain ⟨prefixCount,prefixSteps⟩ := edge.simulation.source first.invariant.typed.typed.decode_wf
    obtain ⟨count,steps⟩ := ih
    exact ⟨prefixCount+count,prefixSteps.trans steps⟩

theorem EventfulMachine.history_metadata {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected} {n : Nat} {events : List SpecExt.HostEvent}
    (history : Spec.Iterations (EventfulTransition memory hooks floats allocator) n before events after) :
    Extend_store (Store.decodeStore view code before.store) (Store.decodeStore view code after.store) ∧
      FrameStorePrefix before.store after.store ∧ after.source.ambient = before.source.ambient := by
  induction history with
  | refl state =>
    exact ⟨Spec.extend_store_refl _ (Store.decodeStore_wf view code _ state.certified.shape state.certified.storeSyntax),.refl _,rfl⟩
  | cons edge tail ih =>
    exact ⟨Spec.extend_store_trans edge.extension ih.1,edge.metadata.trans ih.2.1,ih.2.2.trans edge.ambient⟩

def EventfulMachine.potential {M P view code expected}
    (machine : EventfulMachine emission allowed M P view code expected) : Nat :=
  dispatchMeasure machine.pending U32.max machine.pc machine.source

/-- Once actual divergent dispatches supply successors, their exact event
traces form a coherent infinite source execution. The runtime successor
premise is deliberately explicit until host dispatch is integrated. -/
theorem EventfulMachine.infinite_source {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (running : EventfulMachine emission allowed M P view code expected → Prop)
    (successor : ∀ machine, running machine → ∃ events after,
      EventfulTransition memory hooks floats allocator machine events after ∧ running after)
    (initial : EventfulMachine emission allowed M P view code expected) (active : running initial) :
    Spec.InfiniteSourceWithEvents (Abs.decode initial.source) := by
  let next (before : {s // running s}) events (after : {s // running s}) :=
    EventfulTransition memory hooks floats allocator before.val events after.val
  apply Spec.infinite_source_of_decreasing_stutter next
    (fun s => Abs.decode s.val.source) (fun s => s.val.potential) ?_ ?_ ⟨initial,active⟩
  · intro machine
    obtain ⟨events,after,edge,active⟩ := successor machine.val machine.property
    exact ⟨events,⟨after,active⟩,edge⟩
  · intro before events after edge
    exact edge.simulation
end Exec.Theorems
