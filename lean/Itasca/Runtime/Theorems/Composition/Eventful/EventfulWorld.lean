import Itasca.Runtime.Theorems.Composition.Eventful.EventfulHistory
import Itasca.Runtime.Theorems.Composition.ExecutionCode

namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std Itasca.Runtime.Interp

/-- A change of ghost world at the same raw store preserves the source state,
program counters and saved frames exactly. -/
def EventfulMachine.change_code {M P view before expected}
    (machine : EventfulMachine M P view before expected)
    (after : Store.CodeInterpretation) (agrees : Store.CodeAgreesOn machine.store before after) :
    EventfulMachine M P view after expected :=
  ⟨machine.store,machine.exec,machine.platform,machine.source,machine.pc,machine.pending,
    machine.invariant.change_code agrees,machine.certified.change_code agrees,machine.owned⟩

/-- The current source interpretation is ghost state. In particular it need
not assign the eventual source bodies of future reentrant publications. -/
structure EventfulWorld
    (M P : Type) (view : M → Slice U8) (expected : List valtype) where
  code : Store.CodeInterpretation
  machine : EventfulMachine M P view code expected

/-- A cross-world edge keeps the actual dispatch and labeled source evidence.
It does not assert that host dispatch supplies such an edge: that obligation
must be discharged from a world-indexed callback theorem. -/
structure EventfulWorldTransition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (before : EventfulWorld M P view expected) (events : List SpecExt.HostEvent)
    (after : EventfulWorld M P view expected) : Prop where
  actual : runtime.interp.step memory hooks floats allocator before.machine.exec
    before.machine.store before.machine.platform =
    .ok (.Ok (),after.machine.exec,after.machine.store,after.machine.platform)
  simulation : EventfulConcreteSim U32.max before.machine.pc after.machine.pc
    before.machine.pending after.machine.pending before.machine.source after.machine.source events
  extension : Extend_store (Store.decodeStore view before.code before.machine.store)
    (Store.decodeStore view after.code after.machine.store)
  metadata : FrameStorePrefix before.machine.store after.machine.store
  ambient : after.machine.source.ambient = before.machine.source.ambient
  agrees : Store.CodeAgreesOn before.machine.store before.code after.code

/-- Every previously checked fixed-world ordinary edge embeds unchanged. -/
theorem EventfulTransition.world {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine M P view code expected}
    {events : List SpecExt.HostEvent}
    (edge : EventfulTransition memory hooks floats allocator before events after) :
    EventfulWorldTransition memory hooks floats allocator ⟨code,before⟩ events ⟨code,after⟩ :=
  ⟨edge.actual,edge.simulation,edge.extension,edge.metadata,edge.ambient,by intro index inst found function; rfl⟩

/-- Finite source histories compose even when callbacks publish new code. -/
theorem EventfulWorld.history_source {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {before after : EventfulWorld M P view expected} {n : Nat}
    {events : List SpecExt.HostEvent}
    (history : Spec.Iterations (EventfulWorldTransition memory hooks floats allocator) n before events after) :
    ∃ count, Spec.StepsHN count (Itasca.Runtime.Abs.decode before.machine.source) events
      (Itasca.Runtime.Abs.decode after.machine.source) := by
  induction history with
  | refl state => exact ⟨0,.refl state.machine.invariant.typed.typed.decode_wf⟩
  | @cons n first middle last events rest edge tail ih =>
    obtain ⟨prefixCount,prefixSteps⟩ := edge.simulation.source
      first.machine.invariant.typed.typed.decode_wf
    obtain ⟨count,steps⟩ := ih
    exact ⟨prefixCount+count,prefixSteps.trans steps⟩

/-- Every earlier interpretation remains valid at its issued keys after any
finite sequence of publications and ordinary steps. -/
theorem EventfulWorld.history_metadata {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {before after : EventfulWorld M P view expected} {n : Nat}
    {events : List SpecExt.HostEvent}
    (history : Spec.Iterations (EventfulWorldTransition memory hooks floats allocator) n before events after) :
    Extend_store (Store.decodeStore view before.code before.machine.store)
      (Store.decodeStore view after.code after.machine.store) ∧
    FrameStorePrefix before.machine.store after.machine.store ∧
    Store.CodeAgreesOn before.machine.store before.code after.code := by
  induction history with
  | refl state =>
    exact ⟨Spec.extend_store_refl _ (Store.decodeStore_wf view state.code _
      state.machine.certified.shape state.machine.certified.storeSyntax),.refl _,by intro index inst found function; rfl⟩
  | cons edge tail ih =>
    exact ⟨Spec.extend_store_trans edge.extension ih.1,edge.metadata.trans ih.2.1,
      edge.agrees.trans_prefix edge.metadata ih.2.2⟩

end Itasca.Runtime.Theorems
