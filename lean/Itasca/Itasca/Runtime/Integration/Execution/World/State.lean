import Itasca.Runtime.Integration.Execution.Certificates
import Itasca.Runtime.Integration.Execution.Ownership.ReferenceShape
import Itasca.Runtime.Interp.Machine.CompiledFunctions
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Integration.Execution.History.State

open WebAssembly

open Itasca.Representation

/-! ## ExecutionCode -/

section

namespace Itasca.Interp.Machine
open Aeneas Aeneas.Std

/-- Changing ghost meanings only at unissued instance keys leaves the entire
active and suspended execution relation intact. No frame is reconstructed. -/
theorem Execution.change_code {M : Type} {view : M → Slice U8} {before after : Itasca.Representation.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution}
    {source : Itasca.SourceMachine.AState} {expected : List valtype} {pc : Nat} {pending : Bool}
    (held : Execution view before store exec source expected pc pending)
    (agrees : Itasca.Store.CodeAgreesOn store before after) :
    Execution view after store exec source expected pc pending :=
  { held with storeEq := held.storeEq.trans (Itasca.Store.decode_store_code_agrees view agrees).symm }

end Itasca.Interp.Machine

namespace Itasca.Store
open Aeneas Aeneas.Std

/-- Agreement on old issued keys composes through actual retained instances. -/
theorem CodeAgreesOn.trans_prefix {M : Type} {before middle : runtime.store.Store M}
    {first second third : CodeInterpretation}
    (left : CodeAgreesOn before first second)
    (retained : Store.MetadataExtended before middle)
    (right : CodeAgreesOn middle second third) : CodeAgreesOn before first third := by
  intro index inst found function
  exact (right index inst (retained.instance_lookup found) function).trans
    (left index inst found function)
end Itasca.Store

end

/-! ## State -/

section

namespace Itasca.Integration
open Aeneas Aeneas.Std Itasca.Interp

/-- A change of ghost world at the same raw store preserves the source state,
program counters and saved frames exactly. -/
def EventfulMachine.change_code {M P view before expected}
    (machine : EventfulMachine M P view before expected)
    (after : Representation.CodeInterpretation) (agrees : Store.CodeAgreesOn machine.store before after) :
    EventfulMachine M P view after expected :=
  ⟨machine.store,machine.exec,machine.platform,machine.source,machine.pc,machine.pending,
    machine.invariant.change_code agrees,machine.certified.change_code agrees,machine.owned⟩

/-- Every previously checked fixed-world ordinary edge embeds unchanged. -/
theorem EventfulTransition.world {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Representation.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine M P view code expected}
    {events : List WebAssembly.HostEvent}
    (edge : EventfulTransition memory hooks floats allocator before events after) :
    EventfulWorldTransition memory hooks floats allocator ⟨code,before⟩ events ⟨code,after⟩ :=
  ⟨edge.actual,edge.simulation,edge.extension,edge.metadata,edge.ambient,by intro index inst found function; rfl⟩

/-- Finite source histories compose even when callbacks publish new code. -/
theorem EventfulWorld.history_source {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {before after : EventfulWorld M P view expected} {n : Nat}
    {events : List WebAssembly.HostEvent}
    (history : Spec.Iterations (EventfulWorldTransition memory hooks floats allocator) n before events after) :
    ∃ count, Spec.StepsHN count (Itasca.SourceMachine.decode before.machine.source) events
      (Itasca.SourceMachine.decode after.machine.source) := by
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
    {events : List WebAssembly.HostEvent}
    (history : Spec.Iterations (EventfulWorldTransition memory hooks floats allocator) n before events after) :
    Extend_store (Representation.decodeStore view before.code before.machine.store)
      (Representation.decodeStore view after.code after.machine.store) ∧
    Store.MetadataExtended before.machine.store after.machine.store ∧
    Store.CodeAgreesOn before.machine.store before.code after.code := by
  induction history with
  | refl state =>
    exact ⟨Spec.extend_store_refl _ (Store.decode_store_wf view state.code _
      state.machine.certified.shape state.machine.certified.storeSyntax),.refl _,by intro index inst found function; rfl⟩
  | cons edge tail ih =>
    exact ⟨Spec.extend_store_trans edge.extension ih.1,edge.metadata.trans ih.2.1,
      edge.agrees.trans_prefix edge.metadata ih.2.2⟩

end Itasca.Integration

end
