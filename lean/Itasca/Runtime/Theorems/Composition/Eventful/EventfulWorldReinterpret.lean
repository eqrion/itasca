import Itasca.Runtime.Theorems.Composition.Eventful.EventfulWorld
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std Itasca.Runtime.Interp

/-- Reusing a fixed-world successor after reinterpreting only unissued keys
produces a genuine cross-world edge with the original source endpoint. -/
theorem EventfulTransition.world_reinterpret {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {oldCode newCode : Store.CodeInterpretation} {expected : List valtype}
    {before : EventfulMachine M P view oldCode expected}
    {after : EventfulMachine M P view newCode expected} {events : List SpecExt.HostEvent}
    (agrees : Store.CodeAgreesOn before.store oldCode newCode)
    (edge : EventfulTransition memory hooks floats allocator (before.change_code newCode agrees) events after) :
    EventfulWorldTransition memory hooks floats allocator ⟨oldCode,before⟩ events ⟨newCode,after⟩ := by
  refine ⟨edge.actual,edge.simulation,?_,edge.metadata,edge.ambient,agrees⟩
  simpa only [EventfulMachine.change_code,Store.decodeStore_code_agrees view agrees] using edge.extension
end Itasca.Runtime.Theorems
