import Exec.Theorems.Composition.World.ChosenWorldRecordedLoop
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
theorem chosen_world_recorded_loop_results {choices : Spec.SourceChoices} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (steps : ChosenWorldStepOutcomes choices (emission:=emission) (allowed:=allowed) memory hooks floats allocator view expected Inv)
    (initial : ChosenWorld emission allowed M P view expected) (valid : Inv initial.code initial.machine.store) :
    recordedInvokeLoop memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ()) []
      ⦃ (result,events) => ChosenWorldRecordedLoopOutcome choices Inv initial result events ⦄div := by
  apply Platform.Recording.lift_dspec _ _ _ _
    (recordedInvokeLoop_erase memory hooks floats allocator initial.machine.exec initial.machine.store initial.machine.platform (.Ok ()) [])
    (chosen_world_loop_stops memory hooks floats allocator Inv steps initial valid)
  rintro result ⟨state,invariant,stopped,same⟩
  obtain ⟨events,writer,source⟩ := chosen_world_recorded_loop_finished memory hooks floats allocator Inv initial state invariant stopped
  subst result
  exact ⟨events,by simpa only [List.nil_append] using writer [],source⟩
end Exec.Theorems
