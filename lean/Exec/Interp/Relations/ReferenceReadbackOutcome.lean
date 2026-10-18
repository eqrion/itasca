import Exec.Interp.Machines.Slice.SliceReferenceReadback
import Exec.Interp.Machines.Slice.SliceErrors
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt

/-- Project represented readback values while retaining the full loop outcome
for its separate error and trace consequences. -/
theorem SliceLoopOutcome.readback_references {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    {initial : SliceMachine P store sourceStore ambient expected bound} {out : ExecutionResult M P}
    (outcome : SliceLoopOutcome memory hooks floats allocator initial out)
    (references : Abs.StateReferencesBound Usize.max initial.source) :
    out.2.2.2.2.2.1 = store ∧ (out.2.2.2.2.2.2.2 = .Ok () → ∃ values,
      expected = values.map Code.valueType ∧
      (∀ value ∈ values, wf_val value) ∧
      (∀ value ∈ values, ResultIndexFits value) ∧
      ValuesAt out.2.1.val 0 values ∧
      StepsH (Abs.decode initial.source) [] ⟨⟨sourceStore, ambient⟩, vals values⟩) := by
  rcases outcome with success | failure
  · obtain ⟨final, dispatches, count, history, empty, sourceEmpty, typed, represented, reductions, cost, rfl⟩ := success
    have tags : final.source.results.map Code.valueType = expected := by
      simpa only [show Code.valueType = Abs.valueType from funext valueType_eq_abs] using
        Abs.results_type_of_typed typed
    exact ⟨rfl, fun _ => ⟨final.source.results, tags.symm, Spec.resultsTyped_wf typed,
      results_fit_of_bound _ (SliceMachine.history_references memory hooks floats allocator history references).1, represented, reductions.erase⟩⟩
  · obtain ⟨previous, dispatches, error, finalExec, finalPlatform, history, failed, cause, rfl⟩ := failure
    exact ⟨rfl, by intro impossible; cases impossible⟩
end Exec.Interp
