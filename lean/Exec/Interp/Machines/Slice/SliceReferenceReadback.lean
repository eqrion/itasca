import Exec.Interp.Machines.Slice.SliceLoop
import Exec.Interp.Relations.ReferenceArguments

namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt

/-- The checked slice loop supplies exactly the typed slot results consumed by
public invocation readback, together with its source execution. -/
theorem slice_loop_readback_references {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    {store : runtime.store.Store M} {sourceStore : _root_.store} {ambient : frame}
    {expected : List valtype} {bound : Nat}
    (decoded : sourceStore = Store.decodeStore view code store) (compiled : CompiledFunctions code store)
    (initial : SliceMachine P store sourceStore ambient expected bound)
    (references : Abs.StateReferencesBound Usize.max initial.source) :
    runtime.interp.invoke_with_loop1 memory hooks floats allocator initial.exec store initial.platform (.Ok ())
      ⦃ (_, words, _, _, _, afterStore, _, status) => afterStore = store ∧
        (status = .Ok () → ∃ values,
          expected = values.map Code.valueType ∧
          (∀ value ∈ values, wf_val value) ∧
          (∀ value ∈ values, ResultIndexFits value) ∧
          ValuesAt words.val 0 values ∧
          StepsH (Abs.decode initial.source) [] ⟨⟨sourceStore, ambient⟩, vals values⟩) ⦄div := by
  apply WP.dspec_mono (slice_loop memory hooks floats allocator allocation interrupts view code decoded compiled initial)
  intro out outcome
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
