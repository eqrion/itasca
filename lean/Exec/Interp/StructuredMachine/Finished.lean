import Exec.Interp.StructuredMachine.Execution
namespace Exec.Interp.StructuredMachine
open Aeneas Aeneas.Std
theorem Execution.finished {emission : FunctionEmission} {supported : Abs.AState → Prop} {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} {exec : runtime.interp.Execution} {source : Abs.AState}
    {expected : List valtype} {pc : Nat} {pending : Bool}
    (invariant : Execution emission supported view code store exec source expected pc pending) (empty : exec.frames.val = []) :
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
end Exec.Interp.StructuredMachine
